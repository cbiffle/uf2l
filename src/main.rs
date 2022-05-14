// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `uf2l` (pronounced as U-F-Tool) is a program for dealing with UF2 format
//! firmware images.
//!
//! This is similar to the `elf2uf2` tool but with less validation and more
//! capabilities. In particular, this tool will not check that your ELF files
//! target defined memory regions for your microcontroller (because we don't
//! know what they are) or that the architecture is correct -- it simply moves
//! data to and from UF2 files, and does exactly what you ask it to.

mod format;
mod page;

use std::path::PathBuf;
use std::io::Write;
use std::collections::{BTreeMap, BTreeSet};
use clap::Parser;
use anyhow::{Context, Result, anyhow, bail};
use zerocopy::{AsBytes, U32};

use crate::format::Uf2Record;
use crate::page::PageStore;

///////////////////////////////////////////////////////////////////////
// Top-level command line interface definition and dispatch.

/// uf2l (pronounced U-F-Tool) manipulates UF2 firmware images.
#[derive(Parser)]
#[clap(term_width = 80)]
struct Uf2l {
    #[clap(flatten)]
    global: GlobalFlags,
    #[clap(subcommand)]
    command: Cmd,
}

#[derive(Parser)]
struct GlobalFlags {
    /// Enable additional output, probably more of it than you'd like.
    #[clap(long, short, global = true)]
    verbose: bool,
}

#[derive(Parser)]
enum Cmd {
    /// Convert one or more ELF files into UF2 format.
    Pack(PackArgs),
    /// Read a UF2 file, check validity, and print information about its
    /// contents.
    Info(InfoArgs),
}

///////////////////////////////////////////////////////////////////////
// Main function / dispatch routine.

fn main() -> Result<()> {
    let args = Uf2l::parse();
    match &args.command {
        Cmd::Pack(subargs) => cmd_pack(&args.global, subargs),
        Cmd::Info(subargs) => cmd_info(&args.global, subargs),
    }
}

///////////////////////////////////////////////////////////////////////
// pack

#[derive(Parser)]
struct PackArgs {
    /// Allow output to contain partial blocks, smaller than the block size.
    /// Note that common UF2 implementations will choke on this.
    #[clap(long)]
    allow_small_blocks: bool,

    /// Fill in gaps in memory with padding. Some UF2 implementations misbehave
    /// without this.
    #[clap(short, long)]
    contiguous: bool,

    /// Number of bytes per target system block/page. The UF2 format effectively
    /// limits this to 476.
    #[clap(long, short, default_value = "256")]
    block_size: usize,

    /// Padding byte to use to pad partial blocks (if --allow-small-blocks is
    /// not set) and gaps in memory (if --contiguous is set).
    #[clap(long, default_value = "0", parse(try_from_str = parse_u8))]
    padding: u8,

    /// Family ID identifying the type of processor this image is intended for.
    /// The default value matches the RP2040.
    #[clap(
        long,
        short,
        parse(try_from_str = parse_u32),
        default_value = "0xe48bff56",
    )]
    family_id: u32,

    /// Paths to one or more ELF files to combine into a UF2 image. Files must
    /// not overlap.
    #[clap(required = true)]
    inputs: Vec<PathBuf>,

    /// Path for UF2 output.
    output: PathBuf,
}

fn cmd_pack(
    _global: &GlobalFlags,
    args: &PackArgs,
) -> Result<()> {
    if args.block_size > 476 {
        bail!(
            "requested block size {} exceeds UF2 max of 476",
            args.block_size,
        );
    }

    let mut pages = PageStore::with_page_size(args.block_size);

    // Load all the files into a vector so that we can store references into
    // their contents.
    let images = args.inputs.iter()
        .map(|input| Ok((
            input,
            std::fs::read(input)
                .with_context(|| format!(
                    "unable to load input file {}",
                    input.display(),
                ))?,
        )))
        .collect::<Result<Vec<_>>>()?;
    // Now, attempt to parse all the files as ELF. These don't _need_ to go into
    // a Vec, because we immediately consume it to iterate over it, but that
    // allows us to use the collect syntax with Result which is very easy.
    let decoded_elf = images.iter()
        .map(|(input, image)| Ok((
            input,
            load_elf(image)
                .with_context(|| format!(
                    "could not parse input file {}",
                    input.display(),
                ))?,
        )))
        .collect::<Result<Vec<_>>>()?;

    // Splat all the data extents at the pagestore.
    for (filename, segments) in decoded_elf {
        for (addr, data) in segments {
            pages.add(addr as usize, data)
                .with_context(|| format!(
                    "overlap: could not include data at address {:#010x} \
                     from {}",
                    addr,
                    filename.display(),
                ))?;
        }
    }

    if pages.page_count() == 0 {
        bail!("no data in input, output file would be zero length, aborting.");
    }

    // Allocate a block filled with padding that we can reference if we find
    // pages that are empty, but need to be filled with padding instead.
    let padvec = vec![args.padding; args.block_size];

    if args.contiguous {
        // Record the pages we need to add to make the image contiguous into a
        // vec, which effectively acts as a worklist while we're iterating over
        // (and thus can't modify) the pagestore.
        let mut pad_pages = vec![];
        // end tracks the one-past-the-end of the last page processed, so we
        // seed it with the lowest address in the store.
        let mut end = pages.iter().next().unwrap().0;
        for (addr, _) in pages.iter() {
            while end != addr {
                pad_pages.push(end);
                end += args.block_size;
            }
            end += args.block_size;
        }
        for addr in pad_pages {
            // This shouldn't be able to fail, since a failure would indicate
            // overlap with existing data, and we shouldn't be attempting it.
            pages.add(addr, &padvec)
                .expect("error in padding algorithm");
        }
    }

    // Begin generating output!
    //
    // There's a good chance that our output "filesystem" is the USB bootloader
    // of some attached device. We're okay with that. In particular,
    //
    // - We're not buffering the output, to try to encourage the blocks to be
    //   written in index order one at a time.
    // - We're writing each block exactly once in order.

    let mut out = std::fs::File::create(&args.output)
        .with_context(|| format!(
            "can't create output file {}",
            args.output.display(),
        ))?;

    let block_count = pages.page_count() as u32;

    println!(
        "{}image is {} blocks",
        if args.inputs.len() > 1 { "combined " } else { "" },
        block_count,
    );

    // Set up a prototype record that we can copy to initialize each record in
    // the stream. This will contain valid data for the fields that are fixed,
    // and invalid data for the fields we'll be overwriting.
    let prototype = Uf2Record::prototype(block_count, args.family_id);

    // Now, write each record to the output stream in order. This is designed so
    // that it will only fail in the event of I/O errors to the output
    // filesystem or bootloader.
    for (i, (addr, page)) in pages.iter().enumerate() {
        let len = if args.allow_small_blocks {
            page.len()
        } else {
            // The Page itself will pad its length when we ask it to copy.
            args.block_size
        };

        let mut record = Uf2Record {
            address: U32::new(addr as u32),
            length: U32::new(u32::try_from(len).unwrap()),
            block_no: U32::new(u32::try_from(i).unwrap()),
            ..prototype
        };

        page.write_into(&mut record.data[..len], args.padding);

        out.write_all(record.as_bytes())
            .with_context(|| {
                format!("error writing block {} to output", i)
            })?;
    }

    Ok(())
}

/// Loads the "program" parts of an ELF file into a map from address to data
/// slice. The data is not copied.
///
/// We define the "program" parts as follows:
///
/// - If PHDRs are available, we take those with type `PT_LOAD`.
/// - Otherwise, we take section headers with type `SHT_PROGBITS`.
///
/// If multiple parts have the same starting address, (1) your ELF file is bogus
/// and (2) we will arbitrarily choose the one that appears last in file order
/// and discard the other.
fn load_elf(
    elf_image: &[u8],
) -> Result<BTreeMap<u32, &[u8]>> {
    use goblin::elf::{Elf, program_header, section_header};

    let elf = Elf::parse(&elf_image)
        .with_context(|| format!("could not parse file as ELF"))?;

    if elf.is_64 {
        bail!("UF2 format only supports 32-bit targets, \
            but this ELF file is 64-bit");
    }

    // There are tools in the wild (looking at you, objcopy) that don't generate
    // PHDRs, so we will also accept section headers as a backup.
    //
    // Try PHDRs first though.
    if !elf.program_headers.is_empty() {
        elf.program_headers.iter()
            .filter(|ph| ph.p_type == program_header::PT_LOAD)
            .map(|ph| {
                let offset = usize::try_from(ph.p_offset)
                    .context("offset out of range for usize")?;
                let size = usize::try_from(ph.p_filesz)
                    .context("filesz out of range for usize")?;
                let addr = u32::try_from(ph.p_paddr)
                    .context("paddr out of range for u32")?;
                let end = offset.checked_add(size)
                    .ok_or_else(|| anyhow!("PHDR wraps end of address space"))?;
                let data = elf_image.get(offset..end)
                    .ok_or_else(|| anyhow!("PHDR data out of range"))?;

                Ok((addr, data))
            })
        .collect::<Result<_, _>>()
    } else {
        // Take section headers.
        elf.section_headers.iter()
            .filter(|sh| sh.sh_type == section_header::SHT_PROGBITS)
            .map(|sh| {
                let offset = usize::try_from(sh.sh_offset)
                    .context("offset out of range for usize")?;
                let size = usize::try_from(sh.sh_size)
                    .context("size out of range for usize")?;
                let addr = u32::try_from(sh.sh_addr)
                    .context("addr out of range for u32")?;
                let end = offset.checked_add(size)
                    .ok_or_else(|| anyhow!("section wraps end of address space"))?;
                let data = elf_image.get(offset..end)
                    .ok_or_else(|| anyhow!("section data out of range"))?;

                Ok((addr, data))
            })
        .collect()
    }
}

///////////////////////////////////////////////////////////////////////
// info

#[derive(Parser)]
struct InfoArgs {
    /// Path to a UF2 file to analyze.
    input: PathBuf,
}

fn cmd_info(
    global: &GlobalFlags,
    args: &InfoArgs,
) -> Result<()> {
    let uf2_image = std::fs::read(&args.input)
        .with_context(|| format!(
            "can't read input path {}",
            args.input.display(),
        ))?;
    
    if uf2_image.len() % 512 != 0 {
        bail!(
            "file size ({} bytes) isn't evenly divisible by 512 \
             (not a UF2 file?)",
            uf2_image.len(),
        );
    }

    struct Stream<'a> {
        pages: PageStore<'a>,
        block_size: usize,
        block_count: usize,
        blocks_seen: BTreeSet<usize>,
    }

    let mut families: BTreeMap<u32, Stream<'_>> = BTreeMap::new();

    for (i, record) in uf2_image.chunks_exact(512).enumerate() {
        // This shouldn't fail because the type is Unaligned and chunks_exact
        // ensures the size.
        let record = zerocopy::LayoutVerified::<_, Uf2Record>::new(record)
            .unwrap()
            .into_ref();

        if record.magic[0].get() != Uf2Record::MAGIC[0]
            || record.magic[1].get() != Uf2Record::MAGIC[1]
            || record.final_magic.get() != Uf2Record::FINAL_MAGIC
        {
            println!(
                "warning: record at offset {} has bad magic, skipping",
                i * 512,
            );
            continue;
        }

        if record.flags.get() & (1 | 0x1000) != 0 {
            // Comment record not intended for main flash, or file container,
            // skip without complaint.
            continue;
        }
        if record.flags.get() & 0x2000 == 0 {
            println!(
                "warning: record at offset {} does not include family ID, \
                 skipping",
                i * 512,
            );
            continue;
        }

        if record.length.get() as usize > record.data.len() {
            println!(
                "ERROR: record at offset {} claims impossible length {}",
                i * 512,
                record.length.get(),
            );
            continue;
        }

        let stream = families.entry(record.family_id.get())
            .or_insert_with(|| Stream {
                block_size: record.length.get() as usize,
                pages: PageStore::with_page_size(record.length.get() as usize),
                blocks_seen: BTreeSet::new(),
                block_count: record.total_blocks.get() as usize,
            });

        if record.length.get() as usize > stream.block_size {
            println!(
                "ERROR: family {:#010x} block #{} is larger ({}) than \
                 stream block size ({})",
                record.family_id.get(),
                record.block_no.get(),
                record.length.get(),
                stream.block_size,
            );
        }

        if record.block_no.get() as usize >= stream.block_count {
            println!(
                "ERROR: family {:#010x} block #{} is outside \
                 expected count ({})",
                record.family_id.get(),
                record.block_no.get(),
                stream.block_count,
            );
        }

        if stream.blocks_seen.insert(record.block_no.get() as usize) == false {
            println!(
                "ERROR: family {:#010x} block #{} appears more than once",
                record.family_id.get(),
                record.block_no.get(),
            );
        }

        let data = &record.data[..record.length.get() as usize];
        let address = record.address.get();
        match stream.pages.add(address as usize, data) {
            Err(e) => {
                println!("ERROR: {:?}", e);
            }
            Ok(_) => (),
        }
    }

    println!(
        "file parsed, found data streams for {} family IDs",
        families.len(),
    );

    for (family_id, stream) in families {
        println!();
        println!("family ID {:#08x}:", family_id);
        println!("- expected {} blocks, got {}",
            stream.block_count,
            stream.blocks_seen.len());

        if global.verbose {
            println!("- {:<10}  LEN", "ADDR");
            for (address, page) in stream.pages.iter() {
                println!("  {:#010x}  {}", address, page.len());
            }
        }
    }

    Ok(())
}

///////////////////////////////////////////////////////////////////////
// Clap helper functions. Out of the box, Clap does not appear to be able to
// parse numbers with a base prefix. So, let's fix that.

fn parse_u32(s: &str) -> Result<u32> {
    parse_with_prefix(s, u32::from_str_radix)
}

fn parse_u8(s: &str) -> Result<u8> {
    parse_with_prefix(s, u8::from_str_radix)
}

fn parse_with_prefix<T>(
    s: &str,
    parse_radix: impl FnOnce(&str, u32) -> Result<T, std::num::ParseIntError>,
) -> Result<T> {
    if s.starts_with("0x") {
        parse_radix(&s[2..], 16)
            .context("has hex prefix 0x but is not a hex number")
    } else if s.starts_with("0b") {
        parse_radix(&s[2..], 2)
            .context("has binary prefix 0b but is not a binary number")
    } else {
        parse_radix(s, 10)
            .context("expected decimal number or 0x/0b prefix")
    }
}
