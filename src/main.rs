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
    /// Converts ELF files into UF2 like `pack`, but instead of writing the
    /// result to a normal file, scans for attached bootloaders emulating USB
    /// mass storage devices and copies the firmware directly to one.
    ///
    /// Any mounted drive that contains an `INFO_UF2.TXT` file at its root will
    /// be considered as a potential attached bootloader. Arguments to this
    /// command allow filtering based on the contents of that file.
    #[cfg(feature = "sysinfo")]
    Flash(FlashArgs),
    /// Scans for attached bootloaders like `flash`, but lists them instead of
    /// attempting to upload to one.
    #[cfg(feature = "sysinfo")]
    Scan(ScanArgs),
}

///////////////////////////////////////////////////////////////////////
// Main function / dispatch routine.

fn main() -> Result<()> {
    let args = Uf2l::parse();
    match &args.command {
        Cmd::Pack(subargs) => cmd_pack(&args.global, subargs),
        Cmd::Info(subargs) => cmd_info(&args.global, subargs),

        #[cfg(feature = "sysinfo")]
        Cmd::Flash(subargs) => cmd_flash(&args.global, subargs),
        #[cfg(feature = "sysinfo")]
        Cmd::Scan(subargs) => cmd_scan(&args.global, subargs),
    }
}

///////////////////////////////////////////////////////////////////////
// pack and flash

#[derive(Parser)]
struct PackAndFlashArgs {
    /// Allow output to contain partial blocks, smaller than the block size.
    /// Note that common UF2 implementations will choke on this.
    #[clap(long)]
    allow_small_blocks: bool,

    /// Pad any written data out to erase sector boundaries of this many bytes,
    /// naturally aligned. This is critical for loading files into the RP2040 to
    /// work around a boot ROM bug.
    #[clap(short = 'e', long, value_name = "SECTOR_BYTES")]
    pad_erase_sectors: Option<usize>,

    /// Number of bytes per target system block/page. The UF2 format effectively
    /// limits this to 476.
    #[clap(long, short, default_value = "256")]
    block_size: usize,

    /// Padding byte to use to pad partial blocks (if --allow-small-blocks is
    /// not set) and unused portions of erase sectors (if --pad-erase-sectors is
    /// set).
    #[clap(long, default_value = "0", parse(try_from_str = parse_u8))]
    padding: u8,

    /// Family ID identifying the type of processor this image is intended for,
    /// given either as a decimal number, a hex number prefixed with `0x`, or
    /// the name of the family from the UF2 spec. Pass `help` to see a list of
    /// known names.
    #[clap(
        long,
        short,
        parse(try_from_str = parse_family),
        default_value = "RP2040",
    )]
    family_id: u32,
}

#[derive(Parser)]
struct PackArgs {
    #[clap(flatten)]
    common: PackAndFlashArgs,

    /// Paths to one or more ELF files to combine into a UF2 image. Files must
    /// not overlap.
    #[clap(required = true)]
    inputs: Vec<PathBuf>,

    /// Path for UF2 output.
    output: PathBuf,
}

fn cmd_pack(
    global: &GlobalFlags,
    args: &PackArgs,
) -> Result<()> {
    do_common_pack(
        global,
        &args.common,
        &args.inputs,
        &args.output,
    )
}

#[cfg(feature = "sysinfo")]
#[derive(Parser)]
struct FlashArgs {
    #[clap(flatten)]
    common: PackAndFlashArgs,

    #[clap(flatten)]
    filter: BootloaderFilter,

    /// Normally, the tool will fail if multiple attached bootloaders match, to
    /// avoid doing something questionable. This flag overrides that behavior
    /// and arbitrarily selects one.
    #[clap(long)]
    feeling_lucky: bool,

    /// Paths to one or more ELF files to combine into a UF2 image. Files must
    /// not overlap.
    #[clap(required = true)]
    inputs: Vec<PathBuf>,
}

#[cfg(feature = "sysinfo")]
fn cmd_flash(
    global: &GlobalFlags,
    args: &FlashArgs,
) -> Result<()> {
    use sysinfo::{DiskExt, SystemExt};

    let sys = sysinfo::System::new_with_specifics(
        sysinfo::RefreshKind::new().with_disks_list()
    );

    let mut matches = vec![];
    for disk in sys.disks() {
        let path = disk.mount_point();
        match check_bootloader(&path, &args.filter) {
            Ok(true) => matches.push(path),
            Ok(false) => (),
            Err(e) => {
                eprintln!("warning: {:?}", e);
                continue;
            }
        }
    }

    let dest = match matches.len() {
        0 => {
            bail!("no matching mounted devices were found");
        }
        1 => matches.into_iter().next().unwrap(),
        n if args.feeling_lucky => {
            eprintln!("note: {n} matching devices found, picking one");
            matches.into_iter().next().unwrap()
        }
        n => {
            bail!("couldn't find unique matching device ({n} found)");
        }
    };

    let output = dest.join("FIRMWARE.UF2");
    do_common_pack(
        global,
        &args.common,
        &args.inputs,
        &output,
    )
}

fn do_common_pack(
    _global: &GlobalFlags,
    args: &PackAndFlashArgs,
    inputs: &[PathBuf],
    output: &PathBuf,
) -> Result<()> {
    if args.block_size > 476 {
        bail!(
            "requested block size {} exceeds UF2 max of 476",
            args.block_size,
        );
    }

    if let Some(erase) = args.pad_erase_sectors {
        if erase % args.block_size != 0 {
            bail!(
                "erase sector size {} must be an even multiple \
                 of block size (currently {})",
                erase,
                args.block_size,
            );
        }
    }

    let mut pages = PageStore::with_page_size(args.block_size);

    // Load all the files into a vector so that we can store references into
    // their contents.
    let images = inputs.iter()
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

    if let Some(erase) = args.pad_erase_sectors {
        // Generate a list of the erase sectors touched by the data collected so
        // far. This acts as a worklist for later.
        let mut touched_sectors = BTreeSet::new();
        for (addr, _) in pages.iter() {
            touched_sectors.insert(addr / erase);
        }
        // If any page in any of those sectors is not populated, fill it with
        // padding.
        for sector in touched_sectors {
            let sector_address = sector * erase;
            for page in 0..erase / args.block_size {
                let address = sector_address + page * args.block_size;

                if !pages.has_data_in_page(address) {
                    pages.add(address, &padvec)
                        .expect("error in padding algorithm");
                }
            }
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

    let mut out = std::fs::File::create(output)
        .with_context(|| format!(
            "can't create output file {}",
            output.display(),
        ))?;

    let block_count = pages.page_count() as u32;

    println!(
        "{}image is {} blocks",
        if inputs.len() > 1 { "combined " } else { "" },
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
        blocks: Vec<Option<Uf2Record>>,
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
                blocks: vec![None; record.total_blocks.get() as usize],
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

        if stream.blocks[record.block_no.get() as usize].is_some() {
            println!(
                "ERROR: family {:#010x} block #{} appears more than once",
                record.family_id.get(),
                record.block_no.get(),
            );
        }
        stream.blocks[record.block_no.get() as usize] = Some(record.clone());

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
        let blocks_present = stream.blocks.iter().filter(|r| r.is_some()).count();
        println!();
        println!("family ID {:#08x}:", family_id);
        println!("- expected {} blocks, got {}",
            stream.block_count,
            blocks_present,
        );

        if blocks_present != stream.block_count {
            println!("- not doing further checks because of missing blocks");
            continue;
        }

        if family_id == format::RP2040_FAMILY_ID {
            // Check mitigation for ROM bug. The ROM uses block number to index
            // into a bitset of erased flash pages, instead of transfer address,
            // with the net effect that...
            // - It will unconditionally erase one flash sector per group of 16
            //   UF2 blocks, using the transfer address of the first one seen to
            //   choose the sector.
            // - It will happily write flash pages without erasing them if the
            //   destination erase sector changes within a group of 16 UF2
            //   blocks.
            //
            // Because we can't control the order the blocks are presented to
            // the bootloader by the operating system, the safest mitigation is
            // to require that each group of 16 consecutive (by block number)
            // UF2 blocks targets the _same_ erase sector.
            let mut mitigation_ok = true;
            for sector in stream.blocks.chunks(16) {
                let sector0 = sector[0].as_ref().unwrap();
                let target_sector = sector0.address.get() / 4096;

                let same = sector.iter().all(|r| {
                    r.as_ref().unwrap().address.get() / 4096 == target_sector
                });

                if !same {
                    println!("- ERROR: this file will not flash correctly!");
                    println!("  see: https://github.com/raspberrypi/pico-bootrom/issues/19");
                    mitigation_ok = false;
                    break;
                }
            }

            if mitigation_ok {
                println!("- file will not trigger raspberrypi/pico-bootrom#19 bug");
            }
        }

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
// scan

#[cfg(feature = "sysinfo")]
#[derive(Parser)]
struct ScanArgs {
    #[clap(flatten)]
    filter: BootloaderFilter,
}

#[cfg(feature = "sysinfo")]
fn cmd_scan(
    global: &GlobalFlags,
    args: &ScanArgs,
) -> Result<()> {
    use sysinfo::{DiskExt, SystemExt};

    let sys = sysinfo::System::new_with_specifics(
        sysinfo::RefreshKind::new().with_disks_list()
    );

    let mut matches = vec![];
    for disk in sys.disks() {
        let path = disk.mount_point();
        match read_bootloader_info(&path) {
            Ok(Some(bid)) => {
                let included = args.filter.matches(&bid);
                matches.push((bid, included));
            }
            Ok(None) => (),
            Err(e) => {
                eprintln!("warning: {:?}", e);
                continue;
            }
        }
    }

    if matches.is_empty() {
        println!("no devices found.");
        return Ok(())
    }

    println!("devices found: {}", matches.len());

    println!("{:16} {:16} {:8}{}",
        "CPU", "BOARD", "REV", if args.filter.any_set() { " MATCHES?" } else { "" });
    for (bid, included) in matches {
        println!("{:16} {:16} {:8}{}",
            bid.cpu.as_ref().map(String::as_str).unwrap_or("-"),
            bid.board.as_ref().map(String::as_str).unwrap_or("-"),
            bid.rev.as_ref().map(String::as_str).unwrap_or("-"),
            if args.filter.any_set() {
                if included {
                    " YES"
                } else {
                    " no"
                }
            } else {
                ""
            });
    }

    Ok(())
}

///////////////////////////////////////////////////////////////////////
// Bootloader scan and INFO_UF2.TXT support.

#[cfg(feature = "sysinfo")]
#[derive(Parser)]
struct BootloaderFilter {
    /// CPU type to search for when enumerating UF2 bootloaders. This will be
    /// used to match the first component of the `Board-Id` line of an
    /// `INFO_UF2.TXT` file. If omitted, any CPU type will be accepted.
    #[clap(long)]
    cpu: Option<String>,
    /// Board type to search for when enumerating UF2 bootloaders. This will be
    /// used to match the second component of the `Board-Id` line of an
    /// `INFO_UF2.TXT` file. If omitted, any board will be accepted.
    #[clap(long)]
    board: Option<String>,
    /// Board revision to search for when enumerating UF2 bootloaders. This will
    /// be used to match the third component of the `Board-Id` line of an
    /// `INFO_UF2.TXT` file. If omitted, any board revision will be accepted.
    #[clap(long)]
    revision: Option<String>,
}

impl BootloaderFilter {
    pub fn any_set(&self) -> bool {
        self.cpu.is_some() || self.board.is_some() || self.revision.is_some()
    }

    pub fn matches(&self, bid: &BoardId) -> bool {
        if let Some(cpu_goal) = &self.cpu {
            if bid.cpu.as_ref() != Some(cpu_goal) {
                return false;
            }
        }
        if let Some(board_goal) = &self.board {
            if bid.board.as_ref() != Some(board_goal) {
                return false;
            }
        }
        if let Some(rev_goal) = &self.revision {
            if bid.rev.as_ref() != Some(rev_goal) {
                return false;
            }
        }
        true
    }
}

#[cfg(feature = "sysinfo")]
fn read_bootloader_info(
    path: &std::path::Path,
) -> Result<Option<BoardId>> {
    let info = path.join("INFO_UF2.TXT");
    if !info.is_file() {
        return Ok(None);
    }

    let contents = std::fs::read_to_string(&info)
        .with_context(|| format!("reading {}", info.display()))?;

    let board_id_line = contents.lines()
        .find(|line| line.starts_with("Board-ID: "))
        .ok_or_else(|| anyhow!("INFO_UF2.TXT does not contain Board-ID"))?;
    // Strip off the label...
    let board_id_line = &board_id_line["Board-ID: ".len()..];
    // ...and split it up.
    let mut components = board_id_line.split('-');
    let cpu = components.next().map(String::from);
    let board = components.next().map(String::from);
    let rev = components.next().map(String::from);

    Ok(Some(BoardId { cpu, board, rev }))
}

struct BoardId {
    cpu: Option<String>,
    board: Option<String>,
    rev: Option<String>,
}

#[cfg(feature = "sysinfo")]
fn check_bootloader(
    path: &std::path::Path,
    filter: &BootloaderFilter,
) -> Result<bool> {
    if let Some(bid) = read_bootloader_info(path)? {
        Ok(filter.matches(&bid))
    } else {
        Ok(false)
    }
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

fn parse_family(s: &str) -> Result<u32> {
    // Try parsing as an integer first.
    match parse_u32(s) {
        Ok(f) => Ok(f),
        Err(_e) => {
            // Try looking it up. Special-case the "help" family first.
            if s == "help" {
                eprintln!("Defined UF2 families:");
                eprintln!("{:10} {:16} {}", "HEX", "NAME", "DESCRIPTION");
                for (id, name, desc) in FAMILIES {
                    eprintln!("{:#10x} {:16} {}", id, name, desc);
                }
                bail!("choose a hex value or name from the list above.");
            }

            // The build system sorts the families by name, so we can use binary
            // search to quickly and easily find any match:
            match FAMILIES.binary_search_by_key(&s, |(_, name, _)| name) {
                Ok(i) => Ok(FAMILIES[i].0),
                Err(_) => {
                    bail!("can't parse {} as family name or number \
                        (use --family-id=help for list)", s);
                }
            }
        }
    }
}

include!(concat!(env!("OUT_DIR"), "/uf2families.rs"));
