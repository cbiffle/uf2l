// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A data structure for collecting chunks of bytes across flash pages.

use anyhow::{Context, Result, bail};
use std::collections::BTreeMap;

/// Models a subset of an address space consisting of fixed-sized pages, which
/// can be populated by references to data with lifetime `'a`.
///
/// The address space is `usize`-sized for convenience, though in our
/// application we expect this to be used for 32-bit address spaces.
#[derive(Clone, Debug)]
pub struct PageStore<'a> {
    /// Number of bytes per page.
    page_size: usize,
    /// Pages keyed by _index,_ which is their base address divided by
    /// `page_size`.
    pages: BTreeMap<usize, Page<'a>>,
}

impl<'a> PageStore<'a> {
    /// Creates an empty page store configured for a given page size.
    pub fn with_page_size(page_size: usize) -> Self {
        Self {
            page_size,
            pages: BTreeMap::new(),
        }
    }

    /// Splat `data` into the address space starting at `address`. The data
    /// reference will be retained, not copied.
    ///
    /// If `data` is empty, this is a no-op.
    pub fn add(&mut self, mut address: usize, mut data: &'a [u8]) -> Result<()> {
        if data.is_empty() {
            // Don't populate pages just to put nothing in them.
            return Ok(());
        }

        let ps = self.page_size;

        // Distribute data over pages.

        // First, does the data begin on a non-page-boundary? If so, we have a
        // sub-page-sized piece to add first.
        if address % ps != 0 {
            let (head, rest) = data.split_at(ps - address % ps);
            self.page_mut(address / ps).add(
                address % ps,
                head,
            ).with_context(|| {
                format!("can't add {} bytes at address {:#010x}",
                    data.len(),
                    address)
            })?;
            data = rest;
            address += head.len();
        }

        // Now, do the page-aligned portions.
        for chunk in data.chunks(ps) {
            self.page_mut(address / ps).add(0, chunk)
                .with_context(|| {
                format!("can't add {} bytes at address {:#010x}",
                    chunk.len(),
                    address)
                })?;
            address += chunk.len();
        }

        Ok(())
    }

    pub fn page_mut(&mut self, index: usize) -> &mut Page<'a> {
        self.pages.entry(index).or_default()
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &'_ Page<'a>)> {
        self.pages.iter().map(|(&a, p)| (a * self.page_size, p))
    }

    /// Returns the number of pages with data in them. This is called
    /// `page_count` rather than `len` because `len` is easily confused with
    /// "size of the address space covered by this pagestore," which is not what
    /// this function does.
    pub fn page_count(&self) -> usize {
        self.pages.len()
    }
}

/// Tracks data extents within a single page, all of which reference backing
/// data with lifetime `'a`.
#[derive(Debug, Clone, Default)]
pub struct Page<'a> {
    extents: BTreeMap<usize, &'a [u8]>,
}

impl<'a> Page<'a> {
    /// Add `data` at `offset` within this page. The page size is not checked,
    /// since pages don't know the page size -- the `PageStore` is responsible
    /// for this.
    ///
    /// `data` must not be empty, lest the page accumulate an infinite number of
    /// empty extents without describing anything useful.
    ///
    /// NOTE: this is private to help maintain our invariant on empty pages.
    fn add(&mut self, offset: usize, data: &'a [u8]) -> Result<()> {
        assert!(!data.is_empty());

        // See if this offset is within the range of the earlier extent, if any.
        if let Some((o, s)) = self.extents.range(..offset).next_back() {
            let end = o + s.len();
            if end > offset {
                bail!("can't build page: {} bytes at offset {} would \
                       overlap with {} bytes at offset {}",
                      data.len(),
                      offset,
                      s.len(),
                      o,
                );
            }
        }
        // See if it would overlap the later extent, if any.
        if let Some((o, s)) = self.extents.range(offset..).next() {
            let our_end = offset + data.len();
            if our_end > 0 {
                bail!("can't build page: {} bytes at offset {} would \
                       overlap with {} bytes at offset {}",
                      data.len(),
                      offset,
                      s.len(),
                      o,
                );
            }
        }

        // Sounds like it's no problem then.
        self.extents.insert(offset, data);
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.extents.iter().next_back()
            .map(|(o, d)| o + d.len())
            .unwrap_or(0)
    }

    /// Copies the contents of this page into `dest`, filling in any gaps using
    /// the `pad` byte. If `dest` is longer than the page, its tail will also be
    /// filled with `pad`.
    pub fn write_into(&self, dest: &mut [u8], pad: u8) {
        let mut last = 0;
        for (&offset, data) in &self.extents {
            if last != offset {
                dest[last..offset].fill(pad);
            }
            dest[offset..offset + data.len()].copy_from_slice(data);

            last = offset + data.len();
        }
        if last < dest.len() {
            dest[last..].fill(pad);
        }
    }
}
