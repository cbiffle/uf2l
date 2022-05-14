// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! UF2 file format definitions and magic constants.

use zerocopy::{AsBytes, FromBytes, U32};
use byteorder::LittleEndian;

#[derive(Clone, AsBytes, FromBytes)]
#[repr(C)]
pub struct Uf2Record {
    pub magic: [U32<LittleEndian>; 2],
    pub flags: U32<LittleEndian>,
    pub address: U32<LittleEndian>,
    pub length: U32<LittleEndian>,
    pub block_no: U32<LittleEndian>,
    pub total_blocks: U32<LittleEndian>,
    pub family_id: U32<LittleEndian>,

    pub data: [u8; 476],

    pub final_magic: U32<LittleEndian>,
}

impl Uf2Record {
    pub const MAGIC: [u32; 2] = [0x0A324655, 0x9E5D5157];
    pub const FINAL_MAGIC: u32 = 0x0AB16F30;

    /// Produces a `Uf2Record` that has been initialized for a file containing
    /// `total_blocks` blocks and targeting `family_id`.
    ///
    /// The record is initialized except for the following fields, which you
    /// need to fill in:
    /// - `address`
    /// - `length`
    /// - `block_no`
    /// - `data`
    pub fn prototype(total_blocks: u32, family_id: u32) -> Self {
        Self {
            magic: [
                U32::new(Uf2Record::MAGIC[0]),
                U32::new(Uf2Record::MAGIC[1]),
            ],
            flags: U32::new(0x00002000),
            total_blocks: U32::new(total_blocks),
            family_id: U32::new(family_id),

            final_magic: U32::new(Uf2Record::FINAL_MAGIC),

            // Start of bogus fields
            address: U32::new(!0),
            length: U32::new(!0),
            block_no: U32::new(!0),
            data: [0; 476],
        }
    }
}

pub const RP2040_FAMILY_ID: u32 = 0xe48bff56;
