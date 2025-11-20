use std::io::{self, Read, Write};

use crate::{
    MAX_PAGE_INDEX, PageIndex,
    compression::{CompressionMethod, decompress_page},
    page::{AlignedPage, PAGE_SIZE, ZERO_PAGE, page_xor},
    read_const,
};

pub const ZERO_PAGE_INDEX: PageIndex = 0xC000_0000;
pub const PAGE_FLAG_MASK: PageIndex = 0xC000_0000;
pub const PARENT_PAGE_FLAG: PageIndex = 0x0000_0000;
pub const DIFF_PAGE_FLAG: PageIndex = 0x4000_0000;
pub const FULL_PAGE_FLAG: PageIndex = 0x8000_0000;

pub const COMPRESSED_DIFF_HIGH_BITS: u32 = 16;
pub const COMPRESSED_DIFF_LOW_BITS: u32 =
    (MAX_PAGE_INDEX + 1).ilog2() + PAGE_SIZE.ilog2() - COMPRESSED_DIFF_HIGH_BITS;

const COMPRESSED_PAGE_HIGH_BITS: u32 =
    (MAX_PAGE_INDEX + 1).ilog2() + PAGE_SIZE.ilog2() - COMPRESSED_PAGE_LOW_BITS;
const COMPRESSED_PAGE_LOW_BITS: u32 = 32 - 8;

#[derive(Default)]
pub struct CompressedDiffs {
    packed_metadata: Vec<u64>,
    address_high_bits: Vec<u32>,
    data: Vec<u8>,
}

impl CompressedDiffs {
    // Key only uses lower 30 bits, ie. key & PAGE_FLAG_MASK == 0
    // Packed is 30 bits base_page, 8 bits method, 26 bits low address

    pub fn get(&self, key: u32) -> CompressedDiffItem<'_> {
        let (curr_high, curr_packed) = self.get_raw_item(key).expect("All keys should be valid");
        let addr = Self::addr(curr_high, curr_packed);
        let len = match self.get_raw_item(key + 1) {
            Some((high, packed)) => {
                let next_addr = Self::addr(high, packed);
                next_addr - addr
            }
            None => self.data.len() - addr,
        };
        let method = (curr_packed >> COMPRESSED_DIFF_LOW_BITS & 0xFF) as CompressionMethod;
        let base_page = (curr_packed >> COMPRESSED_DIFF_LOW_BITS >> 8) as PageIndex;
        CompressedDiffItem {
            data: &self.data[addr..][..len],
            method,
            base_page,
        }
    }

    pub fn push(&mut self, data: CompressedDiffItem) -> u32 {
        let addr = self.data.len();
        assert!(
            addr < 1 << (COMPRESSED_DIFF_LOW_BITS + COMPRESSED_DIFF_HIGH_BITS),
            "address should not exceed MAX_PAGE_INDEX * PAGE_SIZE"
        );
        let high_bits = (addr >> COMPRESSED_DIFF_LOW_BITS) as u16 & (u16::MAX);
        let low_bits = addr & ((1 << COMPRESSED_DIFF_LOW_BITS) - 1);

        let new_key = self.packed_metadata.len() as u32;
        let packed =
            (data.base_page as u64 & !(PAGE_FLAG_MASK as u64)) << 8 << COMPRESSED_DIFF_LOW_BITS
                | (data.method as u64) << COMPRESSED_DIFF_LOW_BITS
                | low_bits as u64;
        self.packed_metadata.push(packed);

        if high_bits as usize > self.address_high_bits.len() + 1 {
            panic!("Unexpected jump in address");
        } else if high_bits as usize == self.address_high_bits.len() + 1 {
            self.address_high_bits.push(new_key);
        } else if (high_bits as usize) < self.address_high_bits.len() {
            panic!("Addresses should be in order");
        }

        self.data.extend(data.data);

        new_key
    }

    pub fn write(&self, mut writer: impl Write) -> io::Result<()> {
        writer.write_all(&(self.packed_metadata.len() as u32).to_be_bytes())?;
        writer.write_all(&(self.address_high_bits.len() as u16).to_be_bytes())?;
        writer.write_all(&(self.data.len() as u64).to_be_bytes())?;

        for packed in &self.packed_metadata {
            writer.write_all(&packed.to_be_bytes())?;
        }

        for high_bits in &self.address_high_bits {
            writer.write_all(&high_bits.to_be_bytes())?;
        }

        writer.write_all(self.data.as_slice())?;
        Ok(())
    }

    pub fn read(mut reader: impl Read) -> io::Result<Self> {
        let num_metadata = u32::from_be_bytes(read_const(&mut reader)?);
        let num_high_bits = u16::from_be_bytes(read_const(&mut reader)?);
        let num_data = u64::from_be_bytes(read_const(&mut reader)?);
        let mut packed_metadata = Vec::with_capacity(num_metadata as usize);
        for _ in 0..num_metadata {
            packed_metadata.push(u64::from_be_bytes(read_const(&mut reader)?));
        }
        let mut address_high_bits = Vec::with_capacity(num_high_bits as usize);
        for _ in 0..num_high_bits {
            address_high_bits.push(u32::from_be_bytes(read_const(&mut reader)?));
        }
        let mut data = vec![0; num_data as usize];
        reader.read_exact(&mut data)?;

        Ok(Self {
            packed_metadata,
            address_high_bits,
            data,
        })
    }

    fn get_raw_item(&self, key: u32) -> Option<(u16, u64)> {
        let &packed = self.packed_metadata.get(key as usize)?;
        let high_bits = match self.address_high_bits.binary_search(&key) {
            Ok(v) => v as u16 + 1,
            Err(v) => v as u16,
        };
        Some((high_bits, packed))
    }

    fn addr(high_bits: u16, packed: u64) -> usize {
        let low_bits = packed & ((1 << COMPRESSED_DIFF_LOW_BITS) - 1);
        (high_bits as usize) << COMPRESSED_DIFF_LOW_BITS | low_bits as usize
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CompressedDiffItem<'a> {
    pub data: &'a [u8],
    pub method: CompressionMethod,
    pub base_page: PageIndex,
}

#[derive(Default)]
pub struct CompressedPages {
    packed_metadata: Vec<u32>,
    address_high_bits: Vec<u32>,
    data: Vec<u8>,
}

impl CompressedPages {
    // Key only uses lower 30 bits, ie. key & PAGE_FLAG_MASK == 0
    // Packed is 8 bits method, 24 bits low address

    pub fn get(&self, key: u32) -> CompressedPageItem<'_> {
        let (curr_high, curr_packed) = self.get_raw_item(key).expect("All keys should be valid");
        let addr = Self::addr(curr_high, curr_packed);
        let len = match self.get_raw_item(key + 1) {
            Some((high, packed)) => {
                let next_addr = Self::addr(high, packed);
                next_addr - addr
            }
            None => self.data.len() - addr,
        };
        let method = (curr_packed >> COMPRESSED_PAGE_LOW_BITS & 0xFF) as CompressionMethod;
        CompressedPageItem {
            data: &self.data[addr..][..len],
            method,
        }
    }

    pub fn push(&mut self, data: CompressedPageItem) -> u32 {
        let addr = self.data.len();
        assert!(
            addr < 1 << (COMPRESSED_PAGE_LOW_BITS + COMPRESSED_PAGE_HIGH_BITS),
            "address should not exceed MAX_PAGE_INDEX * PAGE_SIZE"
        );
        let high_bits = (addr >> COMPRESSED_PAGE_LOW_BITS) as u16 & (u16::MAX);
        let low_bits = addr & ((1 << COMPRESSED_PAGE_LOW_BITS) - 1);

        let new_key = self.packed_metadata.len() as u32;
        let packed = (data.method as u32) << COMPRESSED_PAGE_LOW_BITS | low_bits as u32;
        self.packed_metadata.push(packed);

        if high_bits as usize > self.address_high_bits.len() + 1 {
            panic!("Unexpected jump in address");
        } else if high_bits as usize == self.address_high_bits.len() + 1 {
            self.address_high_bits.push(new_key);
        } else if (high_bits as usize) < self.address_high_bits.len() {
            panic!("Addresses should be in order");
        }

        self.data.extend(data.data);

        new_key
    }

    pub fn write(&self, mut writer: impl Write) -> io::Result<()> {
        writer.write_all(&(self.packed_metadata.len() as u32).to_be_bytes())?;
        writer.write_all(&(self.address_high_bits.len() as u32).to_be_bytes())?;
        writer.write_all(&(self.data.len() as u64).to_be_bytes())?;

        for packed in &self.packed_metadata {
            writer.write_all(&packed.to_be_bytes())?;
        }

        for high_bits in &self.address_high_bits {
            writer.write_all(&high_bits.to_be_bytes())?;
        }

        writer.write_all(self.data.as_slice())?;
        Ok(())
    }

    pub fn read(mut reader: impl Read) -> io::Result<Self> {
        let num_metadata = u32::from_be_bytes(read_const(&mut reader)?);
        let num_high_bits = u32::from_be_bytes(read_const(&mut reader)?);
        let num_data = u64::from_be_bytes(read_const(&mut reader)?);
        let mut packed_metadata = Vec::with_capacity(num_metadata as usize);
        for _ in 0..num_metadata {
            packed_metadata.push(u32::from_be_bytes(read_const(&mut reader)?));
        }
        let mut address_high_bits = Vec::with_capacity(num_high_bits as usize);
        for _ in 0..num_high_bits {
            address_high_bits.push(u32::from_be_bytes(read_const(&mut reader)?));
        }
        let mut data = vec![0; num_data as usize];
        reader.read_exact(&mut data)?;

        Ok(Self {
            packed_metadata,
            address_high_bits,
            data,
        })
    }

    fn get_raw_item(&self, key: u32) -> Option<(u16, u32)> {
        let &packed = self.packed_metadata.get(key as usize)?;
        let high_bits = match self.address_high_bits.binary_search(&key) {
            Ok(v) => v as u16 + 1,
            Err(v) => v as u16,
        };
        Some((high_bits, packed))
    }

    fn addr(high_bits: u16, packed: u32) -> usize {
        let low_bits = packed & ((1 << COMPRESSED_PAGE_LOW_BITS) - 1);
        (high_bits as usize) << COMPRESSED_PAGE_LOW_BITS | low_bits as usize
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CompressedPageItem<'a> {
    pub data: &'a [u8],
    pub method: CompressionMethod,
}

#[derive(Default)]
pub struct MemoryDiff {
    base_pages: Vec<PageIndex>,
    compressed_diffs: CompressedDiffs,
    compressed_pages: CompressedPages,
}

impl MemoryDiff {
    pub fn push_exact_match(&mut self, base_page_index: PageIndex) {
        self.base_pages.push(PARENT_PAGE_FLAG | base_page_index);
    }

    pub fn push_zero_page(&mut self) {
        self.base_pages.push(ZERO_PAGE_INDEX);
    }

    pub fn push_full_page(&mut self, method: CompressionMethod, compressed_page: &[u8]) {
        let data = CompressedPageItem {
            data: compressed_page,
            method,
        };
        let key = self.compressed_pages.push(data);
        self.base_pages.push(FULL_PAGE_FLAG | key);
    }

    pub fn push_diff_page(
        &mut self,
        base_page_index: PageIndex,
        method: CompressionMethod,
        compressed_delta: &[u8],
    ) {
        let data = CompressedDiffItem {
            data: compressed_delta,
            method,
            base_page: base_page_index,
        };
        let key = self.compressed_diffs.push(data);
        self.base_pages.push(DIFF_PAGE_FLAG | key);
    }

    pub fn num_pages(&self) -> u32 {
        self.base_pages.len() as _
    }

    pub fn get_page<'a>(
        &'a self,
        parent: &'a [AlignedPage],
        index: PageIndex,
        tmp_buf: &'a mut AlignedPage,
    ) -> Option<&'a AlignedPage> {
        let &base_page = self.base_pages.get(index as usize)?;
        if base_page == ZERO_PAGE_INDEX {
            return Some(&ZERO_PAGE);
        }
        let flags = base_page & PAGE_FLAG_MASK;
        let data = base_page & !PAGE_FLAG_MASK;

        if flags == PARENT_PAGE_FLAG {
            return parent.get(data as usize);
        }

        if flags == FULL_PAGE_FLAG {
            let key = data;
            let page = self.compressed_pages.get(key);
            decompress_page(page.method, page.data, tmp_buf)
                .expect("Decompression should not fail");

            return Some(&*tmp_buf);
        }

        if flags == DIFF_PAGE_FLAG {
            let key = data;
            let diff = self.compressed_diffs.get(key);
            decompress_page(diff.method, diff.data, tmp_buf)
                .expect("Decompression should not fail");
            let base_page = parent.get(diff.base_page as usize)?;
            *tmp_buf = page_xor(base_page, tmp_buf);

            return Some(&*tmp_buf);
        }
        panic!("Invalid index");
    }

    pub fn write(&self, mut writer: impl Write) -> io::Result<()> {
        writer.write_all(&(self.base_pages.len() as PageIndex).to_be_bytes())?;
        for base_page in &self.base_pages {
            writer.write_all(&base_page.to_be_bytes())?;
        }
        self.compressed_diffs.write(&mut writer)?;
        self.compressed_pages.write(&mut writer)?;
        Ok(())
    }

    pub fn read(mut reader: impl Read) -> io::Result<Self> {
        let num_pages = u32::from_be_bytes(read_const(&mut reader)?);
        let mut base_pages = Vec::with_capacity(num_pages as usize);
        for _ in 0..num_pages {
            base_pages.push(u32::from_be_bytes(read_const(&mut reader)?));
        }

        let compressed_diffs = CompressedDiffs::read(&mut reader)?;
        let compressed_pages = CompressedPages::read(&mut reader)?;

        Ok(Self {
            base_pages,
            compressed_diffs,
            compressed_pages,
        })
    }
}
