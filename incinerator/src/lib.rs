pub mod compress;
mod compression;
pub mod decompress;
mod diff;
mod page;

pub use crate::page::{AlignedPage, PAGE_SIZE};
use std::io::{self, Read};

pub use crate::{compress::CompressionBase as CompressBase, diff::MemoryDiff};

// at most address_space / PAGE_SIZE
// supports address spaces up to 4 TiB (2^(32-2) * PAGE_SIZE bytes)
type PageIndex = u32;
pub const MAX_PAGE_INDEX: PageIndex = 0x3FFF_FFFF;

// at most PAGE_SIZE
type ByteIndex = u16;

fn read_const<const N: usize>(mut reader: impl Read) -> io::Result<[u8; N]> {
    let mut buf = [0; N];
    reader.read_exact(&mut buf)?;
    Ok(buf)
}
