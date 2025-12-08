use std::io;

use crate::{diff::MemoryDiff, page::AlignedPage};

#[cfg(feature = "lz4")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn decompress_lz4(compressed_diff: &[u8]) -> io::Result<Box<[u8]>> {
    use lz4_flex::frame::FrameDecoder as Decoder;
    use std::io::Read;
    let mut new_diff = Vec::new();
    Decoder::new(compressed_diff).read_to_end(&mut new_diff)?;
    Ok(new_diff.into_boxed_slice())
}

#[cfg(feature = "zstd")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn decompress_zstd(compressed_diff: &[u8]) -> io::Result<Box<[u8]>> {
    use std::io::Read;
    use zstd::Decoder;
    let mut new_diff = Vec::new();
    Decoder::new(compressed_diff)?.read_to_end(&mut new_diff)?;
    Ok(new_diff.into_boxed_slice())
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn reconstruct_child(parent: &[AlignedPage], diff: &MemoryDiff) -> Box<[AlignedPage]> {
    let mut child = Vec::with_capacity(diff.num_pages() as _);
    let mut tmp_buf = AlignedPage::default();
    for i in 0..diff.num_pages() {
        let child_page = diff
            .get_page(&parent, i, &mut tmp_buf)
            .expect("Pages 0..num_pages should exist");
        child.push(*child_page);
    }
    child.into_boxed_slice()
}
