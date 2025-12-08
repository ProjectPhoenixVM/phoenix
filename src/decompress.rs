use std::borrow::Cow;

use crate::{diff::MemoryDiff, page::AlignedPage};

#[cfg(all(not(feature = "lz4_recompress"), not(feature = "zstd_recompress")))]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
    Ok(Cow::Borrowed(compressed_diff))
}

#[cfg(feature = "lz4_recompress")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
    use lz4_flex::frame::FrameDecoder as Decoder;
    use std::io::Read;
    let mut new_diff = Vec::new();
    Decoder::new(compressed_diff).read_to_end(&mut new_diff)?;
    Ok(Cow::Owned(new_diff))
}

#[cfg(feature = "zstd_recompress")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
    use std::io::Read;
    use zstd::Decoder;
    let mut new_diff = Vec::new();
    Decoder::new(compressed_diff)?.read_to_end(&mut new_diff)?;
    Ok(Cow::Owned(new_diff))
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn reconstruct_diff_metadata(diff: &[u8]) -> anyhow::Result<MemoryDiff> {
    MemoryDiff::read(&mut &*diff).map_err(Into::into)
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn reconstruct_child(parent: &[AlignedPage], diff: &MemoryDiff) -> Box<[AlignedPage]> {
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

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn decompress(
    parent: &[AlignedPage],
    compressed_diff: &[u8],
) -> anyhow::Result<Box<[AlignedPage]>> {
    let diff = decompress_overall(compressed_diff)?;
    let diff = reconstruct_diff_metadata(&*diff)?;
    Ok(reconstruct_child(parent, &diff))
}
