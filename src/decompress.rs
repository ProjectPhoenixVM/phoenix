use std::{
    borrow::Cow,
    fs::File,
    io::{Read, Write as _},
};

use crate::{
    PhoenixDecompressArgs,
    diff::MemoryDiff,
    page::{AlignedPage, read_pages},
};

struct Inputs {
    parent: Box<[AlignedPage]>,
    compressed_diff: Vec<u8>,
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn read_from_disk(parent_file_name: String, diff_file_name: String) -> anyhow::Result<Inputs> {
    let parent = read_pages(File::open(parent_file_name)?)?;
    let mut compressed_diff = Vec::new();
    File::open(diff_file_name)?.read_to_end(&mut compressed_diff)?;
    Ok(Inputs {
        parent,
        compressed_diff,
    })
}

#[cfg(all(not(feature = "lz4_recompress"), not(feature = "zstd_recompress")))]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
    Ok(Cow::Borrowed(compressed_diff))
}

#[cfg(feature = "lz4_recompress")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
    use lz4_flex::frame::FrameDecoder as Decoder;
    let mut new_diff = Vec::new();
    Decoder::new(compressed_diff).read_to_end(&mut new_diff)?;
    Ok(Cow::Owned(new_diff))
}

#[cfg(feature = "zstd_recompress")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn decompress_overall(compressed_diff: &[u8]) -> anyhow::Result<Cow<'_, [u8]>> {
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

fn write_child_to_disk(child: Box<[AlignedPage]>, file_name: String) -> anyhow::Result<()> {
    File::create(file_name)?
        .write_all(bytemuck::cast_slice(&child))
        .map_err(Into::into)
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

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn decompress_files(args: PhoenixDecompressArgs) -> anyhow::Result<()> {
    let Inputs {
        parent,
        compressed_diff,
    } = read_from_disk(args.parent, args.diff)?;
    let child = decompress(&parent, &compressed_diff)?;
    write_child_to_disk(child, args.output)?;
    Ok(())
}
