use std::{
    fs::File,
    io::{self, BufWriter, Read, Write as _},
};

use clap::{Args, Parser};
use incinerator::{AlignedPage, PAGE_SIZE};

fn main() -> anyhow::Result<()> {
    #[cfg(feature = "tracing")]
    {
        use tracing_subscriber::fmt::{self, format::FmtSpan};
        fmt::fmt().with_span_events(FmtSpan::CLOSE).init();
    }

    match PhoenixArgs::parse() {
        PhoenixArgs::Compress(args) => compress::compress_files(args),
        PhoenixArgs::Decompress(args) => decompress::decompress_files(args),
    }
}

#[derive(Parser)]
enum PhoenixArgs {
    Compress(compress::PhoenixCompressArgs),
    Decompress(decompress::PhoenixDecompressArgs),
}

pub fn read_pages(mut file: File) -> anyhow::Result<Box<[AlignedPage]>> {
    let file_len = file.metadata()?.len();
    if !file_len.is_multiple_of(PAGE_SIZE as _) {
        anyhow::bail!("File should be a multiple of {PAGE_SIZE}");
    }
    let mut pages = Vec::with_capacity(file_len as usize / PAGE_SIZE);
    let mut buf = AlignedPage::default();
    loop {
        let res = file.read_exact(&mut *buf);
        if let Err(e) = res {
            if e.kind() == io::ErrorKind::UnexpectedEof {
                break;
            }
            return Err(e.into());
        }
        pages.push(buf);
    }
    Ok(pages.into_boxed_slice())
}

#[derive(Default, Clone, Copy, clap::ValueEnum)]
pub enum RecompressMode {
    #[default]
    None,
    Zstd,
    Lz4,
}

mod compress {
    use super::*;

    #[derive(Args)]
    pub struct PhoenixCompressArgs {
        parent: String,
        child: String,
        output: String,
        recompress_mode: Option<RecompressMode>,
    }

    struct Inputs {
        parent: Box<[incinerator::AlignedPage]>,
        child: Box<[incinerator::AlignedPage]>,
    }

    #[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
    fn read_from_disk(parent_file_name: String, child_file_name: String) -> anyhow::Result<Inputs> {
        let parent = read_pages(File::open(parent_file_name)?)?;
        let child = read_pages(File::open(child_file_name)?)?;
        if parent.len() > incinerator::MAX_PAGE_INDEX as usize * incinerator::PAGE_SIZE {
            anyhow::bail!(
                "Parent should not have more than {} pages",
                incinerator::MAX_PAGE_INDEX
            );
        }
        if child.len() > incinerator::MAX_PAGE_INDEX as usize * incinerator::PAGE_SIZE {
            anyhow::bail!(
                "Child should not have more than {} pages",
                incinerator::MAX_PAGE_INDEX
            );
        }
        Ok(Inputs { parent, child })
    }

    #[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
    fn write_to_disk(data: Vec<u8>, file_name: String) -> anyhow::Result<()> {
        BufWriter::new(File::create(file_name)?)
            .write_all(&data)
            .map_err(Into::into)
    }

    #[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
    pub fn compress_files(args: PhoenixCompressArgs) -> anyhow::Result<()> {
        let Inputs { parent, child } = read_from_disk(args.parent, args.child)?;
        let compressed =
            incinerator::CompressBase::new(&parent, rand::rng()).compress_pages(&child);
        let written = match args.recompress_mode.unwrap_or_default() {
            RecompressMode::None => incinerator::compress::write(&compressed)?,
            RecompressMode::Zstd => incinerator::compress::write_zstd(&compressed)?,
            RecompressMode::Lz4 => incinerator::compress::write_lz4(&compressed)?,
        };
        write_to_disk(written, args.output)?;
        Ok(())
    }
}

mod decompress {
    use super::*;

    #[derive(Args)]
    pub struct PhoenixDecompressArgs {
        parent: String,
        diff: String,
        output: String,
        recompress_mode: Option<RecompressMode>,
    }

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

    fn write_child_to_disk(child: Box<[AlignedPage]>, file_name: String) -> anyhow::Result<()> {
        File::create(file_name)?
            .write_all(bytemuck::cast_slice(&child))
            .map_err(Into::into)
    }

    #[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
    pub fn decompress_files(args: PhoenixDecompressArgs) -> anyhow::Result<()> {
        let Inputs {
            parent,
            compressed_diff,
        } = read_from_disk(args.parent, args.diff)?;
        let bytes = match args.recompress_mode.unwrap_or_default() {
            RecompressMode::None => compressed_diff.into(),
            RecompressMode::Zstd => {
                incinerator::decompress::decompress_zstd(compressed_diff.as_slice())?
            }
            RecompressMode::Lz4 => {
                incinerator::decompress::decompress_lz4(compressed_diff.as_slice())?
            }
        };
        let diff = incinerator::MemoryDiff::read_from_slice(&*bytes)?;
        let child = incinerator::decompress::reconstruct_child(&*parent, &diff);
        write_child_to_disk(child, args.output)?;
        Ok(())
    }
}
