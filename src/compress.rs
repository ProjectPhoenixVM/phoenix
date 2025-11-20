use std::{
    array::from_fn,
    collections::hash_map::Entry,
    fs::File,
    io::{BufWriter, Write as _},
    iter::zip,
    ops::Index,
};

use ahash::AHashMap;
use rand::{Rng, SeedableRng as _};
use rustc_hash::FxHashMap;

use crate::{
    ByteIndex, MAX_PAGE_INDEX, PageIndex, PhoenixCompressArgs,
    compression::compress_page,
    diff::{FULL_PAGE_FLAG, MemoryDiff},
    page::{AlignedPage, PAGE_SIZE, ZERO_PAGE, page_xor, read_pages},
};

const SAMPLE_SIZE: usize = size_of::<SampleKey>();
const NUM_HASHES: usize = 16;
const PAGES_PER_HASH: usize = 4;

type SampleKey = u64;

struct UniquePages<'a> {
    pub unique_indices: Vec<PageIndex>,
    pub unique_pages: AHashMap<&'a AlignedPage, u32>,
    pub pages: &'a [AlignedPage],
}

impl<'a> UniquePages<'a> {
    pub fn new(pages: &'a [AlignedPage]) -> Self {
        let mut unique_indices = Vec::new();
        let mut unique_pages = AHashMap::<&AlignedPage, PageIndex>::with_capacity(pages.len());
        for (page_index, page) in pages.iter().enumerate() {
            if page.is_zero() {
                continue;
            }

            let entry = unique_pages.entry(page);
            if matches!(entry, Entry::Vacant(_)) {
                entry.or_insert(page_index as _);
                unique_indices.push(page_index as _);
            }
        }
        Self {
            unique_indices,
            unique_pages,
            pages,
        }
    }

    pub fn enumerate(&self) -> impl Iterator<Item = (PageIndex, &'a AlignedPage)> {
        self.unique_indices
            .iter()
            .map(|i| (*i, &self.pages[*i as usize]))
    }
}

impl Index<PageIndex> for UniquePages<'_> {
    type Output = AlignedPage;

    fn index(&self, index: PageIndex) -> &Self::Output {
        &self.pages[index as usize]
    }
}

#[derive(Debug)]
struct RandomVec<const N: usize> {
    count: PageIndex,
    storage: [PageIndex; N],
}

impl<const N: usize> Default for RandomVec<N> {
    fn default() -> Self {
        Self {
            count: 0,
            storage: [0; N],
        }
    }
}

impl<const N: usize> RandomVec<N> {
    fn push(&mut self, val: PageIndex, rng: &mut impl Rng) {
        if self.count < N as PageIndex {
            self.storage[self.count as usize] = val;
            self.count += 1;
            return;
        }

        let score = rng.random_range(0..self.count);
        if score < N as PageIndex {
            self.storage[score as usize] = val;
        }
        self.count += 1;
    }

    fn as_slice(&self) -> &[PageIndex] {
        if self.count < N as PageIndex {
            &self.storage[..self.count as usize]
        } else {
            &self.storage[..]
        }
    }
}

fn sample(page: &AlignedPage, indices: [ByteIndex; SAMPLE_SIZE]) -> SampleKey {
    SampleKey::from_ne_bytes(from_fn(|i| page[indices[i] as usize]))
}

type SampledHashMap = FxHashMap<u64, RandomVec<PAGES_PER_HASH>>;

struct SampledMultiHashMap<'a> {
    indices: [[ByteIndex; SAMPLE_SIZE]; NUM_HASHES],
    maps: [SampledHashMap; NUM_HASHES],
    pages: UniquePages<'a>,
}

impl<'a> SampledMultiHashMap<'a> {
    pub fn new(rng: &mut impl Rng, pages: UniquePages<'a>) -> Self {
        let indices = from_fn(|_| from_fn(|_| rng.random_range(0..PAGE_SIZE as ByteIndex)));
        let mut maps = from_fn(|_| {
            let mut map = SampledHashMap::default();
            map.reserve(pages.unique_indices.len());
            map
        });

        for (page_index, page) in pages.enumerate() {
            for (sampler, map) in zip(indices, &mut maps) {
                let sample = sample(page, sampler);
                if sample == 0 {
                    continue;
                }
                map.entry(sample).or_default().push(page_index as _, rng);
            }
        }

        Self {
            indices,
            maps,
            pages,
        }
    }

    pub fn best_match(&self, page: &AlignedPage) -> Option<(usize, PageIndex)> {
        let mut best_diff = PAGE_SIZE;
        let mut best_index = FULL_PAGE_FLAG;
        for (sampler, map) in zip(self.indices, &self.maps) {
            let sample = sample(page, sampler);
            let Some(bucket) = map.get(&sample) else {
                continue;
            };
            for &candidate in bucket.as_slice() {
                let diff = page.byte_diff(&self.pages[candidate]);
                if diff < best_diff {
                    best_diff = diff;
                    best_index = candidate;
                }
            }
        }
        (best_diff != PAGE_SIZE).then_some((best_diff, best_index))
    }
}

struct Inputs {
    parent: Box<[AlignedPage]>,
    child: Box<[AlignedPage]>,
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn read_from_disk(parent_file_name: String, child_file_name: String) -> anyhow::Result<Inputs> {
    let parent = read_pages(File::open(parent_file_name)?)?;
    let child = read_pages(File::open(child_file_name)?)?;
    if parent.len() > MAX_PAGE_INDEX as usize * PAGE_SIZE {
        anyhow::bail!("Parent should not have more than {MAX_PAGE_INDEX} pages");
    }
    if child.len() > MAX_PAGE_INDEX as usize * PAGE_SIZE {
        anyhow::bail!("Child should not have more than {MAX_PAGE_INDEX} pages");
    }
    Ok(Inputs { parent, child })
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn preprocess_parent(parent: &[AlignedPage]) -> SampledMultiHashMap<'_> {
    let pages = UniquePages::new(&parent);

    let mut rng = rand::rngs::StdRng::seed_from_u64(12345u64);
    let sample_map = SampledMultiHashMap::new(&mut rng, pages);

    sample_map
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn compress_child(sample_map: &SampledMultiHashMap, child_pages: &[AlignedPage]) -> MemoryDiff {
    let mut diff = MemoryDiff::default();
    for page in child_pages {
        if page.is_zero() {
            diff.push_zero_page();
            continue;
        }
        if let Some(&exact_match) = sample_map.pages.unique_pages.get(page) {
            diff.push_exact_match(exact_match);
            continue;
        }

        let nonzero_bytes = page.byte_diff(&ZERO_PAGE);

        if let Some((best_diff, best_match)) = sample_map.best_match(page)
            && best_diff + 4 < nonzero_bytes
        // 4 is the additional overhead of diffing
        {
            let xor = page_xor(page, &sample_map.pages[best_match]);

            let mut compressed_delta_buf = ZERO_PAGE;
            let compressed_diff = compress_page(&xor, &mut *compressed_delta_buf);

            diff.push_diff_page(
                best_match,
                compressed_diff.method,
                &compressed_delta_buf[..compressed_diff.len() as usize],
            );
            continue;
        }

        let mut compressed_buf = ZERO_PAGE;
        let compressed_page = compress_page(page, &mut *compressed_buf);

        diff.push_full_page(
            compressed_page.method,
            &compressed_buf[..compressed_page.len() as usize],
        );
    }
    diff
}

#[cfg(all(not(feature = "lz4_recompress"), not(feature = "zstd_recompress")))]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn recompress(diff: MemoryDiff) -> anyhow::Result<Vec<u8>> {
    let mut compressed = Vec::new();
    diff.write(&mut compressed)?;
    Ok(compressed)
}

#[cfg(feature = "zstd_recompress")]
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn recompress(diff: MemoryDiff) -> anyhow::Result<Vec<u8>> {
    let mut compressed = Vec::new();
    let mut encoder = zstd::Encoder::new(&mut compressed, 0)?;
    diff.write(&mut encoder)?;
    encoder.finish()?;
    Ok(compressed)
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
#[cfg(feature = "lz4_recompress")]
fn recompress(diff: MemoryDiff) -> anyhow::Result<Vec<u8>> {
    let mut compressed = Vec::new();
    let mut encoder = lz4_flex::frame::FrameEncoder::new(&mut compressed);
    diff.write(&mut encoder)?;
    encoder.finish()?;
    Ok(compressed)
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
fn write_to_disk(data: Vec<u8>, file_name: String) -> anyhow::Result<()> {
    BufWriter::new(File::create(file_name)?)
        .write_all(&data)
        .map_err(Into::into)
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn compress(parent: &[AlignedPage], child: &[AlignedPage]) -> anyhow::Result<Vec<u8>> {
    let sample_map = preprocess_parent(&parent);
    let diff = compress_child(&sample_map, &child);
    recompress(diff)
}

#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
pub fn compress_files(args: PhoenixCompressArgs) -> anyhow::Result<()> {
    let Inputs { parent, child } = read_from_disk(args.parent, args.child)?;
    let compressed = compress(&parent, &child)?;
    write_to_disk(compressed, args.output)?;
    Ok(())
}
