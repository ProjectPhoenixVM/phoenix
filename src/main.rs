mod compress;

use crate::compress::{CompressionMethod, compress_page, decompress_page};

use std::{
    array::from_fn,
    collections::hash_map::Entry,
    fs::File,
    hash::{Hash, Hasher},
    io::{self, BufWriter, Read, Write},
    iter::zip,
    ops::{Deref, DerefMut, Index},
};

use ahash::AHashMap;
use clap::{Args, Parser};
use rand::{Rng, SeedableRng as _};
use rustc_hash::FxHashMap;

const PAGE_SIZE: usize = 1024 * 4;
const PAGE_SIZE_U64: usize = PAGE_SIZE / size_of::<u64>();
type Page = [u8; PAGE_SIZE];

#[repr(align(64), C)]
#[derive(PartialEq, Eq, Clone, Copy, bytemuck::AnyBitPattern, bytemuck::NoUninit)]
struct AlignedPage(Page);

impl Default for AlignedPage {
    fn default() -> Self {
        Self([0; PAGE_SIZE])
    }
}

const ZERO_PAGE: AlignedPage = AlignedPage([0; _]);

impl Deref for AlignedPage {
    type Target = Page;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for AlignedPage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl AlignedPage {
    pub fn is_zero(&self) -> bool {
        // This optimizes better than a naive loop
        self.0
            .as_chunks::<64>()
            .0
            .iter()
            .all(|b| b.iter().all(|&y| y == 0))
    }

    pub fn as_u64(&self) -> &[u64; PAGE_SIZE_U64] {
        bytemuck::cast_ref(&self.0)
    }

    pub fn byte_diff(&self, other: &Self) -> usize {
        const VECTOR_SIZE: usize = 128;
        type Vector = [u8; VECTOR_SIZE];
        const NUM_VECTORS: usize = PAGE_SIZE / VECTOR_SIZE;
        const {
            if NUM_VECTORS > u8::MAX as usize {
                panic!("Byte diff per-element sum may overflow u8");
            }
        }

        let (base_chunks, rem) = self.0.as_chunks::<VECTOR_SIZE>();
        assert_eq!(rem.len(), 0);
        let (new_chunks, rem) = other.0.as_chunks::<VECTOR_SIZE>();
        assert_eq!(rem.len(), 0);

        const ZERO_VEC: Vector = [0; _];

        let mut running_sum: Vector = ZERO_VEC;
        for (base, new) in core::iter::zip(base_chunks, new_chunks) {
            let xor: Vector = from_fn(|i| base[i] ^ new[i]);
            let biased: Vector = from_fn(|i| xor[i].saturating_add(u8::MAX - 1));
            running_sum = from_fn(|i| running_sum[i].wrapping_add(biased[i]));
        }

        const ACCUMULATED_OFFSET: u8 = (u8::MAX - 1).wrapping_mul(NUM_VECTORS as u8);

        running_sum
            .map(|e| e.wrapping_sub(ACCUMULATED_OFFSET))
            .into_iter()
            .map(|e| e as usize)
            .sum::<usize>()
    }
}

impl Hash for AlignedPage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_u64().hash(state);
    }
}

fn page_xor(a: &AlignedPage, b: &AlignedPage) -> AlignedPage {
    AlignedPage(core::array::from_fn(|i| a.0[i] ^ b.0[i]))
}

const SAMPLE_SIZE: usize = size_of::<SampleKey>();
const NUM_HASHES: usize = 16;
const PAGES_PER_HASH: usize = 4;

// at most address_space / PAGE_SIZE
// supports address spaces up to 4 TiB (2^(32-2) * PAGE_SIZE bytes)
type PageIndex = u32;
const ZERO_PAGE_INDEX: PageIndex = 0xC000_0000;
const PAGE_FLAG_MASK: PageIndex = 0xC000_0000;
const PARENT_PAGE_FLAG: PageIndex = 0x0000_0000;
const DIFF_PAGE_FLAG: PageIndex = 0x4000_0000;
const FULL_PAGE_FLAG: PageIndex = 0x8000_0000;
const MAX_PAGE_INDEX: PageIndex = 0x3FFF_FFFF;

// at most PAGE_SIZE
type ByteIndex = u16;

type SampleKey = u64;

struct UniquePages<'a> {
    pub unique_indices: Vec<PageIndex>,
    pub unique_pages: AHashMap<&'a AlignedPage, PageIndex>,
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

impl<'a> Index<PageIndex> for UniquePages<'a> {
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
    pages: &'a UniquePages<'a>,
}

impl<'a> SampledMultiHashMap<'a> {
    pub fn new(rng: &mut impl Rng, pages: &'a UniquePages<'a>) -> Self {
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

fn read_const<const N: usize>(mut reader: impl Read) -> io::Result<[u8; N]> {
    let mut buf = [0; N];
    reader.read_exact(&mut buf)?;
    Ok(buf)
}

const COMPRESSED_DIFF_HIGH_BITS: u32 = 16;
const COMPRESSED_DIFF_LOW_BITS: u32 =
    (MAX_PAGE_INDEX + 1).ilog2() + PAGE_SIZE.ilog2() - COMPRESSED_DIFF_HIGH_BITS;

#[derive(Default)]
struct CompressedDiffs {
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
struct CompressedDiffItem<'a> {
    data: &'a [u8],
    method: CompressionMethod,
    base_page: PageIndex,
}

const COMPRESSED_PAGE_HIGH_BITS: u32 =
    (MAX_PAGE_INDEX + 1).ilog2() + PAGE_SIZE.ilog2() - COMPRESSED_PAGE_LOW_BITS;
const COMPRESSED_PAGE_LOW_BITS: u32 = 32 - 8;

#[derive(Default)]
struct CompressedPages {
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
struct CompressedPageItem<'a> {
    data: &'a [u8],
    method: CompressionMethod,
}

#[derive(Default)]
struct MemoryDiff {
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

fn read_pages(mut file: File) -> anyhow::Result<Box<[AlignedPage]>> {
    let file_len = file.metadata()?.len();
    if !file_len.is_multiple_of(PAGE_SIZE as _) {
        anyhow::bail!("File should be a multiple of {}", PAGE_SIZE);
    }
    let mut pages = Vec::with_capacity(file_len as usize / PAGE_SIZE);
    let mut buf = AlignedPage::default();
    loop {
        let res = file.read_exact(&mut buf.0);
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

fn compress(args: PhoenixCompressArgs) -> anyhow::Result<()> {
    let span = tracing::info_span!("file_reading");
    let _guard = span.enter();

    let parent = read_pages(File::open(args.parent)?)?;
    let child = read_pages(File::open(args.child)?)?;

    if parent.len() >= MAX_PAGE_INDEX as usize * PAGE_SIZE {
        anyhow::bail!("Parent should not have more than {} pages", MAX_PAGE_INDEX);
    }
    if child.len() >= MAX_PAGE_INDEX as usize * PAGE_SIZE {
        anyhow::bail!("Child should not have more than {} pages", MAX_PAGE_INDEX);
    }

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("parent_preprocessing");
    let _guard = span.enter();

    let pages = UniquePages::new(&parent);

    let mut rng = rand::rngs::StdRng::seed_from_u64(12345u64);
    let sample_map = SampledMultiHashMap::new(&mut rng, &pages);

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("child_processing");
    let _guard = span.enter();

    let mut diff = MemoryDiff::default();
    for page in &child {
        if page.is_zero() {
            diff.push_zero_page();
            continue;
        }
        if let Some(&exact_match) = pages.unique_pages.get(page) {
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
            let compressed_diff = compress_page(&xor, &mut compressed_delta_buf.0);

            diff.push_diff_page(
                best_match,
                compressed_diff.method,
                &compressed_delta_buf[..compressed_diff.len() as usize],
            );
            continue;
        }

        let mut compressed_buf = ZERO_PAGE;
        let compressed_page = compress_page(page, &mut compressed_buf.0);

        diff.push_full_page(
            compressed_page.method,
            &compressed_buf[..compressed_page.len() as usize],
        );
    }

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("diff_writing");
    let _guard = span.enter();

    let mut output = BufWriter::new(File::create(args.output)?);
    diff.write(&mut output)?;

    drop(_guard);
    drop(span);

    Ok(())
}

fn decompress(args: PhoenixDecompressArgs) -> anyhow::Result<()> {
    let span = tracing::info_span!("diff_reading");
    let _guard = span.enter();

    let parent = read_pages(File::open(args.parent)?)?;
    let mut diff = Vec::new();
    File::open(args.diff)?.read_to_end(&mut diff)?;

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("diff_metadata_construction");
    let _guard = span.enter();

    let mut diff = &diff[..];
    let diff = MemoryDiff::read(&mut diff)?;

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("child_reconstruction");
    let _guard = span.enter();

    let mut child = Vec::with_capacity(diff.num_pages() as _);
    let mut tmp_buf = AlignedPage::default();
    for i in 0..diff.num_pages() {
        let child_page = diff
            .get_page(&parent, i, &mut tmp_buf)
            .expect("Pages 0..num_pages should exist");
        child.push(*child_page);
    }

    drop(_guard);
    drop(span);

    let span = tracing::info_span!("child_writing");
    let _guard = span.enter();

    File::create(args.output)?.write_all(bytemuck::cast_slice(child.as_slice()))?;

    drop(_guard);
    drop(span);

    Ok(())
}

fn main() -> anyhow::Result<()> {
    use tracing_subscriber::fmt::{self, format::FmtSpan};

    fmt::fmt().with_span_events(FmtSpan::CLOSE).init();
    match PhoenixArgs::parse() {
        PhoenixArgs::Compress(args) => compress(args),
        PhoenixArgs::Decompress(args) => decompress(args),
    }
}

#[derive(Parser)]
enum PhoenixArgs {
    Compress(PhoenixCompressArgs),
    Decompress(PhoenixDecompressArgs),
}

#[derive(Args)]
struct PhoenixCompressArgs {
    parent: String,
    child: String,
    output: String,
}

#[derive(Args)]
struct PhoenixDecompressArgs {
    parent: String,
    diff: String,
    output: String,
}
