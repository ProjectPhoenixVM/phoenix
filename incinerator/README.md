Incinerator
===

Fast diff compression library designed for virtual machine memory snapshots

Incinerator compresses a derivative snapshot relative to a base snapshot. The compression process takes the base snapshot and derivative snapshot and produces a compressed diff. The decompression process takes the base snapshot and compressed diff and produces the derivative snapshot.

Snapshots are arrays of pages of memory, or arrays of 4096-byte blocks. Incinerator is designed to only compress derivative snapshots which are the exact same size as their base snapshots. It is possible that Incinerator could support arbitrary sized bases and derivatives with only minor modifications, but that is not explored here.

# Algorithm Specification
Incinerator works in 3 stages: parent preprocessing, page matching, and XOR compression.

The descriptions of parent preprocessing and page matching are excerpted from section 3 of the Phoenix paper.

## Page Matching

Selecting an appropriate base page for each derivative page is critical: better matches lead to XOR arrays with more zero bytes and therefore smaller compressed diffs. A brute force approach would compare each derivative page with every page in the base snapshot and choose the closest match. However, for 128MiB snapshots this
requires $32{,}000^2 = 1.024 \times 10^9$ page comparisons, taking several dozen seconds on our evaluation hardware.

Instead, Incinerator employs a randomized sampling technique that
identifies at most 64 candidate pages for comparison. The algorithm then performs exact byte-difference comparisons only on this candidate set and selects the closest match. Empirically, the best candidate found via sampling is typically within 1-2\% of the brute-force optimum, while reducing comparisons by several orders of magnitude.

## Base Preprocessing

To support fast page matching, Incinerator constructs two data structures: a `HashMap` of all pages in the base snapshot and a `SampledMultiHashMap` of all pages in the base snapshot. The `HashMap` is simple: it maps base snapshot page data (4096-byte arrays) to their indexes in the linear base snapshot address space. The `SampledMultiHashMap` is more complex and inspired by bit-sampling techniques for approximate nearest-neighbor search, the structure consists of 16 independent `SampledHashMap`s. Each `SampledHashMap` is parameterized by 8 byte positions uniformly selected from the half-open range $[0,4096)$. For any page, the `SampledHashMap` extracts an 8-byte sample at those positions and maps the sample to a `RandomVec` containing up to 4 page indices.

Each `RandomVec` implements reservoir sampling: if fewer than 4 pages share a given sample, all are stored; if more than 4 exist, new pages replace existing entries with probability proportional to the number of pages processed so far.

During `SampledMultiHashMap` lookup, the query page's sample is computed for each of the 16 hashmaps, yielding at most 64 total candidate base pages.

### Randomized Sampling Evaluation
Let $Q$ denote a derivative page being queried and $B$ the true best-matching base page. Three scenarios arise:

#### No good matches
If no base page is particularly similar to $Q$, then many/all base pages have approximately the same byte difference. In this case, even a suboptimal match causes minimal additional diff size.

#### Few good matches
Suppose $B$ differs from $Q$ by $d$ bytes, where $d$ is small (e.g., a few hundred). The probability that $Q$ and $B$ share the same 8-byte sample in one hashmap is: `p = (1 - d/4096)^8`

The probability that they collide in at least one of the 16 independent hashmaps is: $q = 1 - (1-p)^{16}$

For small $d$, $p$ is large, so $q \approx 1$. Since few pages are similar to $Q$, few will share its sample, meaning `RandomVec` is unlikely to evict $B$ via reservoir sampling.

#### Many good matches
If many pages resemble $Q$, then many will share its samples. In this case, Incinerator does not need to select $B$ specifically: any highly similar page yields a small diff.

Across all regimes, the sampling scheme reliably returns a near-optimal match whenever one exists.

## `MemoryDiff`
The result of diff compressing a snapshot is a `MemoryDiff`. `MemoryDiff` can be quickly serialized and deserialized; it consists of only arrays of bytes and integers.

Let $n$ be the number of pages in a memory snapshot. For the common case of 128 MiB-size snapshots, $n = 128 MiB / 4 KiB = 32768 = 2^{15}$.

Each page in the base and in the derivative has an index. Treating the snapshot as an array of 4096-byte blocks, a page's index is the number of pages before it in the array; page indices range from $0$ to $n-1$ inclusive.

`MemoryDiff` supports at most $2^{30}$ pages, or snapshots of size $2^{30} \cdot 4 KiB = 4 TiB$. We expect this to be large enough for the forseeable future. If larger snapshot sizes are required, the format can be expanded to support larger snapshots at the cost of larger metadata overhead.

`MemoryDiff` has three sub-strucures: `base_pages`, `compressed_diffs`, and `compressed_pages`.

### `base_pages`
`base_pages` is an array of 32-bit values with $n$ elements. Each value in `base_pages` describes the page in the derivative snapshot at the same index. Ie. the fifth page in the snapshot is described by the fifth value in `base_pages`. Arbitrary page decompression starts by indexing `base_pages` and continues the lookup process based on the 32-bit value.

Each 32-bit value in `base_pages` consists of 2 bits of metadata and 30 bits of key. The metadata is the 2 highest bits and the remaining 30 bits is the key.

Say we are considering the `base_pages` value at index $i$ in `base_pages`. This value describes the data of the $i$th page in the derivative snapshot.

The metadata has the following meaning:
- `0b00`: The derivative page is an exact copy of some page in the base snapshot. The key, when treated as a 30-bit integer, specifies which page in the base snapshot the derivative page is a copy of.
- `0b10`: The derivative page is stored in diff-compressed form. It is stored as a compressed xor of bytes between the derivative page and some base page. The payload is a key which is used to look up the page from `compressed_diffs`.
- `0b10`: The derivative page is stored in a compressed form, with no parent page in the base snapshot. The payload is a key which is used to look up the page from `compressed_pages`.
- `0b11`: The derivative page is the zero page (`[0u8; 4096]`). The key must be zero. Nonzero key is reserved for future revisions of the Incinerator specification.

### `compressed_diffs`
`compressed_diffs` stores compressed derivative pages relative to base pages. At a high level, it is a key-value store mapping opaque keys- integers less than $2^{30}$ -to values- `CompressedDiffItem`s.

A `CompressedDiffItem` consists of `compressed_data`, an arbitrary length compressed array, `method`, a `u8` byte describing the compression method, and `base_page`, an index less than $n$ referring to a page in the base snapshot. The `method` is used to determine how to decompress `data` to yield a page sized (4096-byte) array. The page-sized array can be xor-ed with the page in the base snapshot at index `base_page` to yield the desired derivative page.

`compressed_diffs` is implemented using three arrays:
- `packed_metadata`: an array of `u64`s
- `address_high_bits`: an array of `u32`s
- `data`: an array of `u8` (raw byte array)

`data` is a concatenated array of all pages' individual `compressed_data`. 

Any given page's `compressed_data` should have size at most `4096`, which is the size of the page uncompressed. Since `compressed_diffs` stores at most $2^{30}$ pages, the total size of data is at most $2^{30} \cdot 4096 = 2^{42}$

`address` denotes the starting index of a given page's `compressed_data` within `data`. So, `data[address:address+len(compressed_data)] == compressed_data`. `len(compressed_data)` is not stored explicitly in `compressed_diffs`; because all `compressed_data` are stored back-to-back in `data`, `len(compressed_data)` is equal to the `address` of the `compressed_data` of the next page.

Because `data` is bounded in size, the value of any given page's `address` is less than $2^{42}$. For reasons explained later, we split `address` into its 16 high bits and 26 low bits. `address`'s high bits are only nonzero if `data` has size at least $2^{26} bytes = 64 MiB$. When compressing 128 MiB memory snapshots, it is unlikely that any address will have nonzero high bits.

`packed_metadata` contains bit-packed metadata for each page in `compressed_diffs`. The keys used to lookup pages in `compressed_diffs` are indexes into `packed_metadata` specifying which metadata to perform lookup for.

Each `u64` value in packed metadata can be broken into three parts:
- The highest 30 bits are `base_page`, and specify the base page that the diff is computed relative to
- The next 8 bits are `method`, and tell which compression method was used to compress the diff/should be used to decompress the diff
- The low 26 bits of the `u64` give the low 26 bits of `address`

`address_high_bits` is used to determine the high bits of `address` for a given `key`. `address_high_bits` stores the first `key` which has the high bits at its index.

For example, if `address_high_bits = [0, 10, 15]`, then keys 0-9 have high bits equal to 0, keys 10-14 have high bits equal to 1, and keys 15-onwards have high bits equal to 2.

The high bits for a given `key` can be obtained by binary-searching `address_high_bits` to find the last element of `address_high_bits` which is less than or equal to `key`.

Note that because the maximum value for the high bits is $2^{16}$, `len(address_high_bits)` is at most $2^{16}$.

This representation is possible because keys are given out in order of address. When a new page is added, its `compressed_data` is appended to `data` and its key is one greater than the previous key that was given out. So `address` is len(`compressed_data`) <= 4096 greater than the address of `key - 1`.

Note that the specific example given earlier of `address_high_bits = [0, 10, 15]` is actually impossible. Each value in `address_high_bits` represents a concatenation of `compressed_data` which have size equal to $2^{26}$, which is at least $2^{26}/4096 = 2^{14}$ pages. So, each value in `address_high_bits` should be at least $2^{14}$ greater than the previous value.

As an optimization, the first value of `address_high_bits` is implicit instead of explicitly stored, because it is known to always be zero.

### `compressed_pages`
`compressed_pages` is very similar to `compressed_diffs`. At a high level, it is a key-value store mapping opaque keys- integers less than $2^{30}$ -to values- `CompressedPageItem`s.

A `CompressedPageItem` consists of `compressed_data`, an arbitrary length compressed array and `method`, a `u8` byte describing the compression method. The `method` is used to determine how to decompress `data` to yield the 4096-byte array which is the derivative page.

Similar to `compressed_diffs`, `compressed_pages` is implemented using three arrays. However, `packed_metadata` is an array of `u32`s instead of `u64`s.

`data` in `compressed_pages` functions equivalently to `data` in `compressed_diffs`.

`address`es in `compressed_pages` are broken into 18 high bits and 24 low bits (instead of 16 and 26 respectively for `compressed_diffs`).

Each `u32` element of `packed_metadata` can be broken into two parts:
- the 8 high bits are `method`
- the 24 low bits are the low bits of `address`

`address_high_bits` is equivalent to that of `compressed_diffs`, only that it is used to compute 18 high bits instead of 16.

### Serialization

`MemoryDiff` can be trivially serialized into a byte array and sent over the network or stored persistently on disk.

All integers in the serialized form use a big endian representation. We found there was no performance penalty to switching the integers from the native little endian to big endian, so we prefer the conventional big endian as network endian.

The result of `MemoryDiff::write` is to write the following to the stream:
- u32 n: `base_pages.len()`
- [u32; n] base_pages
- u32 dp: `compressed_diffs.packed_metadata.len()`
- u32 dh: `compressed_diffs.address_high_bits.len()`
- u64 dd: `compressed_diffs.data.len()`
- [u64; dp] compressed_diffs.packed_metadata
- [u32; dh] compressed_diffs.address_high_bits
- [u8; dd] compressed_diffs.data
- u32 pp: `compressed_pages.packed_metadata.len()`
- u32 ph: `compressed_pages.address_high_bits.len()`
- u64 pd: `compressed_pages.data.len()`
- [u32; pp] compressed_pages.packed_metadata
- [u32; ph] compressed_pages.address_high_bits
- [u8; pd] compressed_pages.data


## Compression Format

Incinerator uses a custom format to compress page-sized arrays (hereinafter referred to as pages) of data. The format is actually a collection of sub-formats, so an 8-bit integer `method` is used to describe the sub-format used to compress a given page. Compressing a page returns a byte array `data` of size at most 4096 and a u8 `method`. To correctly decompress the page, the same `data` and `method` must be provided to the decompress function.

Because pages are often actually XORs of two similar pages, we assume that many of the bytes in the page will be zero, so many of the submethods are designed with built-in bias to reduce compression size for pages with many zero bytes.

There are 5 core sub-formats: `NoCompression`, `BytePlacement`, `RunLength`, `ZeroLength`, and `PatternArray`. These core sub-formats can be composed into one of 84 total sub-formats. Incinerator chooses the sub-format which produces the smallest compressed form, preferring the simpler-to-decode format if two formats produce the same size output.

### `NoCompression`
`NoCompression` is very simple. It... doesn't do any compression.

`NoCompression` is important because allows us to make all other sub-formats fallible: other sub-formats are designed to return a failure on some edge-case inputs if encoding that input would require a compromise in compressed size to the general case. For this reason, other sub-formats also return failure if their compressed size would be larger than the size of the input, since they know `NoCompression` will beat them on compressed size.

`NoCompression` has key `0b00`

### `BytePlacement`
At a high level, `BytePlacement` specifies a set of indices into the array and a set of data to go at the aforementioned indices. `BytePlacement` works well compared to other sub-formats on inputs which have few nonzero data bytes which are scattered relatively uniformly throughout the input.

Because arrays can have arbitrary length indices can be arbitrary large. So, we split the array into chunks of size at-most 256 to ensure that indices can be represented with a single byte.
Each chunk has one byte of head and at most 510 ((256-1) * 2) bytes of payload. The `BytePlacement` compressed representation is the concatenation of all the chunks' heads followed by all the chunks' payloads.

The head of a chunk is `n`: the count of nonzero bytes in the chunk. If the chunk contains 256 nonzero bytes (ie. all the bytes are nonzero), then `BytePlacement` fails for this input. This does not hurt the compressed size in practice because if any chunk has no zero bytes, the overhead of `BytePlacement` for this chunk would make the total compressed size almost certainly worse than for other sub-formats.

The payload of a chunk contains `n` segments, where each segment has an index byte + a data byte. The index byte points to a position in the chunk and the data byte specifies what the data at the position should be. All bytes which are not pointed to by any index are given the value `0u8`.

`BytePlacement` has key `0b01`

### `RunLength`
`RunLength` is simply the [run-length encoding](https://en.wikipedia.org/wiki/Run-length_encoding) of the input buffer. `RunLength` works well compared to other sub-formats on inputs which contain bytes repeated many times consecutively.

The output of `RunLength` is a series of segments, each segment containing of a data byte + a count byte. A count byte of `n` specifies that the data byte is repeated `n + 1` times in the uncompressed buffer (it is 1-biased because a count of 0 is meaningless). If a byte is repeated more than 256 times in a row, it should be split into multiple segments; ie. it is permissible to have adjacent segments with the same data byte.

`RunLength` has key `0b10`

### `ZeroLength`
`ZeroLength` is a modifed form of run-length encoding, taking advantage of the fact that much of our data will likely be zero. `ZeroLength` works well compared to other sub-formats on inputs which contain lots of consecutive zero bytes.

The output of `ZeroLength` is a series of segments. Each segment contains a count `n` of zero bytes, a count `m` of data bytes, and `m` bytes of data. Each segment corresponds to a portion of the decompressed data which starts with `n` bytes of zeros, followed by an `m`-byte long data buffer which is equal to the one in the segment.

A sequence of longer than 255 zero bytes or longer than 255 nonzero bytes in the input buffer can be encoded as two segments, with a zero value for `m` or `n` respectively in the first segment.

As an optimization, we note that if `n = 1` in any segment, the segment can be combined with with the previous segment by concatenating the two data buffers and inserting a zero data byte in between. For example, the input buffer `[1, 2, 3, 0, 5, 6, 7]` could be encoded as `[[0; 3; 1, 2, 3]; [1; 3; 5, 6, 7]]`, which takes 10 bytes, or it could be encoded more optimally as `[[0; 7; 1, 2, 3, 0, 5, 6, 7]]`, which takes only 9 bytes. Caution must to be taken to ensure `n` and `m` remain than 256. Depending on the implementation, this optimization can be implemented very simply, see [98603a5](https://github.com/ProjectPhoenixVM/phoenix/commit/f9a0fce00fab8cef1bc3645fd3c4c97e4a1c9ae0#diff-6446fc43513a34426c336386ba85248b92579774d1ac78648e54a9d7c5b0e17fR210-R213).

`ZeroLength` has key `0b11`

### `PatternArray`
`PatternArray` is the most complex sub-format as it produces buffers which can be recompressed using other sub-formats.

The `PatternArray` sub-format is motivated by page-XORs which look like the following hexdump (.. is 0x00):
```
.. 20 6D B3 08 .. .. ..     .. 20 6D B3 08 .. .. ..
.. .. .. .. .. .. .. ..     .. 20 6D B3 08 .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. 40 7E F6 01 .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. .. .. .. .. .. ..
.. .. 20 A1 B4 .. .. ..     .. .. .. .. .. .. .. ..
.. .. .. .. .. .. .. ..     .. .. 20 A1 B4 .. .. ..
.. .. .. .. .. .. .. ..     .. .. 20 A1 B4 .. .. ..
.. .. 20 A1 B4 .. .. ..     .. .. .. .. .. .. .. ..
.. .. 20 A1 B4 .. .. ..     .. .. 20 A1 B4 .. .. ..
.. .. .. .. .. .. .. ..     .. .. 20 A1 B4 .. .. ..
.. .. 20 A1 B4 .. .. ..     .. .. .. .. .. .. .. ..
.. .. 20 A1 B4 .. .. ..     .. .. 20 A1 B4 .. .. ..
.. .. .. .. .. .. .. ..     .. .. 20 A1 B4 .. .. ..
```

We suspect this kind of pattern is caused by pages of memory storing pointers in both the base and derivative snapshot, but due to [ASLR](https://en.wikipedia.org/wiki/Address_space_layout_randomization) and other sources of randomness in memory allocation, the high bits of the pointers differ in the two pages. However they always differ by the same amount, so taking the XOR reveals the shared differences.

`PatternArray` treats the uncompressed array as a series of 8-byte "patterns". The compressed output then stores a "pattern array" containing only the unique patterns and a "data array" 1/8th the size of the uncompressed array. Each byte in the "data array" indexes the pattern array to specify which data the corresponding 8 bytes in the uncompressed array are.

Because each byte in the data array can only take 256 values, the maximum size of the pattern array is 256. Since we compress 4096-byte pages, it is possible that there are at most 4096/8 = 512 unique patterns, so `PatternArray` will sometimes fail.

Additionally, because the all-zero pattern is common, it is implicitly added as the zeroth value of the pattern array. So in practice only 255 nonzero patterns can be stored in the pattern array.

The Incinerator implementation stores patterns in the pattern array in sorted order, however this is not a requirement of the format and should not be relied on.

Notice that the data array is just a 512-length array of bytes. It can be further compressed. Incinerator applies another round of compression to the data array. Not only can it use any of the other four compression sub-formats, it can `PatternArray` compress the data array, producing a sub-pattern array and sub-data array of size 64. The sub-pattern array is small enough that applying `PatternArray` recursively does not yield significant results, so Incinerator only tries 1 level of recursive `PatternArray` compression.

The pattern array is also an array. It can also be recompressed. Applying `PatternArray` to the pattern array would never reduce its size because all 8-byte chunks in the pattern array are already unique (by definition). So Incinerator only tries the other four compression sub-formats.

The compressed data for `PatternArray` is stored as a byte representing the number of patterns (the implicit zero pattern is not included, so this value is at most 254), followed by the compressed pattern array, followed by the compressed data array.

`PatternArray` does not have a key; the `method` follows one of three different forms depending on whether 0, 1, or 2 levels of `PatternArray` are applied and depending on which sub-formats are used to compress the various sub-arrays.

### `method`
`method` is a byte describing exactly which composition of sub-formats were used to compress a given page.

If no levels of `PatternArray` are applied, then let the key used to compress the page be `0bXX``. The method is `0b00_000_0XX`

If one level of `PatternArray` is applied, let the key used to compress the pattern array be `0bXX`, and let the key used to compress the data array be `0bYY`. The method is `0b00_0YY_1XX`.

If two levels of `PatternArray` are applied, let the key used to compress the pattern array be `0bXX`, let the key used to compress the sub-pattern array be `0bYY`, and let the key used to compress the sub-data array be `0bZZ`. The method is `0bZZ_1YY_1XX`.


# Future work

There are only 84 sub-formats, meaning an alternate encoding scheme could use only 7 bits, freeing one additiona bit to store address_high_bits

All the lengths for the arrays in the serialized `MemoryDiff` could use fewer bits (ie. dd knows it has max size 2^30*2^12, why use 64 bits when 42 could do)

Allow up to 256 patterns in the pattern array if the zero pattern is never used
