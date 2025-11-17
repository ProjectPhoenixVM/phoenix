use crate::{AlignedPage, ByteIndex, PAGE_SIZE};

pub type CompressionMethod = u8;
type Error = &'static str;
type Result<T> = core::result::Result<T, Error>;

fn write(output: &mut &mut [u8], data: &[u8]) -> Result<()> {
    let segment = output
        .split_off_mut(..data.len())
        .ok_or("Ran out of output buffer")?;
    segment.copy_from_slice(data);
    Ok(())
}

fn read<'a>(input: &mut &'a [u8], len: usize) -> Result<&'a [u8]> {
    input.split_off(..len).ok_or("Ran out of input buffer")
}

fn read_const<'a, const N: usize>(input: &mut &'a [u8]) -> Result<&'a [u8; N]> {
    read(input, N).map(|slice| slice.try_into().unwrap())
}

const fn usize_min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

fn dedup(slice: &mut [u64]) -> &mut [u64] {
    let mut read = 1;
    let mut write = 1;
    'outer: while read < slice.len() {
        assert!(write <= read);
        while slice[read] == slice[read - 1] {
            read += 1;
            if read == slice.len() {
                break 'outer;
            }
        }
        if write != read {
            slice[write] = slice[read];
        }
        write += 1;
        read += 1;
    }
    &mut slice[..write]
}

/// Stores a byte and its position in the output buffer
/// The output buffer is initialized to zero
/// The output buffer is split into 256-byte chunks so that all pointers can be u8
/// Counts of nonzero bytes per chunk are one-biased so all chunks must have at least one placement
///
/// [u8]: number of 1-biased placements in each 256-byte block of the range
/// [
///      u8: pointer
///      u8: data
/// ]
struct BytePlacement;

impl BytePlacement {
    #[inline]
    fn compress<'a>(xor: &[u8], full_output: &'a mut [u8]) -> Result<&'a [u8]> {
        const CHUNK_SIZE: usize = 256;
        let mut output = &mut full_output[..];
        let num_chunks = xor.len().div_ceil(CHUNK_SIZE);
        let mut head = output
            .split_off_mut(..num_chunks)
            .ok_or("Not enough output space")?;
        let (chunks, tail) = xor.as_chunks::<CHUNK_SIZE>();
        for chunk in chunks {
            let num_nonzero = chunk.into_iter().filter(|b| **b != 0).count();
            if num_nonzero == 0 {
                write(&mut head, &[0])?;
                write(&mut output, &[0, 0])?;
            } else {
                write(&mut head, &[(num_nonzero - 1) as u8])?;
                for (pos, &byte) in chunk.into_iter().enumerate() {
                    if byte != 0 {
                        write(&mut output, &[pos as u8, byte])?;
                    }
                }
            }
        }
        if !tail.is_empty() {
            let tail_num_nonzero = tail.into_iter().filter(|b| **b != 0).count();
            if tail_num_nonzero == 0 {
                write(&mut head, &[0])?;
                write(&mut output, &[0, 0])?;
            } else {
                write(&mut head, &[(tail_num_nonzero - 1) as u8])?;
                for (pos, &byte) in tail.iter().enumerate() {
                    if byte != 0 {
                        write(&mut output, &[pos as u8, byte])?;
                    }
                }
            }
        }
        let output_len = output.len();
        let out_len = full_output.len() - output_len;
        Ok(&full_output[..out_len])
    }

    #[inline]
    fn decompress(input: &mut &[u8], output: &mut [u8]) -> Result<()> {
        output.fill(0);
        const CHUNK_SIZE: usize = 256;
        let num_chunks = output.len().div_ceil(CHUNK_SIZE);
        let header = input.split_off(..num_chunks).ok_or("Not enough input")?;
        let (chunks, tail) = output.as_chunks_mut::<CHUNK_SIZE>();
        for (chunk, num_nonzero) in chunks.into_iter().zip(header.into_iter()) {
            let num_nonzero = *num_nonzero as usize + 1;
            if input.len() < num_nonzero * 2 {
                return Err("Input data is cut short");
            }
            for _ in 0..num_nonzero {
                let &[pos, data] = read_const(input)?;
                chunk[pos as usize] = data;
            }
        }
        if !tail.is_empty() {
            let num_nonzero = *header.last().unwrap() as usize + 1;
            if input.len() < num_nonzero * 2 {
                return Err("Input data is cut short");
            }
            for _ in 0..num_nonzero {
                let &[pos, data] = read_const(input)?;
                tail[pos as usize] = data;
            }
        }
        Ok(())
    }
}

/// Stores a byte and the number of times it should be copied
///
/// [
///      u8: data
///      u8: count
/// ]
struct RunLength;

impl RunLength {
    #[inline]
    fn compress<'a>(xor: &[u8], full_output: &'a mut [u8]) -> Result<&'a [u8]> {
        let mut output = &mut full_output[..];

        let mut last = xor[0];
        let mut count = 1u8;
        for byte in (&xor[1..]).into_iter().copied() {
            if byte == last {
                if count == 255 {
                    write(&mut output, &[byte, count])?;
                    count = 0;
                }
                count += 1;
                continue;
            }
            write(&mut output, &[last, count])?;
            last = byte;
            count = 1;
        }
        write(&mut output, &[last, count])?;
        let output_len = output.len();
        let out_len = full_output.len() - output_len;
        Ok(&full_output[..out_len])
    }

    #[inline]
    fn decompress(input: &mut &[u8], output: &mut [u8]) -> Result<()> {
        let mut output = &mut output[..];

        while let Ok(&[data, count]) = read_const(input) {
            let count = (count as usize).min(output.len());
            let buf = output
                .split_off_mut(..count)
                .ok_or("Ran out of output buffer")?;
            buf.fill(data);
            if output.len() == 0 {
                return Ok(());
            }
        }

        Err("Not enough input data to fill output buffer")
    }
}

/// Stores zero count followed by a buffer of data
///
/// [
///      u8: number of zeroes
///      u8: length of data
///      [u8]: data
/// ]
struct ZeroLength;

impl ZeroLength {
    #[inline]
    fn compress<'a>(xor: &[u8], full_output: &'a mut [u8]) -> Result<&'a [u8]> {
        let mut output = &mut full_output[..];
        let mut input = &xor[..];

        while input.len() > 0 {
            let num_zeros = input
                .iter()
                .position(|e| *e != 0)
                .unwrap_or(input.len())
                .min(u8::MAX as usize) as u8;
            input = &input[num_zeros as usize..];
            let num_data = input
                .windows(2)
                .position(|e| e == &[0, 0])
                .unwrap_or(input.len())
                .min(u8::MAX as usize) as u8;
            let (data, rem) = input.split_at(num_data as usize);
            input = rem;
            if input.len() == 0 && num_data == 0 {
                write(&mut output, &[num_zeros])?;
                break;
            }
            write(&mut output, &[num_zeros, num_data])?;
            write(&mut output, data)?;
        }
        let output_len = output.len();
        let out_len = full_output.len() - output_len;
        Ok(&full_output[..out_len])
    }

    #[inline]
    fn decompress(input: &mut &[u8], output: &mut [u8]) -> Result<()> {
        let mut output = &mut output[..];

        loop {
            let &[num_zeros] = read_const(input)?;
            let zeros = output
                .split_off_mut(..num_zeros as usize)
                .ok_or("Input decompressed exceeds output buffer")?;
            zeros.fill(0);
            if output.len() == 0 {
                return Ok(());
            }

            let &[data_len] = read_const(input)?;
            let data =
                read(input, data_len as usize).map_err(|_| "Final segment exceeds input buffer")?;
            write(&mut output, data)?;

            if output.len() == 0 {
                return Ok(());
            }
        }
    }
}

/// Breaks page into 64-byte patterns
/// Stores unique patterns in a pattern array
/// The 0th pattern is always [0; 8]
/// Stores an array of patterns for the whole page
///
/// [
///      u8: number of patterns (max 254)
///      [u64]: patterns
///      [u8; 512]: patterns to apply
/// ]
struct PatternArray<'a>(&'a [u8]);

impl<'a> PatternArray<'a> {
    const PATTERN_ARRAY_SIZE: usize = size_of::<u64>() * usize_min(Self::DATA_ARRAY_SIZE, 254);
    const DATA_ARRAY_SIZE: usize = PAGE_SIZE / size_of::<u64>();
    const MAX_SIZE: usize = 1 + Self::PATTERN_ARRAY_SIZE + Self::DATA_ARRAY_SIZE;

    fn patterns(&self) -> &'a [u8] {
        &self.0[1..][..self.patterns_size()]
    }

    fn data(&self) -> &'a [u8] {
        &self.0[1 + self.patterns_size()..]
    }

    fn patterns_size(&self) -> usize {
        let num_patterns = self.0[0];
        num_patterns as usize * size_of::<u64>()
    }
}

impl<'a> PatternArray<'a> {
    #[inline]
    fn compress(xor: &[u8], full_output: &'a mut [u8]) -> Result<Self> {
        assert!(xor.len() <= PAGE_SIZE);
        let (xor_chunks, rem) = xor.as_chunks::<8>();
        assert!(rem.is_empty());

        let mut output = &mut full_output[..];

        let mut data = [0u64; 512];
        let data_bytes = bytemuck::cast_slice_mut::<_, u8>(&mut data);
        data_bytes[..xor.len()].copy_from_slice(xor);
        let with_duplicates = &mut data[..xor_chunks.len()];

        with_duplicates.sort_unstable();
        let patterns = dedup(with_duplicates);

        let patterns_len = patterns.len();
        let mut patterns = &data[..patterns_len];
        if patterns[0] == 0 {
            patterns = &patterns[1..];
        }

        if patterns.len() > u8::MAX as usize - 1 {
            return Err("Too many patterns");
        }
        let num_patterns = patterns.len() as u8;
        write(&mut output, &[num_patterns])?;
        write(&mut output, bytemuck::cast_slice(&patterns))?;

        if output.len() < xor_chunks.len() {
            return Err("Not enough output space");
        }
        for (i, pattern) in xor_chunks
            .into_iter()
            .copied()
            .map(u64::from_ne_bytes)
            .enumerate()
        {
            if pattern == 0 {
                output[i] = 0
            } else {
                let index = patterns.binary_search(&pattern).unwrap();
                output[i] = index as u8 + 1;
            }
        }

        let output_len = output.len();
        let out_len = full_output.len() - output_len + xor_chunks.len();
        Ok(Self(&full_output[..out_len]))
    }

    #[inline]
    fn decompress(input: &mut &[u8], output: &mut [u8]) -> Result<()> {
        let (output_chunks, rem) = output.as_chunks_mut::<8>();
        assert_eq!(rem.len(), 0);

        let &[num_patterns] = read_const(input)?;
        let patterns = read(input, num_patterns as usize * 8)?;
        let (pattern_data, rem) = patterns.as_chunks::<8>();
        assert_eq!(rem.len(), 0);
        let mut patterns = [[0; 8]; 256];
        patterns[1..num_patterns as usize + 1].copy_from_slice(pattern_data);

        let data = read(input, output_chunks.len())?;
        for (byte, out) in data.into_iter().zip(output_chunks) {
            out.copy_from_slice(&patterns[*byte as usize]);
        }

        Ok(())
    }
}

/// Method:
/// 0b_00_000_0xx: page is compressed with method XX
/// 0b_00_0yy_1xx: page is compressed with pattern array
///                   pattern array patterns are compressed with method XX
///                   pattern array data is compressed with method YY
/// 0b_zz_1yy_1xx: page is compressed with superpattern array
///                   pattern array patterns are compressed with method XX
///                   superpattern array patterns are compressed with method YY
///                   pattern array data is compressed with method ZZ
#[derive(Debug, Clone, Copy)]
pub struct CompressHeader {
    pub method: CompressionMethod,
    pub len: ByteIndex,
}

impl CompressHeader {
    pub fn len(&self) -> usize {
        self.len as _
    }
}

const NO_COMPRESSION: u8 = 0b00;
const BYTE_PLACEMENT: u8 = 0b01;
const RUN_LENGTH: u8 = 0b10;
const ZERO_LENGTH: u8 = 0b11;

const PATTERN_ARRAY: u8 = 0b100;

fn compress_slice(buf: &[u8], output: &mut [u8]) -> CompressHeader {
    assert!(buf.len() <= PAGE_SIZE);

    let mut buffer = [0; PAGE_SIZE * 3];
    let mut buffer = &mut buffer[..];
    let bp_output = buffer.split_off_mut(..buf.len()).unwrap();
    let rle_output = buffer.split_off_mut(..buf.len()).unwrap();
    let zle_output = buffer.split_off_mut(..buf.len()).unwrap();

    let mut best_result = CompressHeader {
        method: NO_COMPRESSION,
        len: buf.len() as _,
    };
    let mut best_buf = buf;

    let bp_res = BytePlacement::compress(buf, bp_output);
    if let Ok(slice) = bp_res
        && slice.len() < best_result.len as usize
    {
        best_result = CompressHeader {
            method: BYTE_PLACEMENT,
            len: slice.len() as _,
        };
        best_buf = slice;
    }

    let rle_res = RunLength::compress(buf, rle_output);
    if let Ok(slice) = rle_res
        && slice.len() < best_result.len as usize
    {
        best_result = CompressHeader {
            method: RUN_LENGTH,
            len: slice.len() as _,
        };
        best_buf = slice;
    }

    let zle_res = ZeroLength::compress(buf, zle_output);
    if let Ok(slice) = zle_res
        && slice.len() < best_result.len as usize
    {
        best_result = CompressHeader {
            method: ZERO_LENGTH,
            len: slice.len() as _,
        };
        best_buf = slice;
    }

    let output = &mut output[..best_buf.len()];
    output.copy_from_slice(best_buf);

    best_result
}

pub fn compress_page(buf: &AlignedPage, output: &mut [u8]) -> CompressHeader {
    compress_inner::<true>(&buf.0, output)
}

fn compress_inner<const ALLOW_SUPERPATTERN: bool>(buf: &[u8], output: &mut [u8]) -> CompressHeader {
    let mut buffer = [0; PAGE_SIZE * 2];
    let mut buffer = &mut buffer[..];
    let slice_output = buffer.split_off_mut(..buf.len()).unwrap();
    let pattern_array_output = buffer.split_off_mut(..buf.len()).unwrap();
    assert_eq!(slice_output.len(), buf.len());
    assert_eq!(pattern_array_output.len(), buf.len());

    let slice_result = compress_slice(buf, slice_output);

    let Ok(pattern_array_output) = PatternArray::compress(buf, pattern_array_output) else {
        output[..slice_result.len()].copy_from_slice(&slice_output[..slice_result.len()]);
        return slice_result;
    };

    let mut patterns_buffer = [0; PatternArray::PATTERN_ARRAY_SIZE];
    let patterns_buffer = &mut patterns_buffer[..pattern_array_output.patterns().len()];
    let patterns_compressed = compress_slice(pattern_array_output.patterns(), patterns_buffer);

    let mut data_buffer = [0; PatternArray::DATA_ARRAY_SIZE];
    let data_buffer = &mut data_buffer[..pattern_array_output.data().len()];
    let data_compressed = if ALLOW_SUPERPATTERN {
        compress_inner::<false>(pattern_array_output.data(), data_buffer)
    } else {
        compress_slice(pattern_array_output.data(), data_buffer)
    };

    let pattern_array_result = CompressHeader {
        method: data_compressed.method << 3 | PATTERN_ARRAY | patterns_compressed.method,
        len: 1 + patterns_compressed.len + data_compressed.len,
    };

    if slice_result.len <= pattern_array_result.len {
        let len = slice_result.len();
        output[..len].copy_from_slice(&slice_output[..len]);
        slice_result
    } else {
        let patterns_len = patterns_compressed.len();
        let data_len = data_compressed.len();
        output[0] = pattern_array_output.0[0];
        output[1..][..patterns_len].copy_from_slice(&patterns_buffer[..patterns_len]);
        output[1 + patterns_len..][..data_len].copy_from_slice(&data_buffer[..data_len]);
        pattern_array_result
    }
}

pub fn decompress_page(
    method: CompressionMethod,
    mut input: &[u8],
    output: &mut AlignedPage,
) -> Result<()> {
    decompress_inner(method, &mut input, &mut output.0)
}

fn decompress_inner(method: CompressionMethod, input: &mut &[u8], output: &mut [u8]) -> Result<()> {
    match method {
        NO_COMPRESSION => {
            let data = read(input, output.len())?;
            output.copy_from_slice(data);
            Ok(())
        }
        BYTE_PLACEMENT => BytePlacement::decompress(input, output),
        RUN_LENGTH => RunLength::decompress(input, output),
        ZERO_LENGTH => ZeroLength::decompress(input, output),
        _ => {
            assert!(method & PATTERN_ARRAY != 0);
            let mut intermediate = [0; PatternArray::MAX_SIZE];

            let &[num_patterns] = read_const(input)?;
            intermediate[0] = num_patterns;

            let patterns_len = num_patterns as usize * size_of::<u64>();
            let patterns = &mut intermediate[1..][..patterns_len];
            let patterns_method = method & 0b11;
            decompress_inner(patterns_method, input, patterns)?;

            let data_len = output.len() / size_of::<u64>();
            let data = &mut intermediate[1 + patterns_len..][..data_len];
            let data_method = method >> 3;
            decompress_inner(data_method, input, data)?;

            PatternArray::decompress(&mut &intermediate[..], output)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::array::from_fn;

    use super::dedup;

    #[test]
    fn test_dedup_simple() {
        let mut slice = [0, 0, 1, 2, 2, 3, 4, 4, 5, 5, 5, 5, 6, 7, 8, 8, 9];
        let deduped = dedup(&mut slice);
        assert_eq!(deduped, from_fn::<_, 10, _>(|i| i as u64));
    }

    #[test]
    fn test_dedup_single() {
        let mut slice = [0, 0, 0, 0, 0];
        let deduped = dedup(&mut slice);
        assert_eq!(deduped, [0]);
    }

    #[test]
    fn test_dedup_unique() {
        let original = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut slice = original;
        let deduped = dedup(&mut slice);
        assert_eq!(deduped, original);
    }

    #[test]
    fn test_dedup_small() {
        let mut slice = [0];
        let deduped = dedup(&mut slice);
        assert_eq!(deduped, [0]);
    }

    #[test]
    fn test_dedup_final_repeated() {
        let mut slice = [0, 1, 1, 2, 3, 3, 3];
        let deduped = dedup(&mut slice);
        assert_eq!(deduped, [0, 1, 2, 3]);
    }
}
