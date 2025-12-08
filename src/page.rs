use std::{
    array::from_fn,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

pub const PAGE_SIZE: usize = 1024 * 4;
pub const PAGE_SIZE_U64: usize = PAGE_SIZE / size_of::<u64>();
pub type Page = [u8; PAGE_SIZE];

#[repr(align(64), C)]
#[derive(PartialEq, Eq, Clone, Copy, bytemuck::AnyBitPattern, bytemuck::NoUninit)]
pub struct AlignedPage(Page);
pub const ZERO_PAGE: AlignedPage = AlignedPage([0; _]);

impl Default for AlignedPage {
    fn default() -> Self {
        ZERO_PAGE
    }
}

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
            assert!(
                NUM_VECTORS <= u8::MAX as usize,
                "Byte diff per-element sum may overflow u8"
            );
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

pub fn page_xor(a: &AlignedPage, b: &AlignedPage) -> AlignedPage {
    AlignedPage(core::array::from_fn(|i| a.0[i] ^ b.0[i]))
}
