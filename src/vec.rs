//! Types for arrays of nibbles.
use std::{slice as stdslice, mem};
use base::{u4lo, u4};
use pair::u4x2;
use slice::{self, NibSliceAligned, NibSliceAlignedMut, NibSliceFull, NibSliceNoR};
use common::{get_nib, set_nib, shift_left, shift_right};
use quickcheck::{Arbitrary, Gen};

/// A `Vec` of nibbles.
#[derive(Clone)]
pub struct NibVec  {
    inner: Vec<u4x2>,
    has_right_lo: bool,
}
impl NibVec {
    /// Creates an empty `ArrayVec`.
    pub fn new() -> Self {
        NibVec { inner: Vec::new(), has_right_lo: true }
    }

    /// Creates a vector from a vector of pairs.
    pub fn from_pair_vec(inner: Vec<u4x2>) -> Self {
        NibVec { inner, has_right_lo: true }
    }

    /// Creates a vector from a vector of bytes.
    pub fn from_byte_vec(inner: Vec<u8>) -> Self {
        Self::from_pair_vec(unsafe { mem::transmute(inner) })
    }

    pub fn to_byte_vec(&self) -> Vec<u8> {
        unsafe { mem::transmute(self.inner.clone()) }
    }

    /// Number of nibbles in the vector.
    pub fn len(&self) -> usize {
        (self.inner.len() << 1).saturating_sub(!self.has_right_lo as usize)
    }

    /// Whether the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// How many nibbles can be stored in the vector.
    pub fn capacity(&self) -> usize {
        self.inner.capacity() << 1
    }

    /// Pushes a nibble onto the vector.
    ///
    /// # Panics
    ///
    /// Panics if the vector is full.
    pub fn push<T: u4>(&mut self, nib: T) {
        if self.has_right_lo {
            self.inner.push(u4x2::from_hi(nib.to_u4hi()));
        } else {
            let i = self.inner.len() - 1;
            self.inner[i].set_lo(nib);
        }
        self.has_right_lo = !self.has_right_lo;
    }

    /// Inserts a nibble into the vector at the given index.
    pub fn insert<T: u4>(&mut self, index: usize, nib: T) {
        if self.has_right_lo {
            self.push(u4lo::from_lo(0));
        }
        shift_right(self.inner.as_mut_slice(), index);
        set_nib(self.inner.as_mut_slice(), index, nib);
    }

    fn discard_at(&mut self, index: usize) {
        shift_left(self.inner.as_mut_slice(), index);
        self.has_right_lo = !self.has_right_lo;
        if self.has_right_lo {
            self.inner.pop();
        }
    }

    /// Removes a nibble from the vector at the given index, converting it to a high-order nibble.
    pub fn remove<T: u4>(&mut self, index: usize) -> T {
        let ret = get_nib(self.inner.as_slice(), index);
        self.discard_at(index);
        ret
    }

    /// Removes a nibble from the vector, converting it to a high-order nibble.
    pub fn pop<T: u4>(&mut self) -> Option<T> {
        self.has_right_lo = !self.has_right_lo;
        if self.has_right_lo {
            Some(T::from_lo(self.inner[self.inner.len() - 1].lo().to_lo()))
        } else {
            self.inner.pop().map(|pair| T::from_hi(pair.hi().to_hi()))
        }
    }

    /// Clears the vector, removing all nibbles.
    pub fn clear(&mut self) {
        self.inner.clear();
        self.has_right_lo = true;
    }

    /// Intreprets this array as a slice.
    pub fn as_slice(&self) -> NibSliceAligned {
        if self.has_right_lo {
            NibSliceAligned::Even(unsafe { &*(&self.inner[..] as *const [u4x2] as *const NibSliceFull) })
        } else {
            NibSliceAligned::Odd(unsafe { &*(&self.inner[..] as *const [u4x2] as *const NibSliceNoR) })
        }
    }

    /// Intreprets this array as a mutable slice.
    pub fn as_mut_slice(&mut self) -> NibSliceAlignedMut {
        if self.has_right_lo {
            NibSliceAlignedMut::Even(unsafe { &mut *(&mut self.inner[..] as *mut [u4x2] as *mut NibSliceFull) })
        } else {
            NibSliceAlignedMut::Odd(unsafe { &mut *(&mut self.inner[..] as *mut [u4x2] as *mut NibSliceNoR) })
        }
    }
}
impl Default for NibVec {
    fn default() -> Self {
        NibVec::new()
    }
}
impl slice::private::Sealed for NibVec {
    #[inline(always)]
    fn has_left_hi(&self) -> bool { true }
    #[inline(always)]
    fn has_right_lo(&self) -> bool { self.as_slice().has_right_lo() }
    #[inline(always)]
    fn iter(&self) -> stdslice::Iter<u4x2> { self.inner.iter() }
}
impl slice::private::SealedMut for NibVec {
    #[inline(always)]
    fn iter_mut(&mut self) -> stdslice::IterMut<u4x2> { self.inner.iter_mut() }
}
impl slice::NibSliceExt for NibVec {}
impl slice::NibSliceMutExt for NibVec {}

unsafe impl Send for NibVec {}
impl Arbitrary for NibVec {
    fn arbitrary<G: Gen>(g: &mut G) -> NibVec {
        let size = { let s = g.size(); g.gen_range(0, s) };
        let mut ret = NibVec::new();
        for _ in 0..size {
            ret.push(u4lo::from_lo(u8::arbitrary(g)));
        }
        ret
    }
    // fn shrink(&self) -> Box<Iterator<Item=NibVec>> {
    //     Box::new()
    // }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_str_works() {
        let result = NibVec::from_str("112").unwrap();
        let mut expected = NibVec::new();
        expected.push(u4lo::from_lo(1));
        expected.push(u4lo::from_lo(1));
        expected.push(u4lo::from_lo(2));
        assert_eq!(result, expected);
    }

    quickcheck! {
        fn nibble_add_len(n: u16) -> bool {
            let mut nib = NibVec::new();
            for i in 0..n {
                nib.push(u4lo::from_lo(i as u8));
            }
            nib.len() == (n as usize)
        }

        /*
        fn byte_vec_round_trip(nib_vec: NibVec) -> bool {
            let byte_vec = nib_vec.to_byte_vec();
            let nib_vec_2 = NibVec::from_byte_vec(byte_vec);
            nib_vec == nib_vec_2
        }
        */

        fn byte_vec_round_trip(byte_vec: Vec<u8>) -> bool {
            let byte_vec_copy = byte_vec.clone();
            let nib_vec = NibVec::from_byte_vec(byte_vec);
            let byte_vec_2 = nib_vec.to_byte_vec();
            byte_vec_copy == byte_vec_2
        }
    }
}
