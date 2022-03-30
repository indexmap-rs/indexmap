use crate::IndexMap;
use core::ops::{Index, IndexMut};

/// Indexable types can convert to and from `usize`.
pub trait Indexable: Sized + Copy + Ord + Send + Sync + TryFrom<usize> + TryInto<usize> {
    /// Creates an index from a `usize`; panics on failure.
    #[inline]
    #[track_caller]
    fn from_usize(i: usize) -> Self {
        match Self::try_from(i) {
            Ok(i) => i,
            Err(_) => panic!("invalid index!"),
        }
    }

    /// Converts the index to a `usize`; panics on failure.
    #[inline]
    #[track_caller]
    fn into_usize(self) -> usize {
        match self.try_into() {
            Ok(i) => i,
            Err(_) => panic!("invalid index!"),
        }
    }
}

impl Indexable for usize {}

macro_rules! impl_indexable {
    ($($ty:ident)*) => {$(
        impl Indexable for $ty {}

        impl<K, V, S> Index<$ty> for IndexMap<K, V, S, $ty> {
            type Output = V;

            fn index(&self, index: $ty) -> &V {
                self.get_index(index)
                    .expect("IndexMap: index out of bounds")
                    .1
            }
        }

        impl<K, V, S> IndexMut<$ty> for IndexMap<K, V, S, $ty> {
            fn index_mut(&mut self, index: $ty) -> &mut V {
                self.get_index_mut(index)
                    .expect("IndexMap: index out of bounds")
                    .1
            }
        }
    )*}
}

impl_indexable!(u8 u16 u32 u64 u128);
