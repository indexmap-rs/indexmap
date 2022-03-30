use fxhash::FxBuildHasher;
use indexmap::{IndexMap, IndexSet, Indexable};
use std::ops::{Index, IndexMut};

fn main() {
    let map: FancyMap<i32, i32> = (-10..=10).map(|i| (i, i * i)).collect();
    let set: FancySet<i32> = map.values().cloned().collect();

    println!("map to squares: {:?}", map);
    assert_eq!(map[&-10], map[&10]); // index by key
    assert_eq!(map[FancyIndex(0)], map[FancyIndex(20)]); // index by position

    println!("unique squares: {:?}", set);
    assert_eq!(set[FancyIndex(0)], 100); // index by position
    assert_eq!(set[FancyIndex(10)], 0); // index by position
}

/// A custom index newtype ensures it can't be confused with indexes for
/// unrelated containers. This one is also smaller to reduce map memory,
/// which also reduces the maximum capacity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FancyIndex(u16);

pub type FancyMap<K, V> = IndexMap<K, V, FxBuildHasher, FancyIndex>;
pub type FancySet<T> = IndexSet<T, FxBuildHasher, FancyIndex>;

impl Indexable for FancyIndex {}

impl TryFrom<usize> for FancyIndex {
    type Error = <u16 as TryFrom<usize>>::Error;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Ok(FancyIndex(u16::try_from(value)?))
    }
}

impl From<FancyIndex> for usize {
    fn from(i: FancyIndex) -> usize {
        i.0.into()
    }
}

// Unfortunately, `Index` and `IndexMut for IndexMap` are not automatically implemented for all
// `Idx: Indexable`, because the compiler considers `Index<Idx>` could potentially overlap with
// `Index<&Q>` for keys, since references are fundamental. Therefore, we have to implement indexing
// with `FancyIndex` ourselves. `IndexSet` does already implement all `Index<Idx>` though.

impl<K, V> Index<FancyIndex> for FancyMap<K, V> {
    type Output = V;

    fn index(&self, index: FancyIndex) -> &V {
        let (_key, value) = self
            .get_index(index)
            .expect("IndexMap: index out of bounds");
        value
    }
}

impl<K, V> IndexMut<FancyIndex> for FancyMap<K, V> {
    fn index_mut(&mut self, index: FancyIndex) -> &mut V {
        let (_key, value) = self
            .get_index_mut(index)
            .expect("IndexMap: index out of bounds");
        value
    }
}
