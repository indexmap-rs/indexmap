#![no_std]

use core::hash::BuildHasherDefault;
use indexmap::IndexMap;
use indexmap::IndexSet;
use twox_hash::XxHash64;
type Map<K, V> = IndexMap<K, V, BuildHasherDefault<XxHash64>>;
type Set<T> = IndexSet<T, BuildHasherDefault<XxHash64>>;

use core::iter::FromIterator;

pub fn test_compile() {
    let mut map = Map::default();
    map.insert(1, 1);
    map.insert(2, 4);
    for (_, _) in map.iter() {}

    let _map2 = Map::from_iter(Some((1, 1)));

    let mut set = Set::default();
    set.insert("a");
}
