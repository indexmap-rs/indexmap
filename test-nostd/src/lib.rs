#![no_std]

extern crate indexmap;
extern crate ahash;

use indexmap::IndexMap;
use indexmap::IndexSet;
type Map<K, V> = IndexMap<K, V, ahash::ABuildHasher>;
type Set<T> = IndexSet<T, ahash::ABuildHasher>;

use core::iter::FromIterator;

pub fn test_compile() {
    let mut map = Map::default();
    map.insert(1, 1);
    map.insert(2, 4);
    for (_, _) in map.iter() { }

    let _map2 = Map::from_iter(Some((1, 1)));

    let mut set = Set::default();
    set.insert("a");
}
