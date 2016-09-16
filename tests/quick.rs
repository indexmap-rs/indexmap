
extern crate orderedmap;
#[macro_use]
extern crate quickcheck;

use orderedmap::OrderedMap;

use std::collections::HashSet;
use std::hash::Hash;

fn set<'a, T: 'a, I>(iter: I) -> HashSet<T>
    where I: IntoIterator<Item=&'a T>,
    T: Copy + Hash + Eq
{
    iter.into_iter().cloned().collect()
}

quickcheck! {
    fn contains(insert: Vec<u32>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        insert.iter().all(|&key| map.get(&key).is_some())
    }
    fn insert_remove(insert: Vec<u8>, remove: Vec<u8>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        for &key in &remove {
            map.remove_pair(&key);
        }
        let elements = &set(&insert) - &set(&remove);
        map.len() == elements.len() && map.iter().count() == elements.len() &&
            elements.iter().all(|k| map.get(k).is_some())
    }
}
