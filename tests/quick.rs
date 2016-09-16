
extern crate orderedmap;
extern crate itertools;
#[macro_use]
extern crate quickcheck;

use orderedmap::OrderedMap;
use itertools::Itertools;

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

    fn contains_not(insert: Vec<u8>, not: Vec<u8>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        let nots = &set(&not) - &set(&insert);
        nots.iter().all(|&key| map.get(&key).is_none())
    }

    fn insert_remove(insert: Vec<u8>, remove: Vec<u8>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        for &key in &remove {
            map.swap_remove_pair(&key);
        }
        let elements = &set(&insert) - &set(&remove);
        map.len() == elements.len() && map.iter().count() == elements.len() &&
            elements.iter().all(|k| map.get(k).is_some())
    }

    fn insertion_order(insert: Vec<u32>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        itertools::assert_equal(insert.iter().unique(), map.keys());
        true
    }

    fn pop(insert: Vec<u8>) -> bool {
        let mut map = OrderedMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        let mut pops = Vec::new();
        while let Some((key, _v)) = map.pop() {
            pops.push(key);
        }
        pops.reverse();

        itertools::assert_equal(insert.iter().unique(), &pops);
        true
    }

}
