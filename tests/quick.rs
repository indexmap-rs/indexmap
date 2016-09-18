
extern crate ordermap;
extern crate itertools;
#[macro_use]
extern crate quickcheck;

use ordermap::OrderMap;
use itertools::Itertools;

use quickcheck::Arbitrary;
use quickcheck::Gen;

use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;
use std::ops::Deref;

fn set<'a, T: 'a, I>(iter: I) -> HashSet<T>
    where I: IntoIterator<Item=&'a T>,
    T: Copy + Hash + Eq
{
    iter.into_iter().cloned().collect()
}

quickcheck! {
    fn contains(insert: Vec<u32>) -> bool {
        let mut map = OrderMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        insert.iter().all(|&key| map.get(&key).is_some())
    }

    fn contains_not(insert: Vec<u8>, not: Vec<u8>) -> bool {
        let mut map = OrderMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        let nots = &set(&not) - &set(&insert);
        nots.iter().all(|&key| map.get(&key).is_none())
    }

    fn insert_remove(insert: Vec<u8>, remove: Vec<u8>) -> bool {
        let mut map = OrderMap::new();
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
        let mut map = OrderMap::new();
        for &key in &insert {
            map.insert(key, ());
        }
        itertools::assert_equal(insert.iter().unique(), map.keys());
        true
    }

    fn pop(insert: Vec<u8>) -> bool {
        let mut map = OrderMap::new();
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

    fn with_cap(cap: u16) -> bool {
        let cap = cap as usize;
        let mut map = OrderMap::with_capacity(cap);
        map.insert(1, 1);
        println!("wish: {}, got: {} (diff: {})", cap, map.capacity(), map.capacity() as isize - cap as isize);
        map.capacity() >= cap
    }

}

use Op::*;
#[derive(Copy, Clone, Debug)]
enum Op<K, V> {
    Add(K, V),
    Remove(K),
}

impl<K, V> Arbitrary for Op<K, V>
    where K: Arbitrary,
          V: Arbitrary,
{
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        if g.gen() {
            Add(K::arbitrary(g), V::arbitrary(g))
        } else {
            Remove(K::arbitrary(g))
        }
    }
}

fn do_ops<K, V>(ops: &[Op<K, V>], a: &mut OrderMap<K, V>, b: &mut HashMap<K, V>)
    where K: Hash + Eq + Clone,
          V: Clone,
{
    for op in ops {
        match *op {
            Add(ref k, ref v) => {
                a.insert(k.clone(), v.clone());
                b.insert(k.clone(), v.clone());
            }
            Remove(ref k) => {
                a.swap_remove(k);
                b.remove(k);
            }
        }
    }
}

fn assert_maps_equivalent<K, V>(a: &OrderMap<K, V>, b: &HashMap<K, V>) -> bool
    where K: Hash + Eq + Debug,
          V: Eq + Debug,
{
    assert_eq!(a.len(), b.len());
    assert_eq!(a.iter().next().is_some(), b.iter().next().is_some());
    for key in a.keys() {
        assert!(b.contains_key(key), "b does not contain {:?}", key);
    }
    for key in b.keys() {
        assert!(a.get(key).is_some(), "a does not contain {:?}", key);
    }
    true
}

quickcheck! {
    fn operations_i8(ops: Large<Vec<Op<i8, String>>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        assert_maps_equivalent(&map, &reference)
    }

    fn operations_string(ops: Large<Vec<Op<String, String>>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        assert_maps_equivalent(&map, &reference)
    }
}

/// quickcheck Arbitrary adaptor -- make a larger vec
#[derive(Clone, Debug)]
struct Large<T>(T);

impl<T> Deref for Large<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}

impl<T> Arbitrary for Large<Vec<T>>
    where T: Arbitrary
{
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let len = g.next_u32() % (g.size() * 10) as u32;
        Large((0..len).map(|_| T::arbitrary(g)).collect())
    }

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new((**self).shrink().map(Large))
    }
}
