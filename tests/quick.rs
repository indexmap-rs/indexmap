
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
use std::iter::FromIterator;
use std::hash::Hash;
use std::fmt::Debug;
use std::ops::Deref;
use std::cmp::min;

use ordermap::Entry as OEntry;
use std::collections::hash_map::Entry as HEntry;


fn set<'a, T: 'a, I>(iter: I) -> HashSet<T>
    where I: IntoIterator<Item=&'a T>,
    T: Copy + Hash + Eq
{
    iter.into_iter().cloned().collect()
}

fn ordermap<'a, T: 'a, I>(iter: I) -> OrderMap<T, ()>
    where I: IntoIterator<Item=&'a T>,
    T: Copy + Hash + Eq
{
    OrderMap::from_iter(iter.into_iter().cloned().map(|k| (k, ())))
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

    fn with_cap(cap: usize) -> bool {
        let map: OrderMap<u8, u8> = OrderMap::with_capacity(cap);
        println!("wish: {}, got: {} (diff: {})", cap, map.capacity(), map.capacity() as isize - cap as isize);
        map.capacity() >= cap
    }

}

use Op::*;
#[derive(Copy, Clone, Debug)]
enum Op<K, V> {
    Add(K, V),
    Remove(K),
    AddEntry(K, V),
    RemoveEntry(K),
}

impl<K, V> Arbitrary for Op<K, V>
    where K: Arbitrary,
          V: Arbitrary,
{
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match g.gen::<u32>() % 4 {
            0 => Add(K::arbitrary(g), V::arbitrary(g)),
            1 => AddEntry(K::arbitrary(g), V::arbitrary(g)),
            2 => Remove(K::arbitrary(g)),
            _ => RemoveEntry(K::arbitrary(g)),
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
            AddEntry(ref k, ref v) => {
                a.entry(k.clone()).or_insert(v.clone());
                b.entry(k.clone()).or_insert(v.clone());
            }
            Remove(ref k) => {
                a.swap_remove(k);
                b.remove(k);
            }
            RemoveEntry(ref k) => {
                match a.entry(k.clone()) {
                    OEntry::Occupied(ent) => { ent.remove_entry(); },
                    _ => { }
                }
                match b.entry(k.clone()) {
                    HEntry::Occupied(ent) => { ent.remove_entry(); },
                    _ => { }
                }
            }
        }
        //println!("{:?}", a);
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
    for key in a.keys() {
        assert_eq!(a[key], b[key]);
    }
    true
}

quickcheck! {
    fn operations_i8(ops: Large<Vec<Op<i8, i8>>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        assert_maps_equivalent(&map, &reference)
    }

    fn operations_string(ops: Vec<Op<Alpha, i8>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        assert_maps_equivalent(&map, &reference)
    }

    fn keys_values(ops: Large<Vec<Op<i8, i8>>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        let mut visit = OrderMap::new();
        for (k, v) in map.keys().zip(map.values()) {
            assert_eq!(&map[k], v);
            assert!(!visit.contains_key(k));
            visit.insert(*k, *v);
        }
        assert_eq!(visit.len(), reference.len());
        true
    }

    fn keys_values_mut(ops: Large<Vec<Op<i8, i8>>>) -> bool {
        let mut map = OrderMap::new();
        let mut reference = HashMap::new();
        do_ops(&ops, &mut map, &mut reference);
        let mut visit = OrderMap::new();
        let keys = Vec::from_iter(map.keys().cloned());
        for (k, v) in keys.iter().zip(map.values_mut()) {
            assert_eq!(&reference[k], v);
            assert!(!visit.contains_key(k));
            visit.insert(*k, *v);
        }
        assert_eq!(visit.len(), reference.len());
        true
    }

    fn retain(keys: Large<Vec<i8>>, remove: Large<Vec<i8>>) -> bool {
        let mut map = ordermap(keys.iter());
        let remove_map = ordermap(remove.iter());
        let keys_s = set(keys.iter());
        let remove_s = set(remove.iter());
        let answer = &keys_s - &remove_s;
        map.retain(|k, _| !remove_map.contains_key(k));
        assert_eq!(map.len(), answer.len());
        for key in &answer {
            assert!(map.contains_key(key));
        }
        true

    }

    // Check that retain visits each key exactly once
    fn retain_visit(keys: Large<Vec<i8>>, remove: Large<Vec<i8>>) -> bool {
        let mut map = ordermap(keys.iter());
        let initial_map = map.clone();
        let mut visit = OrderMap::with_capacity(map.len());
        let remove_map = ordermap(remove.iter());
        map.retain(|k, _| {
            *visit.entry(*k).or_insert(0) += 1;
            !remove_map.contains_key(k)
        });

        assert_eq!(visit.len(), initial_map.len());
        assert!(visit.iter().all(|(_, v)| *v == 1));
        true
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Alpha(String);

impl Deref for Alpha {
    type Target = String;
    fn deref(&self) -> &String { &self.0 }
}

const ALPHABET: &'static [u8] = b"abcdefghijklmnopqrstuvwxyz";

impl Arbitrary for Alpha {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let len = g.next_u32() % g.size() as u32;
        let len = min(len, 16);
        Alpha((0..len).map(|_| {
            ALPHABET[g.next_u32() as usize % ALPHABET.len()] as char
        }).collect())
    }

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new((**self).shrink().map(Alpha))
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
