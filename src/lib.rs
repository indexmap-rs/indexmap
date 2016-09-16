#![feature(sip_hash_13)] // must use for fair comparison
extern crate itertools;

mod macros;
mod util;

use itertools::free::{enumerate};

use std::hash::Hash;
use std::hash::SipHasher13;
use std::hash::Hasher;
use std::borrow::Borrow;

use std::cmp::max;
use std::fmt;
use std::mem::swap;

use util::second;

fn hash_elem<K: ?Sized + Hash>(k: &K) -> u64 {
    let mut h = SipHasher13::new();
    k.hash(&mut h);
    h.finish()
}

type PosType = usize;

macro_rules! debug {
    ($fmt:expr) => { };
    ($fmt:expr, $($t:tt)*) => { };
}

#[derive(Copy)]
struct Pos {
    index: PosType,
}

impl Clone for Pos {
    #[inline(always)]
    fn clone(&self) -> Self { *self }
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.pos() {
            Some(i) => write!(f, "Pos({})", i),
            None => write!(f, "Pos(None)"),
        }
    }
}

impl Pos {
    #[inline(always)]
    fn new(i: usize) -> Self { Pos { index: i as PosType } }
    #[inline(always)]
    fn none() -> Self { Pos { index: PosType::max_value() } }
    #[inline(always)]
    fn pos(&self) -> Option<usize> {
        if self.index == PosType::max_value() { None } else { Some(self.index as usize) }
    }
}

/// A hash map that preserves insertion order of the key-value pairs.
///
/// The key-value pairs have a consistent order that is determined by
/// the sequence of insertion and removal calls on the map. The order does
/// not depend on the keys of the map at all.
///
/// All iterators traverse the map in the same order.
#[derive(Clone)]
pub struct OrderedMap<K, V> {
    len: usize,
    mask: usize,
    indices: Vec<Pos>,
    entries: Vec<Entry<K, V>>,
}

#[derive(Copy, Clone, Debug)]
struct Entry<K, V> {
    hash: u64,
    key: K,
    value: V,
}

#[inline(always)]
fn desired_pos(mask: usize, hash: u64) -> usize {
    hash as usize & mask
}

/// The number of steps that `current` is forward of the desired position for hash
#[inline(always)]
fn probe_distance(mask: usize, hash: u64, current: usize) -> usize {
    current.wrapping_sub(desired_pos(mask, hash)) & mask
}

enum Inserted {
    Done,
    AlreadyExists,
    SwapWith {
        probe: usize,
        old_index: usize,
        dist: usize,
    }
}

impl<K, V> fmt::Debug for OrderedMap<K, V>
    where K: fmt::Debug + Hash + Eq,
          V: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(f.debug_map().entries(self.iter()).finish());
        try!(writeln!(f, ""));
        for (i, index) in enumerate(&self.indices) {
            try!(write!(f, "{}: {:?}", i, index));
            if let Some(pos) = index.pos() {
                let hash = self.entries[pos].hash;
                let key = &self.entries[pos].key;
                let desire = desired_pos(self.mask, hash);
                try!(writeln!(f, ", desired={}, probe_distance={}, key={:?}",
                              desire,
                              probe_distance(self.mask, hash, i),
                              key));
            }
            try!(writeln!(f, ""));
        }
        Ok(())
    }
}

fn usable_capacity(cap: usize) -> usize {
    cap - cap / 4
}

fn to_raw_capacity(n: usize) -> usize {
    n + n / 3
}

// this could not be captured in an efficient iterator
macro_rules! probe_loop {
    ($probe_var: ident < $len: expr, $body: expr) => {
        loop {
            if $probe_var < $len {
                $body
                $probe_var += 1;
            } else {
                $probe_var = 0;
            }
        }
    }
}

impl<K, V> OrderedMap<K, V>
    where K: Eq + Hash
{
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    pub fn with_capacity(n: usize) -> Self {
        let raw = to_raw_capacity(n);
        let power = if n == 0 { 0 } else { max(raw.next_power_of_two(), 8) };
        OrderedMap {
            len: 0,
            mask: power.wrapping_sub(1),
            indices: vec![Pos::none(); power],
            entries: Vec::with_capacity(n), // FIXME: compute adjusted n
        }
    }

    // `n` must be a power of two
    fn with_raw_capacity_no_entries(n: usize) -> Self {
        let power = n;
        debug_assert_eq!(n, n.next_power_of_two());
        OrderedMap {
            len: 0,
            mask: (power - 1),
            indices: vec![Pos::none(); power],
            entries: Vec::new(),
        }
    }

    pub fn len(&self) -> usize { self.len }

    #[inline(always)]
    fn raw_capacity(&self) -> usize {
        self.indices.len()
    }

    pub fn capacity(&self) -> usize {
        usable_capacity(self.raw_capacity())
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.len = 0;
        for pos in &mut self.indices {
            *pos = Pos::none();
        }
    }

    // First phase: Look for the preferred location for key.
    //
    // We will know if `key` is already in the map, before we need to insert it.
    // When we insert they key, it might be that we need to continue displacing
    // entries (robin hood hashing), in which case Inserted::SwapWith is returned
    fn insert_phase_1(&mut self, key: K, value: V) -> Inserted {
        let hash = hash_elem(&key);
        let mut probe = desired_pos(self.mask, hash);
        let mut dist = 0;
        debug_assert!(self.len() < self.raw_capacity());
        probe_loop!(probe < self.indices.len(), {
            if let Some(i) = self.indices[probe].pos() {
                // if existing element probed less than us, swap
                let their_dist = probe_distance(self.mask, self.entries[i].hash, probe);
                if their_dist < dist {
                    //   0    1       2       3
                    // [ None Some(0) Some(1) None ] // indices
                    // [ aaaa ]
                    // [ bbbb ]
                    //
                    // if the new entry at index 2 is better at #1, we do:
                    //
                    // let index = 2;
                    // entries.push(cccc);
                    //
                    // old_index = indices[1]; (Some(0))
                    // indices[1] = Some(2);
                    //
                    //
                    // insert key
                    let index = self.entries.len();
                    self.indices[probe] = Pos::new(index);
                    self.entries.push(Entry { hash: hash, key: key, value: value });
                    self.len += 1;
                    return Inserted::SwapWith {
                        probe: probe,
                        old_index: i,
                        dist: their_dist,
                    };
                } else if self.entries[i].hash == hash && self.entries[i].key == key {
                    return Inserted::AlreadyExists;
                }
            } else {
                // empty bucket, insert here
                let index = self.entries.len();
                self.indices[probe] = Pos::new(index);
                self.entries.push(Entry { hash: hash, key: key, value: value });
                self.len += 1;
                return Inserted::Done;
            }
            dist += 1;
        });
    }

    fn insert_phase_2(&mut self, mut probe: usize, mut old_index: usize, mut dist: usize) {
        probe_loop!(probe < self.indices.len(), {
            if let Some(i) = self.indices[probe].pos() {
                // if existing element probed less than us, swap
                let their_dist = probe_distance(self.mask, self.entries[i].hash, probe);
                if their_dist < dist {
                    self.indices[probe] = Pos::new(old_index);
                    old_index = i;
                    dist = their_dist;
                }
            } else {
                self.indices[probe] = Pos::new(old_index);
                break;
            }
            dist += 1;
        });
    }

    fn first_allocation(&mut self) {
        debug_assert_eq!(self.len(), 0);
        *self = OrderedMap::with_raw_capacity_no_entries(8);
    }

    #[inline(never)]
    fn double_capacity(&mut self) {
        debug_assert!(self.raw_capacity() == 0 || self.len() > 0);
        if self.raw_capacity() == 0 {
            return self.first_allocation();
        }

        // find first ideally placed element -- start of cluster
        let mut first_ideal = 0;
        for (i, index) in enumerate(&self.indices) {
            if let Some(pos) = index.pos() {
                if 0 == probe_distance(self.mask, self.entries[pos].hash, i) {
                    first_ideal = i;
                    break;
                }
            }
        }

        let mut old_self = OrderedMap::with_raw_capacity_no_entries(self.indices.len() * 2);
        swap(self, &mut old_self);
        for pos in &old_self.indices[first_ideal..] {
            if let Some(i) = pos.pos() {
                self.insert_hashed_ordered(i, &old_self.entries[i]);
            }
        }

        for pos in &old_self.indices[..first_ideal] {
            if let Some(i) = pos.pos() {
                self.insert_hashed_ordered(i, &old_self.entries[i]);
            }
        }
        self.entries = old_self.entries;
        debug_assert_eq!(self.len, old_self.len);
    }

    // bumps length;
    fn insert_hashed_ordered(&mut self, index: usize, entry: &Entry<K, V>) {
        // find first empty bucket and insert there
        let mut probe = desired_pos(self.mask, entry.hash);
        debug_assert!(self.len() < self.raw_capacity());
        probe_loop!(probe < self.indices.len(), {
            if let Some(_) = self.indices[probe].pos() {
                /* nothing */
            } else {
                // empty bucket, insert here
                self.indices[probe] = Pos::new(index);
                self.len += 1;
                return;
            }
        });
    }

    fn reserve_one(&mut self) {
        if self.len() == self.capacity() {
            self.double_capacity();
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.reserve_one();
        match self.insert_phase_1(key, value) {
            Inserted::AlreadyExists | Inserted::Done => { }
            Inserted::SwapWith { probe, old_index, dist } => {
                self.insert_phase_2(probe, old_index, dist);
            }
        }

    }

    /// Return an iterator over the keys of the map, in their order
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            iter: self.entries.iter()
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.entries.iter()
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.entries.iter_mut()
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair(key).map(second)
    }

    pub fn get_pair<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if let Some((_, found)) = self.find_position(key) {
            let entry = &self.entries[found];
            Some((&entry.key, &entry.value))
        } else {
            None
        }
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair_mut(key).map(second)
    }

    pub fn get_pair_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut K, &mut V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if let Some((_, found)) = self.find_position(key) {
            let entry = &mut self.entries[found];
            Some((&mut entry.key, &mut entry.value))
        } else {
            None
        }
    }

    /// Return probe (indices) and position (entries)
    fn find_position<Q: ?Sized>(&self, key: &Q) -> Option<(usize, usize)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if self.len() == 0 { return None; }
        let h = hash_elem(key);
        let mut probe = desired_pos(self.mask, h);
        let mut dist = 0;
        probe_loop!(probe < self.indices.len(), {
            if let Some(i) = self.indices[probe].pos() {
                let entry = &self.entries[i];
                if dist > probe_distance(self.mask, entry.hash, probe) {
                    // give up when probe distance is too long
                    return None;
                } else if entry.hash == h && *entry.key.borrow() == *key {
                    return Some((probe, i));
                }
            } else {
                return None;
            }
            dist += 1;
        });
    }

    /// Remove the key-value pair equivalent to `key` and return
    /// its value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// previously last element of the map and popping it off. This perturbs
    /// the postion of previously the last element.
    ///
    /// Return `None` if `key` is not in map.
    pub fn swap_remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.swap_remove_pair(key).map(second)
    }
    /// Remove the key-value pair equivalent to `key` and return it.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// previously last element of the map and popping it off. This perturbs
    /// the postion of previously the last element.
    ///
    /// Return `None` if `key` is not in map.
    pub fn swap_remove_pair<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        let (probe, found) = match self.find_position(key) {
            None => return None,
            Some(t) => t,
        };
        self.remove_found(probe, found)
    }

    fn remove_found(&mut self, probe: usize, found: usize) -> Option<(K, V)>
    {
        // index `probe` and entry `found` is to be removed
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        self.indices[probe] = Pos::none();
        let entry = self.entries.swap_remove(found);
        self.len -= 1;

        // correct index that points to the entry that had to swap places
        if let Some(entry) = self.entries.get(found) {
            // was not last element
            // examine new element in `found` and find it in indices
            let mut probe = desired_pos(self.mask, entry.hash);
            probe_loop!(probe < self.indices.len(), {
                if let Some(i) = self.indices[probe].pos() {
                    if i >= self.entries.len() {
                        // found it
                        self.indices[probe] = Pos::new(found);
                        break;
                    }
                }
            });
        }
        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        if self.len > 0 {
            let mut last_probe = probe;
            let mut probe = probe + 1;
            probe_loop!(probe < self.indices.len(), {
                if let Some(i) = self.indices[probe].pos() {
                    if probe_distance(self.mask, self.entries[i].hash, probe) > 0 {
                        self.indices[last_probe] = Pos::new(i);
                        self.indices[probe] = Pos::none();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
                last_probe = probe;
            });
        }

        Some((entry.key, entry.value))
    }

    /// Remove the last key-value pair
    pub fn pop(&mut self) -> Option<(K, V)> {
        let (probe, found) = match self.entries.last()
            .and_then(|e| self.find_position(&e.key))
        {
            None => return None,
            Some(t) => t,
        };
        debug_assert_eq!(found, self.entries.len() - 1);
        self.remove_found(probe, found)
    }
}

use std::slice::Iter as SliceIter;
use std::slice::IterMut as SliceIterMut;

pub struct Keys<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next().map(|ent| &ent.key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        self.iter.next_back().map(|ent| &ent.key)
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| (&e.key, &e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|e| (&e.key, &e.value))
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: SliceIterMut<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| (&e.key, &mut e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|e| (&e.key, &mut e.value))
    }
}

use std::ops::{Index, IndexMut};

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for OrderedMap<K, V>
    where K: Eq + Hash,
          K: Borrow<Q>,
          Q: Eq + Hash,
{
    type Output = V;
    fn index(&self, key: &'a Q) -> &V {
        if let Some(v) = self.get(key) {
            v
        } else {
            panic!("OrderedMap: key not found")
        }
    }
}

/// Mutable indexing allows changing / updating values of key-value
/// pairs that are already present.
///
/// You can **not** insert new pairs with index syntax, use `.insert()`.
impl<'a, K, V, Q: ?Sized> IndexMut<&'a Q> for OrderedMap<K, V>
    where K: Eq + Hash,
          K: Borrow<Q>,
          Q: Eq + Hash,
{
    fn index_mut(&mut self, key: &'a Q) -> &mut V {
        if let Some(v) = self.get_mut(key) {
            v
        } else {
            panic!("OrderedMap: key not found")
        }
    }
}

use std::iter::FromIterator;

impl<K, V> FromIterator<(K, V)> for OrderedMap<K, V>
    where K: Hash + Eq
{
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iterable: I) -> Self {
        let iter = iterable.into_iter();
        let (low, _) = iter.size_hint();
        let mut map = Self::with_capacity(low);
        for (k, v) in iter { map.insert(k, v); }
        map
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut map = OrderedMap::new();
        map.insert(1, ());
        map.insert(1, ());
        assert_eq!(map.len(), 1);
        assert!(map.get(&1).is_some());
    }

    #[test]
    fn insert() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5];
        let not_present = [1, 3, 6, 9, 10];
        let mut map = OrderedMap::with_capacity(insert.len());

        for (i, &elt) in insert.iter().enumerate() {
            assert_eq!(map.len(), i);
            map.insert(elt, elt);
            assert_eq!(map.len(), i + 1);
            assert_eq!(map.get(&elt), Some(&elt));
            assert_eq!(map[&elt], elt);
        }
        println!("{:?}", map);

        for &elt in &not_present {
            assert!(map.get(&elt).is_none());
        }
    }

    #[test]
    fn insert_2() {
        let mut map = OrderedMap::with_capacity(16);

        let mut keys = vec![];
        keys.extend(0..16);
        keys.extend(128..267);

        for &i in &keys {
            let old_map = map.clone();
            map.insert(i, ());
            for key in old_map.keys() {
                if !map.get(key).is_some() {
                    println!("old_map: {:?}", old_map);
                    println!("map: {:?}", map);
                    panic!("did not find {} in map", key);
                }
            }
        }

        for &i in &keys {
            assert!(map.get(&i).is_some(), "did not find {}", i);
        }
    }

    #[test]
    fn insert_order() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderedMap::new();

        for &elt in &insert {
            map.insert(elt, ());
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn grow() {
        let insert = [0, 4, 2, 12, 8, 7, 11];
        let not_present = [1, 3, 6, 9, 10];
        let mut map = OrderedMap::with_capacity(insert.len());


        for (i, &elt) in insert.iter().enumerate() {
            assert_eq!(map.len(), i);
            map.insert(elt, elt);
            assert_eq!(map.len(), i + 1);
            assert_eq!(map.get(&elt), Some(&elt));
            assert_eq!(map[&elt], elt);
        }

        println!("{:?}", map);
        map.double_capacity();
        println!("{:?}", map);

        for &elt in &not_present {
            assert!(map.get(&elt).is_none());
        }
    }

    #[test]
    fn remove() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderedMap::new();

        for &elt in &insert {
            map.insert(elt, elt);
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }

        let remove_fail = [99, 77];
        let remove = [4, 12, 8, 7];

        for &key in &remove_fail {
            assert!(map.swap_remove_pair(&key).is_none());
        }
        println!("{:?}", map);
        for &key in &remove {
        //println!("{:?}", map);
            assert_eq!(map.swap_remove_pair(&key), Some((key, key)));
        }
        println!("{:?}", map);

        for key in &insert {
            assert_eq!(map.get(key).is_some(), !remove.contains(key));
        }
        assert_eq!(map.len(), insert.len() - remove.len());
        assert_eq!(map.keys().count(), insert.len() - remove.len());
    }
}
