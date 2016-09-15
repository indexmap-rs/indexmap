extern crate itertools;

mod macros;

use itertools::free::{enumerate};

use std::hash::Hash;
use std::hash::SipHasher;
use std::hash::Hasher;
use std::borrow::Borrow;

use std::cmp::max;
use std::fmt;

fn hash_elem<K: ?Sized + Hash>(k: &K) -> u64 {
    let mut h = SipHasher::new();
    k.hash(&mut h);
    h.finish()
}

type PosType = usize;

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

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for OrderedMap<K, V>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "len={}", self.len));
        try!(writeln!(f, "indices={:?}", self.indices));
        for (i, index) in enumerate(&self.indices) {
            try!(write!(f, "{}: {:?}", i, index));
            if let Some(pos) = index.pos() {
                let hash = self.entries[pos].hash;
                let key = &self.entries[pos].key;
                let desire = desired_pos(self.mask, hash);
                try!(writeln!(f, ", desired_pos={}, probe_distance={}, key={:?}",
                              desire,
                              probe_distance(self.mask, hash, i),
                              key));
            }
            try!(writeln!(f, ""));
        }
        try!(writeln!(f, "entries={:?}", self.entries));
        Ok(())
    }
}

impl<K, V> OrderedMap<K, V>
    where K: Eq + Hash
{
    pub fn new() -> Self { Self::with_capacity(0) }

    pub fn with_capacity(n: usize) -> Self {
        let power = max(n.next_power_of_two(), 8);
        OrderedMap {
            len: 0,
            mask: (power - 1),
            indices: vec![Pos::none(); power],
            entries: Vec::with_capacity(n),
        }
    }

    pub fn len(&self) -> usize { self.len }
    pub fn capacity(&self) -> usize { self.indices.len() }

    // First phase: Look for the preferred location for key.
    //
    // We will know if `key` is already in the map, before we need to insert it.
    // When we insert they key, it might be that we need to continue displacing
    // entries (robin hood hashing), in which case Inserted::SwapWith is returned
    fn insert_phase_1(&mut self, key: K, value: V) -> Inserted {
        let hash = hash_elem(&key);
        let mut probe = desired_pos(self.mask, hash);
        let mut dist = 0;
        debug_assert!(1 + self.len() < self.capacity());
        loop {
            if probe < self.indices.len() {
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
                        //println!("entry already exists");
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
                probe += 1;
                dist += 1;
            } else {
                probe = 0;
            }
        }
    }

    fn insert_phase_2(&mut self, mut probe: usize, mut old_index: usize, mut dist: usize) {
        loop {
            if probe < self.indices.len() {
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
                probe += 1;
                dist += 1;
            } else {
                probe = 0;
            }
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        assert!(self.len() + 1 < self.capacity());
        match self.insert_phase_1(key, value) {
            Inserted::AlreadyExists | Inserted::Done => { }
            Inserted::SwapWith { probe, old_index, dist } => {
                self.insert_phase_2(probe, old_index, dist);
            }
        }

    }

    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            iter: self.entries.iter()
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        let h = hash_elem(key);
        let mut probe = h as usize & self.mask;
        let mut dist = 0;
        loop {
            if probe < self.indices.len() {
                if let Some(i) = self.indices[probe].pos() {
                    let entry = &self.entries[i];
                    let that_dist = probe_distance(self.mask, entry.hash, probe);
                    if dist > that_dist {
                        // give up when probe distance is too long
                        break;
                    } else if entry.hash == h && *entry.key.borrow() == *key {
                        return Some(&entry.key);
                    }
                } else {
                    break;
                }
                probe += 1;
                dist += 1;
            } else {
                probe = 0;
            }
        }
        None
    }
}

use std::slice::Iter as SliceIter;

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

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> { }


use std::ops::Index;

impl<'a, K, V> Index<&'a K> for OrderedMap<K, V>
    where K: Eq + Hash
{
    type Output = K;
    fn index(&self, key: &'a K) -> &K {
        if let Some(v) = self.get(key) {
            v
        } else {
            panic!("OrderedMap: key not found")
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut map = OrderedMap::new();
        println!("{:?}", map);
        map.insert(1, ());
        map.insert(1, ());
        println!("{:?}", map);
        /*
        println!("{:?}", map);
        map.insert(2);
        println!("{:?}", map);
        println!("{:?}", map[&2]);
        */
        //println!("{:?}", map[&3]);
        for i in 0..map.capacity() - 2 {
            println!("Insert {}", i);
            map.insert(i, ());
            println!("{:?}", map);
            for j in 0..i + 1 {
                print!("{:?}, ", map[&j]);
            }
            println!("");
            for key in map.keys() {
                print!("key={}, ", key);
            }
            println!("");
        }
    }

    #[test]
    fn insert_works() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5];
        let not_present = [1, 3, 6, 9, 10];
        let mut map = OrderedMap::with_capacity(insert.len() + 1);

        for (i, &elt) in insert.iter().enumerate() {
            assert_eq!(map.len(), i);
            map.insert(elt, ());
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
    fn insert_works_2() {
        let mut map = OrderedMap::with_capacity(64);

        for i in 0..58 {
            map.insert(i, ());
        }
        println!("{:?}", map);

        for i in 0..64 {
            assert_eq!(map.get(&i).is_some(), i < 58, "did not find {}", i);
        }
    }

    #[test]
    fn insert_order() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5];
        let mut map = OrderedMap::with_capacity(insert.len() + 1);

        for &elt in &insert {
            map.insert(elt, ());
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
    }
}
