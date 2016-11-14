#![feature(test)]
extern crate test;
extern crate rand;
extern crate fnv;
#[macro_use]
extern crate lazy_static;

use fnv::FnvHasher;
use std::hash::BuildHasherDefault;
type FnvBuilder = BuildHasherDefault<FnvHasher>;

use test::Bencher;
use test::black_box;

extern crate ordermap;

use ordermap::OrderMap;

use std::collections::HashMap;
use std::iter::FromIterator;

use rand::{weak_rng, Rng};

#[bench]
fn new_hashmap(b: &mut Bencher) {
    b.iter(|| {
        HashMap::<String, String>::new()
    });
}

#[bench]
fn new_orderedmap(b: &mut Bencher) {
    b.iter(|| {
        OrderMap::<String, String>::new()
    });
}

#[bench]
fn with_capacity_10e5_hashmap(b: &mut Bencher) {
    b.iter(|| {
        HashMap::<String, String>::with_capacity(10_000)
    });
}

#[bench]
fn with_capacity_10e5_orderedmap(b: &mut Bencher) {
    b.iter(|| {
        OrderMap::<String, String>::with_capacity(10_000)
    });
}

#[bench]
fn insert_hashmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn insert_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn insert_hashmap_string_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for x in 0..c {
            map.insert(x.to_string(), ());
        }
        map
    });
}

#[bench]
fn insert_orderedmap_string_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for x in 0..c {
            map.insert(x.to_string(), ());
        }
        map
    });
}

#[bench]
fn insert_hashmap_str_10_000(b: &mut Bencher) {
    let c = 10_000;
    let ss = Vec::from_iter((0..c).map(|x| x.to_string()));
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for key in &ss {
            map.insert(&key[..], ());
        }
        map
    });
}

#[bench]
fn insert_orderedmap_str_10_000(b: &mut Bencher) {
    let c = 10_000;
    let ss = Vec::from_iter((0..c).map(|x| x.to_string()));
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for key in &ss {
            map.insert(&key[..], ());
        }
        map
    });
}

#[bench]
fn insert_hashmap_int_bigvalue_10_000(b: &mut Bencher) {
    let c = 10_000;
    let value = [0u64; 10];
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for i in 0..c {
            map.insert(i, value);
        }
        map
    });
}

#[bench]
fn insert_orderedmap_int_bigvalue_10_000(b: &mut Bencher) {
    let c = 10_000;
    let value = [0u64; 10];
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for i in 0..c {
            map.insert(i, value);
        }
        map
    });
}

#[bench]
fn insert_hashmap_100_000(b: &mut Bencher) {
    let c = 100_000;
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn insert_orderedmap_100_000(b: &mut Bencher) {
    let c = 100_000;
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn insert_hashmap_150(b: &mut Bencher) {
    let c = 150;
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn insert_orderedmap_150(b: &mut Bencher) {
    let c = 150;
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn entry_hashmap_150(b: &mut Bencher) {
    let c = 150;
    b.iter(|| {
        let mut map = HashMap::with_capacity(c);
        for x in 0..c {
            map.entry(x).or_insert(());
        }
        map
    });
}

#[bench]
fn entry_orderedmap_150(b: &mut Bencher) {
    let c = 150;
    b.iter(|| {
        let mut map = OrderMap::with_capacity(c);
        for x in 0..c {
            map.entry(x).or_insert(());
        }
        map
    });
}

#[bench]
fn iter_sum_hashmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = HashMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        map.keys().sum::<usize>()
    });
}

#[bench]
fn iter_sum_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        map.keys().sum::<usize>()
    });
}

#[bench]
fn iter_black_box_hashmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = HashMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        for &key in map.keys() {
            black_box(key);
        }
    });
}

#[bench]
fn iter_black_box_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        for &key in map.keys() {
            black_box(key);
        }
    });
}

fn shuffled_keys<I>(iter: I) -> Vec<I::Item>
    where I: IntoIterator
{
    let mut v = Vec::from_iter(iter);
    let mut rng = weak_rng();
    rng.shuffle(&mut v);
    v
}

#[bench]
fn lookup_hashmap_10_000_exist(b: &mut Bencher) {
    let c = 10_000;
    let mut map = HashMap::with_capacity(c);
    let keys = shuffled_keys(0..c);
    for &key in &keys {
        map.insert(key, 1);
    }
    b.iter(|| {
        let mut found = 0;
        for key in 5000..c {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_hashmap_10_000_noexist(b: &mut Bencher) {
    let c = 10_000;
    let mut map = HashMap::with_capacity(c);
    let keys = shuffled_keys(0..c);
    for &key in &keys {
        map.insert(key, 1);
    }
    b.iter(|| {
        let mut found = 0;
        for key in c..15000 {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_orderedmap_10_000_exist(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderMap::with_capacity(c);
    let keys = shuffled_keys(0..c);
    for &key in &keys {
        map.insert(key, 1);
    }
    b.iter(|| {
        let mut found = 0;
        for key in 5000..c {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_orderedmap_10_000_noexist(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderMap::with_capacity(c);
    let keys = shuffled_keys(0..c);
    for &key in &keys {
        map.insert(key, 1);
    }
    b.iter(|| {
        let mut found = 0;
        for key in c..15000 {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

// number of items to look up
const LOOKUP_MAP_SIZE: u32 = 100_000_u32;
const LOOKUP_SAMPLE_SIZE: u32 = 5000;


lazy_static! {
    static ref KEYS: Vec<u32> = {
        shuffled_keys(0..LOOKUP_MAP_SIZE)
    };
}
lazy_static! {
    static ref HMAP_100K: HashMap<u32, u32> = {
        let c = LOOKUP_MAP_SIZE;
        let mut map = HashMap::with_capacity(c as usize);
        let keys = &*KEYS;
        for &key in keys {
            map.insert(key, key);
        }
        map
    };
}

lazy_static! {
    static ref OMAP_100K: OrderMap<u32, u32> = {
        let c = LOOKUP_MAP_SIZE;
        let mut map = OrderMap::with_capacity(c as usize);
        let keys = &*KEYS;
        for &key in keys {
            map.insert(key, key);
        }
        map
    };
}

#[bench]
fn lookup_hashmap_100_000_multi(b: &mut Bencher) {
    let map = &*HMAP_100K;
    b.iter(|| {
        let mut found = 0;
        for key in 0..LOOKUP_SAMPLE_SIZE {
            found += map.get(&key).is_some() as u32;
        }
        found
    });
}


#[bench]
fn lookup_ordermap_100_000_multi(b: &mut Bencher) {
    let map = &*OMAP_100K;
    b.iter(|| {
        let mut found = 0;
        for key in 0..LOOKUP_SAMPLE_SIZE {
            found += map.get(&key).is_some() as u32;
        }
        found
    });
}

// inorder: Test looking up keys in the same order as they were inserted
#[bench]
fn lookup_hashmap_100_000_inorder_multi(b: &mut Bencher) {
    let map = &*HMAP_100K;
    let keys = &*KEYS;
    b.iter(|| {
        let mut found = 0;
        for key in &keys[0..LOOKUP_SAMPLE_SIZE as usize] {
            found += map.get(key).is_some() as u32;
        }
        found
    });
}


#[bench]
fn lookup_ordermap_100_000_inorder_multi(b: &mut Bencher) {
    let map = &*OMAP_100K;
    let keys = &*KEYS;
    b.iter(|| {
        let mut found = 0;
        for key in &keys[0..LOOKUP_SAMPLE_SIZE as usize] {
            found += map.get(key).is_some() as u32;
        }
        found
    });
}

#[bench]
fn lookup_hashmap_100_000_single(b: &mut Bencher) {
    let map = &*HMAP_100K;
    let mut iter = (0..LOOKUP_MAP_SIZE + LOOKUP_SAMPLE_SIZE).cycle();
    b.iter(|| {
        let key = iter.next().unwrap();
        map.get(&key).is_some()
    });
}


#[bench]
fn lookup_ordermap_100_000_single(b: &mut Bencher) {
    let map = &*OMAP_100K;
    let mut iter = (0..LOOKUP_MAP_SIZE + LOOKUP_SAMPLE_SIZE).cycle();
    b.iter(|| {
        let key = iter.next().unwrap();
        map.get(&key).is_some()
    });
}

const GROW_SIZE: usize = 100_000;
type GrowKey = u32;

// Test grow/resize without preallocation
#[bench]
fn grow_fnv_hashmap_100_000(b: &mut Bencher) {
    b.iter(|| {
        let mut map: HashMap<_, _, FnvBuilder> = HashMap::default();
        for x in 0..GROW_SIZE {
            map.insert(x as GrowKey, x as GrowKey);
        }
        map
    });
}

#[bench]
fn grow_fnv_ordermap_100_000(b: &mut Bencher) {
    b.iter(|| {
        let mut map: OrderMap<_, _, FnvBuilder> = OrderMap::default();
        for x in 0..GROW_SIZE {
            map.insert(x as GrowKey, x as GrowKey);
        }
        map
    });
}


const MERGE: u64 = 10_000;
#[bench]
fn hashmap_merge_simple(b: &mut Bencher) {
    let first_map: HashMap<u64, _> = (0..MERGE).map(|i| (i, ())).collect();
    let second_map: HashMap<u64, _> = (MERGE..MERGE * 2).map(|i| (i, ())).collect();
    b.iter(|| {
        let mut merged = first_map.clone();
        merged.extend(second_map.iter().map(|(&k, &v)| (k, v)));
        merged
    });
}

#[bench]
fn hashmap_merge_shuffle(b: &mut Bencher) {
    let first_map: HashMap<u64, _> = (0..MERGE).map(|i| (i, ())).collect();
    let second_map: HashMap<u64, _> = (MERGE..MERGE * 2).map(|i| (i, ())).collect();
    let mut v = Vec::new();
    let mut rng = weak_rng();
    b.iter(|| {
        let mut merged = first_map.clone();
        v.extend(second_map.iter().map(|(&k, &v)| (k, v)));
        rng.shuffle(&mut v);
        merged.extend(v.drain(..));

        merged
    });
}

#[bench]
fn ordermap_merge_simple(b: &mut Bencher) {
    let first_map: OrderMap<u64, _> = (0..MERGE).map(|i| (i, ())).collect();
    let second_map: OrderMap<u64, _> = (MERGE..MERGE * 2).map(|i| (i, ())).collect();
    b.iter(|| {
        let mut merged = first_map.clone();
        merged.extend(second_map.iter().map(|(&k, &v)| (k, v)));
        merged
    });
}

#[bench]
fn ordermap_merge_shuffle(b: &mut Bencher) {
    let first_map: OrderMap<u64, _> = (0..MERGE).map(|i| (i, ())).collect();
    let second_map: OrderMap<u64, _> = (MERGE..MERGE * 2).map(|i| (i, ())).collect();
    let mut v = Vec::new();
    let mut rng = weak_rng();
    b.iter(|| {
        let mut merged = first_map.clone();
        v.extend(second_map.iter().map(|(&k, &v)| (k, v)));
        rng.shuffle(&mut v);
        merged.extend(v.drain(..));

        merged
    });
}

#[bench]
fn remove_ordermap_100_000(b: &mut Bencher) {
    let map = OMAP_100K.clone();
    let mut keys = Vec::from_iter(map.keys().cloned());
    weak_rng().shuffle(&mut keys);

    b.iter(|| {
        let mut map = map.clone();
        for key in &keys {
            map.remove(key).is_some();
        }
        assert_eq!(map.len(), 0);
        map
    });
}

#[bench]
fn pop_ordermap_100_000(b: &mut Bencher) {
    let map = OMAP_100K.clone();

    b.iter(|| {
        let mut map = map.clone();
        while map.len() > 0 {
            map.pop();
        }
        assert_eq!(map.len(), 0);
        map
    });
}

#[bench]
fn retain_few_ordermap_100_000(b: &mut Bencher) {
    let map = OMAP_100K.clone();

    b.iter(|| {
        let mut map = map.clone();
        map.retain(|k, _| *k % 7 == 0);
        map
    });
}

#[bench]
fn retain_half_ordermap_100_000(b: &mut Bencher) {
    let map = OMAP_100K.clone();

    b.iter(|| {
        let mut map = map.clone();
        map.retain(|k, _| *k % 2 == 0);
        map
    });
}

#[bench]
fn retain_many_ordermap_100_000(b: &mut Bencher) {
    let map = OMAP_100K.clone();

    b.iter(|| {
        let mut map = map.clone();
        map.retain(|k, _| *k % 100 != 0);
        map
    });
}
