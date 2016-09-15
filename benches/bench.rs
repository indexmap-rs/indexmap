#![feature(test)]
extern crate test;

use test::Bencher;

extern crate orderedmap;

use orderedmap::OrderedMap;

use std::collections::HashMap;
use std::iter::FromIterator;

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
        let mut map = OrderedMap::with_capacity(c);
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
        let mut map = OrderedMap::with_capacity(c);
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
        let mut map = OrderedMap::with_capacity(c);
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
        let mut map = OrderedMap::with_capacity(c);
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
        let mut map = OrderedMap::with_capacity(c);
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
        let mut map = OrderedMap::with_capacity(c);
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn iterate_hashmap_10_000(b: &mut Bencher) {
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
fn iterate_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderedMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        map.keys().sum::<usize>()
    });
}

