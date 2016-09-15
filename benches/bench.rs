#![feature(test)]
extern crate test;
extern crate rand;

use test::Bencher;

extern crate orderedmap;

use orderedmap::OrderedMap;

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
        OrderedMap::<String, String>::new()
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
        OrderedMap::<String, String>::with_capacity(10_000)
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

#[bench]
fn lookup_hashmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = HashMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        let mut found = 0;
        for key in 5000..15000 {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    let mut map = OrderedMap::with_capacity(c);
    let len = c - c/10;
    for x in 0..len {
        map.insert(x, ());
    }
    assert_eq!(map.len(), len);
    b.iter(|| {
        let mut found = 0;
        for key in 5000..15000 {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_hashmap_100_000(b: &mut Bencher) {
    let c = 100_000;
    let mut map = HashMap::with_capacity(c);
    let mut keys = (0..c - c/10).collect::<Vec<_>>();
    for &key in &keys {
        map.insert(key, ());
    }
    assert_eq!(map.len(), keys.len());
    let mut rng = weak_rng();
    rng.shuffle(&mut keys);
    let len = keys.len();
    keys.truncate(len/2);
    b.iter(|| {
        let mut found = 0;
        for &key in &keys {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

#[bench]
fn lookup_orderedmap_100_000(b: &mut Bencher) {
    let c = 100_000;
    let mut map = OrderedMap::with_capacity(c);
    let mut keys = (0..c - c/10).collect::<Vec<_>>();
    for &key in &keys {
        map.insert(key, ());
    }
    assert_eq!(map.len(), keys.len());
    let mut rng = weak_rng();
    rng.shuffle(&mut keys);
    let len = keys.len();
    keys.truncate(len/2);
    b.iter(|| {
        let mut found = 0;
        for &key in &keys {
            found += map.get(&key).is_some() as i32;
        }
        found
    });
}

// without preallocation
#[bench]
fn grow_hashmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = HashMap::new();
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}

#[bench]
fn grow_orderedmap_10_000(b: &mut Bencher) {
    let c = 10_000;
    b.iter(|| {
        let mut map = OrderedMap::new();
        for x in 0..c {
            map.insert(x, ());
        }
        map
    });
}
