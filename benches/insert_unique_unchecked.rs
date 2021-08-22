#![feature(test)]

extern crate test;

use test::Bencher;

use indexmap::IndexMap;

#[bench]
fn insert(b: &mut Bencher) {
    b.iter(|| {
        let mut m = IndexMap::with_capacity(1000);
        for i in 0..1000 {
            m.insert(i, i);
        }
        m
    });
}

#[bench]
fn insert_unique_unchecked(b: &mut Bencher) {
    b.iter(|| {
        let mut m = IndexMap::with_capacity(1000);
        for i in 0..1000 {
            m.insert_unique_unchecked(i, i);
        }
        m
    });
}
