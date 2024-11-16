use indexmap::{indexmap, indexset, IndexMap, IndexSet};

#[test]
fn test_set_just() {
    let s = IndexSet::<u8>::just(42);
    assert_eq!(s, indexset!(42));
}

#[test]
fn test_map_just() {
    let m = IndexMap::<u8, u16>::just((42, 1337));
    assert_eq!(m.get(&42), Some(&1337));
}

#[test]
fn test_sort() {
    let m = indexmap! {
        1 => 2,
        7 => 1,
        2 => 2,
        3 => 3,
    };

    itertools::assert_equal(
        m.sorted_by(|_k1, v1, _k2, v2| v1.cmp(v2)),
        vec![(7, 1), (1, 2), (2, 2), (3, 3)],
    );
}

#[test]
fn test_sort_set() {
    let s = indexset! {
        1,
        7,
        2,
        3,
    };

    itertools::assert_equal(s.sorted_by(|v1, v2| v1.cmp(v2)), vec![1, 2, 3, 7]);
}
