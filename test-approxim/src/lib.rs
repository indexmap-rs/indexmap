#![cfg(test)]

use approxim::{assert_abs_diff_eq, assert_relative_eq};
use indexmap::indexmap;

#[test]
fn test_abs_diff_eq() {
    let left = indexmap! { 1 => 1000, 2 => 2000 };
    let right = indexmap! { 1 => 1001, 2 => 1999 };
    assert_abs_diff_eq!(left, right, epsilon = 1);
}

#[test]
#[should_panic]
fn test_abs_diff_eq_different_insertion_order() {
    let left = indexmap! { 1 => 2, 3 => 4 };
    let right = indexmap! { 3 => 4, 1 => 2,  };
    assert_abs_diff_eq!(left, right);
}

#[test]
fn test_relative_eq() {
    let left = indexmap! { 1 => 1.71828182, 2 => 1.0 };
    let right = indexmap! { 1 => 1.718281815, 2 => 1.00000001 };
    assert_relative_eq!(left, right, epsilon = 1e-8);

    let left = indexmap! { 1 => 1., 2 => 1. };
    let right = indexmap! { 1 => 1.2, 2 => 1.5 };
    assert_relative_eq!(left, right, max_relative = 0.34);
}

#[test]
#[should_panic]
fn test_relative_eq_different_insertion_order() {
    let left = indexmap! { 1 => 2., 3 => 8. };
    let right = indexmap! { 3 => 8., 1 => 2.,  };
    assert_relative_eq!(left, right);
}
