#![cfg(test)]

use approxim::{assert_abs_diff_eq, assert_relative_eq, assert_ulps_eq};
use indexmap::indexmap;

#[test]
fn test_abs_diff_eq() {
    // check with non-zero epsilon
    let left = indexmap! { 1 => 1000, 2 => 2000 };
    let right = indexmap! { 1 => 1001, 2 => 1999 };
    assert_abs_diff_eq!(left, right, epsilon = 1);

    // check different insertion order
    let left = indexmap! { 1 => 2, 3 => 4 };
    let right = indexmap! { 3 => 4, 1 => 2,  };
    assert_abs_diff_eq!(left, right);
}

#[test]
#[should_panic]
fn test_abs_diff_eq_len() {
    let left = indexmap! { 1 => 1000, 2 => 2000 };
    let right = indexmap! { 1 => 1000, 2 => 2000, 3 => 3000 };
    assert_abs_diff_eq!(left, right);
}

#[test]
fn test_relative_eq() {
    // check with non-default epsilon
    let left = indexmap! { 1 => 1.71828182, 2 => 1.0 };
    let right = indexmap! { 1 => 1.718281815, 2 => 1.00000001 };
    assert_relative_eq!(left, right, epsilon = 1e-8);

    // check with non-default max relative value
    let left = indexmap! { 1 => 1., 2 => 1. };
    let right = indexmap! { 1 => 1.2, 2 => 1.5 };
    assert_relative_eq!(left, right, max_relative = 0.34);

    // check different insertion order
    let left = indexmap! { 1 => 2., 3 => 8. };
    let right = indexmap! { 3 => 8., 1 => 2.,  };
    assert_relative_eq!(left, right);
}

#[test]
#[should_panic]
fn test_relative_eq_len() {
    let left = indexmap! { 1 => 0., 2 => 1. };
    let right = indexmap! { 1 => 0., 2 => 1., 3 => 2. };
    assert_relative_eq!(left, right);
}

#[test]
fn test_ulps_eq() {
    // check with non-default epsilon
    let left = indexmap! { 1 => 0., 2 => 0. };
    let right = indexmap! { 1 => 1e-41, 2 => 1e-40 };
    assert_ulps_eq!(left, right, epsilon = 1e-40);

    // check with non-default max ulps value
    let left = indexmap! { 1 => 1., 2 => 1. };
    let right = indexmap! { 1 => 1. + 1e-16, 2 => 1. + 1e-15 };
    assert_ulps_eq!(left, right, max_ulps = 5);

    // check different insertion order
    let left = indexmap! { 1 => 2., 3 => 8. };
    let right = indexmap! { 3 => 8., 1 => 2.,  };
    assert_ulps_eq!(left, right);
}

#[test]
#[should_panic]
fn test_ulps_eq_len() {
    let left = indexmap! { 1 => 0., 2 => 1. };
    let right = indexmap! { 1 => 0., 2 => 1., 3 => 2. };
    assert_ulps_eq!(left, right);
}
