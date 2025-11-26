#![cfg_attr(docsrs, doc(cfg(feature = "approxim")))]
//! Trait implementations from [`approxim`](https://docs.rs/approxim/latest/approxim/) crate.
//!
//! Considering [`IndexMap`] preserves insertion order, these trait implementations
//! take that into account. Meaning
//! ```should_panic
//! # use approxim::assert_abs_diff_eq;
//! # use indexmap::indexmap;
//!
//! let left = indexmap! { 1 => 2, 3 => 4 };
//! let right = indexmap! { 3 => 4, 1 => 2,  };
//!
//! assert_abs_diff_eq!(left, right); // false
//! ```
//! will result in relative inequality, despite the contents
//! being the same.

use core::hash::BuildHasher;
use std::hash::Hash;

use approxim::{AbsDiffEq, RelativeEq, UlpsEq};

use crate::IndexMap;

impl<K, V, S> AbsDiffEq for IndexMap<K, V, S>
where
    K: Eq + Hash,
    V: AbsDiffEq,
    V::Epsilon: Copy,
    S: BuildHasher,
{
    type Epsilon = V::Epsilon;

    fn default_epsilon() -> Self::Epsilon {
        V::default_epsilon()
    }

    fn abs_diff_eq(&self, other: &Self, epsilon: Self::Epsilon) -> bool {
        self.len() == other.len()
            && self.iter().zip(other.iter()).all(
                |((key_left, val_left), (key_right, val_right))| {
                    key_left == key_right && val_left.abs_diff_eq(val_right, epsilon)
                },
            )
    }
}

/// RelativeEq implementation for V:RelativeEq
impl<K, V, S> RelativeEq for IndexMap<K, V, S>
where
    K: Eq + Hash,
    V: RelativeEq,
    V::Epsilon: Copy,
    S: BuildHasher,
{
    fn default_max_relative() -> Self::Epsilon {
        V::default_max_relative()
    }

    fn relative_eq(
        &self,
        other: &Self,
        epsilon: Self::Epsilon,
        max_relative: Self::Epsilon,
    ) -> bool {
        self.len() == other.len()
            && self.iter().zip(other.iter()).all(
                |((key_left, val_left), (key_right, val_right))| {
                    key_left == key_right && val_left.relative_eq(val_right, epsilon, max_relative)
                },
            )
    }
}

impl<K, V, S> UlpsEq for IndexMap<K, V, S>
where
    K: Eq + Hash,
    V: UlpsEq,
    V::Epsilon: Copy,
    S: BuildHasher,
{
    fn default_max_ulps() -> u32 {
        V::default_max_ulps()
    }

    fn ulps_eq(&self, other: &Self, epsilon: Self::Epsilon, max_ulps: u32) -> bool {
        self.len() == other.len()
            && self.iter().zip(other.iter()).all(
                |((key_left, val_left), (key_right, val_right))| {
                    key_left == key_right && val_left.ulps_eq(val_right, epsilon, max_ulps)
                },
            )
    }
}
