#![cfg_attr(docsrs, doc(cfg(feature = "approxim")))]
//! Trait implementations from [`approxim`](https://docs.rs/approxim/latest/approxim/) crate
//! for [`IndexMap`].
//!
//! Keys are compared using `PartialEq` and values are compared using the approximate comparison
//! traits. Insertion order is not taken into account for the comparison, just as with
//! [`PartialEq`].

use core::hash::BuildHasher;
use std::hash::Hash;

use approxim::{AbsDiffEq, RelativeEq, UlpsEq};

use crate::IndexMap;

impl<K, V1, V2, S1, S2> AbsDiffEq<IndexMap<K, V2, S2>> for IndexMap<K, V1, S1>
where
    K: Eq + Hash,
    V1: AbsDiffEq<V2>,
    V1::Epsilon: Copy,
    S1: BuildHasher,
    S2: BuildHasher,
{
    type Epsilon = V1::Epsilon;

    fn default_epsilon() -> Self::Epsilon {
        V1::default_epsilon()
    }

    fn abs_diff_eq(&self, other: &IndexMap<K, V2, S2>, epsilon: Self::Epsilon) -> bool {
        self.len() == other.len()
            && self.iter().all(|(key, value)| {
                other
                    .get(key)
                    .map_or(false, |v| value.abs_diff_eq(v, epsilon))
            })
    }
}

impl<K, V1, V2, S1, S2> RelativeEq<IndexMap<K, V2, S2>> for IndexMap<K, V1, S1>
where
    K: Eq + Hash,
    V1: RelativeEq<V2>,
    V1::Epsilon: Copy,
    S1: BuildHasher,
    S2: BuildHasher,
{
    fn default_max_relative() -> Self::Epsilon {
        V1::default_max_relative()
    }

    fn relative_eq(
        &self,
        other: &IndexMap<K, V2, S2>,
        epsilon: Self::Epsilon,
        max_relative: Self::Epsilon,
    ) -> bool {
        self.len() == other.len()
            && self.iter().all(|(key, value)| {
                other
                    .get(key)
                    .map_or(false, |v| value.relative_eq(v, epsilon, max_relative))
            })
    }
}

impl<K, V1, V2, S1, S2> UlpsEq<IndexMap<K, V2, S2>> for IndexMap<K, V1, S1>
where
    K: Eq + Hash,
    V1: UlpsEq<V2>,
    V1::Epsilon: Copy,
    S1: BuildHasher,
    S2: BuildHasher,
{
    fn default_max_ulps() -> u32 {
        V1::default_max_ulps()
    }

    fn ulps_eq(&self, other: &IndexMap<K, V2, S2>, epsilon: Self::Epsilon, max_ulps: u32) -> bool {
        self.len() == other.len()
            && self.iter().all(|(key, value)| {
                other
                    .get(key)
                    .map_or(false, |v| value.ulps_eq(v, epsilon, max_ulps))
            })
    }
}
