//! Opt-in access to the experimental raw entry API.
//!
//! This module is designed to mimic the raw entry API of [`HashMap`][std::collections::hash_map],
//! matching its unstable state as of Rust 1.75. See the tracking issue
//! [rust#56167](https://github.com/rust-lang/rust/issues/56167) for more details.
//!
//! The trait [`RawEntryApiV1`] and the `_v1` suffix on its methods are meant to insulate this for
//! the future, in case later breaking changes are needed. If the standard library stabilizes its
//! `hash_raw_entry` feature (or some replacement), matching *inherent* methods will be added to
//! `IndexMap` without such an opt-in trait.

use super::raw::RawTableEntry;
use super::{get_hash, IndexMapCore};
use crate::{Equivalent, HashValue, IndexMap};
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;
use core::mem;

/// Opt-in access to the experimental raw entry API.
///
/// See the [`raw_entry_v1`][self] module documentation for more information.
pub trait RawEntryApiV1<K, V, S>: private::Sealed {
    /// Creates a raw immutable entry builder for the [`IndexMap`].
    fn raw_entry_v1(&self) -> RawEntryBuilder<'_, K, V, S>;

    /// Creates a raw entry builder for the [`IndexMap`].
    fn raw_entry_mut_v1(&mut self) -> RawEntryBuilderMut<'_, K, V, S>;
}

impl<K, V, S> RawEntryApiV1<K, V, S> for IndexMap<K, V, S> {
    fn raw_entry_v1(&self) -> RawEntryBuilder<'_, K, V, S> {
        RawEntryBuilder { map: self }
    }

    fn raw_entry_mut_v1(&mut self) -> RawEntryBuilderMut<'_, K, V, S> {
        RawEntryBuilderMut { map: self }
    }
}

/// A builder for computing where in an [`IndexMap`] a key-value pair would be stored.
///
/// This `struct` is created by the [`IndexMap::raw_entry_v1`] method, provided by the
/// [`RawEntryApiV1`] trait. See its documentation for more.
pub struct RawEntryBuilder<'a, K, V, S> {
    map: &'a IndexMap<K, V, S>,
}

impl<'a, K, V, S> RawEntryBuilder<'a, K, V, S> {
    /// Access an entry by key.
    pub fn from_key<Q: ?Sized>(self, key: &Q) -> Option<(&'a K, &'a V)>
    where
        S: BuildHasher,
        Q: Hash + Equivalent<K>,
    {
        self.map.get_key_value(key)
    }

    /// Access an entry by a key and its hash.
    pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, key: &Q) -> Option<(&'a K, &'a V)>
    where
        Q: Equivalent<K>,
    {
        let hash = HashValue(hash as usize);
        let i = self.map.core.get_index_of(hash, key)?;
        Some(self.map.core.entries[i].refs())
    }

    /// Access an entry by hash.
    pub fn from_hash<F>(self, hash: u64, mut is_match: F) -> Option<(&'a K, &'a V)>
    where
        F: FnMut(&K) -> bool,
    {
        let hash = HashValue(hash as usize);
        let entries = &*self.map.core.entries;
        let eq = move |&i: &usize| is_match(&entries[i].key);
        let i = *self.map.core.indices.get(hash.get(), eq)?;
        Some(entries[i].refs())
    }
}

/// A builder for computing where in an [`IndexMap`] a key-value pair would be stored.
///
/// This `struct` is created by the [`IndexMap::raw_entry_mut_v1`] method, provided by the
/// [`RawEntryApiV1`] trait. See its documentation for more.
pub struct RawEntryBuilderMut<'a, K, V, S> {
    map: &'a mut IndexMap<K, V, S>,
}

impl<'a, K, V, S> RawEntryBuilderMut<'a, K, V, S> {
    /// Access an entry by key.
    pub fn from_key<Q: ?Sized>(self, key: &Q) -> RawEntryMut<'a, K, V, S>
    where
        S: BuildHasher,
        Q: Hash + Equivalent<K>,
    {
        let hash = self.map.hash(key);
        self.from_key_hashed_nocheck(hash.get(), key)
    }

    /// Access an entry by a key and its hash.
    pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, key: &Q) -> RawEntryMut<'a, K, V, S>
    where
        Q: Equivalent<K>,
    {
        self.from_hash(hash, |k| Q::equivalent(key, k))
    }

    /// Access an entry by hash.
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> RawEntryMut<'a, K, V, S>
    where
        F: FnMut(&K) -> bool,
    {
        let hash = HashValue(hash as usize);
        match self.map.core.raw_entry(hash, is_match) {
            Ok(raw) => RawEntryMut::Occupied(RawOccupiedEntryMut {
                raw,
                hash_builder: PhantomData,
            }),
            Err(map) => RawEntryMut::Vacant(RawVacantEntryMut {
                map,
                hash_builder: &self.map.hash_builder,
            }),
        }
    }
}

/// Raw entry for an existing key-value pair or a vacant location to
/// insert one.
pub enum RawEntryMut<'a, K, V, S> {
    /// Existing slot with equivalent key.
    Occupied(RawOccupiedEntryMut<'a, K, V, S>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(RawVacantEntryMut<'a, K, V, S>),
}

impl<'a, K, V, S> RawEntryMut<'a, K, V, S> {
    /// Inserts the given default key and value in the entry if it is vacant and returns mutable
    /// references to them. Otherwise mutable references to an already existent pair are returned.
    pub fn or_insert(self, default_key: K, default_value: V) -> (&'a mut K, &'a mut V)
    where
        K: Hash,
        S: BuildHasher,
    {
        match self {
            Self::Occupied(entry) => entry.into_key_value_mut(),
            Self::Vacant(entry) => entry.insert(default_key, default_value),
        }
    }

    /// Inserts the result of the `call` function in the entry if it is vacant and returns mutable
    /// references to them. Otherwise mutable references to an already existent pair are returned.
    pub fn or_insert_with<F>(self, call: F) -> (&'a mut K, &'a mut V)
    where
        F: FnOnce() -> (K, V),
        K: Hash,
        S: BuildHasher,
    {
        match self {
            Self::Occupied(entry) => entry.into_key_value_mut(),
            Self::Vacant(entry) => {
                let (key, value) = call();
                entry.insert(key, value)
            }
        }
    }

    /// Modifies the entry if it is occupied.
    pub fn and_modify<F>(mut self, f: F) -> Self
    where
        F: FnOnce(&mut K, &mut V),
    {
        if let Self::Occupied(entry) = &mut self {
            let (k, v) = entry.get_key_value_mut();
            f(k, v);
        }
        self
    }
}

/// A raw view into an occupied entry in an [`IndexMap`].
/// It is part of the [`RawEntryMut`] enum.
pub struct RawOccupiedEntryMut<'a, K, V, S> {
    raw: RawTableEntry<'a, K, V>,
    hash_builder: PhantomData<&'a S>,
}

impl<'a, K, V, S> RawOccupiedEntryMut<'a, K, V, S> {
    /// Return the index of the key-value pair
    #[inline]
    pub fn index(&self) -> usize {
        self.raw.index()
    }

    /// Gets a reference to the entry's key in the map.
    ///
    /// Note that this is not the key that was used to find the entry. There may be an observable
    /// difference if the key type has any distinguishing features outside of `Hash` and `Eq`, like
    /// extra fields or the memory address of an allocation.
    pub fn key(&self) -> &K {
        &self.raw.bucket().key
    }

    /// Gets a mutable reference to the entry's key in the map.
    ///
    /// Note that this is not the key that was used to find the entry. There may be an observable
    /// difference if the key type has any distinguishing features outside of `Hash` and `Eq`, like
    /// extra fields or the memory address of an allocation.
    pub fn key_mut(&mut self) -> &mut K {
        &mut self.raw.bucket_mut().key
    }

    /// Converts into a mutable reference to the entry's key in the map,
    /// with a lifetime bound to the map itself.
    ///
    /// Note that this is not the key that was used to find the entry. There may be an observable
    /// difference if the key type has any distinguishing features outside of `Hash` and `Eq`, like
    /// extra fields or the memory address of an allocation.
    pub fn into_key(&mut self) -> &mut K {
        &mut self.raw.bucket_mut().key
    }

    /// Gets a reference to the entry's value in the map.
    pub fn get(&self) -> &V {
        &self.raw.bucket().value
    }

    /// Gets a mutable reference to the entry's value in the map.
    ///
    /// If you need a reference which may outlive the destruction of the
    /// [`RawEntryMut`] value, see [`into_mut`][Self::into_mut].
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.raw.bucket_mut().value
    }

    /// Converts into a mutable reference to the entry's value in the map,
    /// with a lifetime bound to the map itself.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.raw.into_bucket().value
    }

    /// Gets a reference to the entry's key and value in the map.
    pub fn get_key_value(&self) -> (&K, &V) {
        self.raw.bucket().refs()
    }

    /// Gets a reference to the entry's key and value in the map.
    pub fn get_key_value_mut(&mut self) -> (&mut K, &mut V) {
        self.raw.bucket_mut().muts()
    }

    /// Converts into a mutable reference to the entry's key and value in the map,
    /// with a lifetime bound to the map itself.
    pub fn into_key_value_mut(self) -> (&'a mut K, &'a mut V) {
        self.raw.into_bucket().muts()
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Sets the key of the entry, and returns the entry's old key.
    pub fn insert_key(&mut self, key: K) -> K {
        mem::replace(self.key_mut(), key)
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// **NOTE:** This is equivalent to [`.swap_remove()`][Self::swap_remove], replacing this
    /// entry's position with the last element, and it is deprecated in favor of calling that
    /// explicitly. If you need to preserve the relative order of the keys in the map, use
    /// [`.shift_remove()`][Self::shift_remove] instead.
    #[deprecated(note = "`remove` disrupts the map order -- \
        use `swap_remove` or `shift_remove` for explicit behavior.")]
    pub fn remove(self) -> V {
        self.swap_remove()
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// Like [`Vec::swap_remove`][crate::Vec::swap_remove], the pair is removed by swapping it with
    /// the last element of the map and popping it off.
    /// **This perturbs the position of what used to be the last element!**
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove(self) -> V {
        self.swap_remove_entry().1
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// Like [`Vec::remove`][crate::Vec::remove], the pair is removed by shifting all of the
    /// elements that follow it, preserving their relative order.
    /// **This perturbs the index of all of those elements!**
    ///
    /// Computes in **O(n)** time (average).
    pub fn shift_remove(self) -> V {
        self.shift_remove_entry().1
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// **NOTE:** This is equivalent to [`.swap_remove_entry()`][Self::swap_remove_entry],
    /// replacing this entry's position with the last element, and it is deprecated in favor of
    /// calling that explicitly. If you need to preserve the relative order of the keys in the map,
    /// use [`.shift_remove_entry()`][Self::shift_remove_entry] instead.
    #[deprecated(note = "`remove_entry` disrupts the map order -- \
        use `swap_remove_entry` or `shift_remove_entry` for explicit behavior.")]
    pub fn remove_entry(self) -> (K, V) {
        self.swap_remove_entry()
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like [`Vec::swap_remove`][crate::Vec::swap_remove], the pair is removed by swapping it with
    /// the last element of the map and popping it off.
    /// **This perturbs the position of what used to be the last element!**
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove_entry(self) -> (K, V) {
        let (map, index) = self.raw.remove_index();
        map.swap_remove_finish(index)
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like [`Vec::remove`][crate::Vec::remove], the pair is removed by shifting all of the
    /// elements that follow it, preserving their relative order.
    /// **This perturbs the index of all of those elements!**
    ///
    /// Computes in **O(n)** time (average).
    pub fn shift_remove_entry(self) -> (K, V) {
        let (map, index) = self.raw.remove_index();
        map.shift_remove_finish(index)
    }
}

/// A view into a vacant raw entry in an [`IndexMap`].
/// It is part of the [`RawEntryMut`] enum.
pub struct RawVacantEntryMut<'a, K, V, S> {
    map: &'a mut IndexMapCore<K, V>,
    hash_builder: &'a S,
}

impl<'a, K, V, S> RawVacantEntryMut<'a, K, V, S> {
    /// Return the index where a key-value pair may be inserted.
    pub fn index(&self) -> usize {
        self.map.indices.len()
    }

    /// Inserts the given key and value into the map,
    /// and returns mutable references to them.
    pub fn insert(self, key: K, value: V) -> (&'a mut K, &'a mut V)
    where
        K: Hash,
        S: BuildHasher,
    {
        let mut h = self.hash_builder.build_hasher();
        key.hash(&mut h);
        self.insert_hashed_nocheck(h.finish(), key, value)
    }

    /// Inserts the given key and value into the map with the provided hash,
    /// and returns mutable references to them.
    pub fn insert_hashed_nocheck(self, hash: u64, key: K, value: V) -> (&'a mut K, &'a mut V) {
        let i = self.index();
        let map = self.map;
        let hash = HashValue(hash as usize);
        map.indices.insert(hash.get(), i, get_hash(&map.entries));
        debug_assert_eq!(i, map.entries.len());
        map.push_entry(hash, key, value);
        map.entries[i].muts()
    }
}

mod private {
    pub trait Sealed {}

    impl<K, V, S> Sealed for super::IndexMap<K, V, S> {}
}
