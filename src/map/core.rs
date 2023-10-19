//! This is the core implementation that doesn't depend on the hasher at all.
//!
//! The methods of `IndexMapCore` don't use any Hash properties of K.
//!
//! It's cleaner to separate them out, then the compiler checks that we are not
//! using Hash at all in these methods.
//!
//! However, we should probably not let this show in the public API or docs.

use hashbrown::hash_table;

use crate::vec::{Drain, Vec};
use crate::TryReserveError;
use core::fmt;
use core::mem;
use core::ops::RangeBounds;

use crate::util::simplify_range;
use crate::{Bucket, Equivalent, HashValue};

type Indices = hash_table::HashTable<usize>;
type Entries<K, V> = Vec<Bucket<K, V>>;

/// Core of the map that does not depend on S
#[derive(Debug)]
pub(crate) struct IndexMapCore<K, V> {
    /// indices mapping from the entry hash to its index.
    indices: Indices,
    /// entries is a dense vec maintaining entry order.
    entries: Entries<K, V>,
}

#[inline(always)]
fn get_hash<K, V>(entries: &[Bucket<K, V>]) -> impl Fn(&usize) -> u64 + '_ {
    move |&i| entries[i].hash.get()
}

#[inline]
fn equivalent<'a, K, V, Q: ?Sized + Equivalent<K>>(
    key: &'a Q,
    entries: &'a [Bucket<K, V>],
) -> impl Fn(&usize) -> bool + 'a {
    move |&i| Q::equivalent(key, &entries[i].key)
}

#[inline]
fn erase_index(table: &mut Indices, hash: HashValue, index: usize) {
    if let Ok(entry) = table.find_entry(hash.get(), move |&i| i == index) {
        entry.remove();
    } else if cfg!(debug_assertions) {
        panic!("index not found");
    }
}

#[inline]
fn update_index(table: &mut Indices, hash: HashValue, old: usize, new: usize) {
    let index = table
        .find_mut(hash.get(), move |&i| i == old)
        .expect("index not found");
    *index = new;
}

/// Inserts many entries into the indices table without reallocating,
/// and without regard for duplication.
///
/// ***Panics*** if there is not sufficient capacity already.
fn insert_bulk_no_grow<K, V>(indices: &mut Indices, entries: &[Bucket<K, V>]) {
    assert!(indices.capacity() - indices.len() >= entries.len());
    for entry in entries {
        indices.insert_unique(entry.hash.get(), indices.len(), |_| unreachable!());
    }
}

impl<K, V> Clone for IndexMapCore<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        let mut new = Self::new();
        new.clone_from(self);
        new
    }

    fn clone_from(&mut self, other: &Self) {
        self.indices.clone_from(&other.indices);
        if self.entries.capacity() < other.entries.len() {
            // If we must resize, match the indices capacity.
            let additional = other.entries.len() - self.entries.len();
            self.reserve_entries(additional);
        }
        self.entries.clone_from(&other.entries);
    }
}

impl<K, V> crate::Entries for IndexMapCore<K, V> {
    type Entry = Bucket<K, V>;

    #[inline]
    fn into_entries(self) -> Vec<Self::Entry> {
        self.entries
    }

    #[inline]
    fn as_entries(&self) -> &[Self::Entry] {
        &self.entries
    }

    #[inline]
    fn as_entries_mut(&mut self) -> &mut [Self::Entry] {
        &mut self.entries
    }

    fn with_entries<F>(&mut self, f: F)
    where
        F: FnOnce(&mut [Self::Entry]),
    {
        f(&mut self.entries);
        self.rebuild_hash_table();
    }
}

impl<K, V> IndexMapCore<K, V> {
    /// The maximum capacity before the `entries` allocation would exceed `isize::MAX`.
    const MAX_ENTRIES_CAPACITY: usize = (isize::MAX as usize) / mem::size_of::<Bucket<K, V>>();

    #[inline]
    pub(crate) const fn new() -> Self {
        IndexMapCore {
            indices: Indices::new(),
            entries: Vec::new(),
        }
    }

    #[inline]
    pub(crate) fn with_capacity(n: usize) -> Self {
        IndexMapCore {
            indices: Indices::with_capacity(n),
            entries: Vec::with_capacity(n),
        }
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.indices.len()
    }

    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        Ord::min(self.indices.capacity(), self.entries.capacity())
    }

    pub(crate) fn clear(&mut self) {
        self.indices.clear();
        self.entries.clear();
    }

    pub(crate) fn truncate(&mut self, len: usize) {
        if len < self.len() {
            self.erase_indices(len, self.entries.len());
            self.entries.truncate(len);
        }
    }

    pub(crate) fn drain<R>(&mut self, range: R) -> Drain<'_, Bucket<K, V>>
    where
        R: RangeBounds<usize>,
    {
        let range = simplify_range(range, self.entries.len());
        self.erase_indices(range.start, range.end);
        self.entries.drain(range)
    }

    #[cfg(feature = "rayon")]
    pub(crate) fn par_drain<R>(&mut self, range: R) -> rayon::vec::Drain<'_, Bucket<K, V>>
    where
        K: Send,
        V: Send,
        R: RangeBounds<usize>,
    {
        use rayon::iter::ParallelDrainRange;
        let range = simplify_range(range, self.entries.len());
        self.erase_indices(range.start, range.end);
        self.entries.par_drain(range)
    }

    pub(crate) fn split_off(&mut self, at: usize) -> Self {
        assert!(at <= self.entries.len());
        self.erase_indices(at, self.entries.len());
        let entries = self.entries.split_off(at);

        let mut indices = Indices::with_capacity(entries.len());
        insert_bulk_no_grow(&mut indices, &entries);
        Self { indices, entries }
    }

    /// Reserve capacity for `additional` more key-value pairs.
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.indices.reserve(additional, get_hash(&self.entries));
        // Only grow entries if necessary, since we also round up capacity.
        if additional > self.entries.capacity() - self.entries.len() {
            self.reserve_entries(additional);
        }
    }

    /// Reserve entries capacity, rounded up to match the indices
    fn reserve_entries(&mut self, additional: usize) {
        Self::_reserve_entries(&self.indices, &mut self.entries, additional);
    }

    fn _reserve_entries(indices: &Indices, entries: &mut Entries<K, V>, additional: usize) {
        // Use a soft-limit on the maximum capacity, but if the caller explicitly
        // requested more, do it and let them have the resulting panic.
        let new_capacity = Ord::min(indices.capacity(), Self::MAX_ENTRIES_CAPACITY);
        let try_add = new_capacity - entries.len();
        if try_add > additional && entries.try_reserve_exact(try_add).is_ok() {
            return;
        }
        entries.reserve_exact(additional);
    }

    /// Reserve capacity for `additional` more key-value pairs, without over-allocating.
    pub(crate) fn reserve_exact(&mut self, additional: usize) {
        self.indices.reserve(additional, get_hash(&self.entries));
        self.entries.reserve_exact(additional);
    }

    /// Try to reserve capacity for `additional` more key-value pairs.
    pub(crate) fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.indices
            .try_reserve(additional, get_hash(&self.entries))
            .map_err(TryReserveError::from_hashbrown)?;
        // Only grow entries if necessary, since we also round up capacity.
        if additional > self.entries.capacity() - self.entries.len() {
            self.try_reserve_entries(additional)
        } else {
            Ok(())
        }
    }

    /// Try to reserve entries capacity, rounded up to match the indices
    fn try_reserve_entries(&mut self, additional: usize) -> Result<(), TryReserveError> {
        // Use a soft-limit on the maximum capacity, but if the caller explicitly
        // requested more, do it and let them have the resulting error.
        let new_capacity = Ord::min(self.indices.capacity(), Self::MAX_ENTRIES_CAPACITY);
        let try_add = new_capacity - self.entries.len();
        if try_add > additional && self.entries.try_reserve_exact(try_add).is_ok() {
            return Ok(());
        }
        self.entries
            .try_reserve_exact(additional)
            .map_err(TryReserveError::from_alloc)
    }

    /// Try to reserve capacity for `additional` more key-value pairs, without over-allocating.
    pub(crate) fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.indices
            .try_reserve(additional, get_hash(&self.entries))
            .map_err(TryReserveError::from_hashbrown)?;
        self.entries
            .try_reserve_exact(additional)
            .map_err(TryReserveError::from_alloc)
    }

    /// Shrink the capacity of the map with a lower bound
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        self.indices
            .shrink_to(min_capacity, get_hash(&self.entries));
        self.entries.shrink_to(min_capacity);
    }

    /// Remove the last key-value pair
    pub(crate) fn pop(&mut self) -> Option<(K, V)> {
        if let Some(entry) = self.entries.pop() {
            let last = self.entries.len();
            erase_index(&mut self.indices, entry.hash, last);
            Some((entry.key, entry.value))
        } else {
            None
        }
    }

    /// Append a key-value pair to `entries`, *without* checking whether it already exists.
    fn push_entry(&mut self, hash: HashValue, key: K, value: V) {
        Self::_push_entry(&self.indices, &mut self.entries, hash, key, value);
    }

    fn _push_entry(
        indices: &Indices,
        entries: &mut Entries<K, V>,
        hash: HashValue,
        key: K,
        value: V,
    ) {
        if entries.len() == entries.capacity() {
            // Reserve our own capacity synced to the indices,
            // rather than letting `Vec::push` just double it.
            Self::_reserve_entries(indices, entries, 1);
        }
        entries.push(Bucket { hash, key, value });
    }

    /// Return the index in `entries` where an equivalent key can be found
    pub(crate) fn get_index_of<Q>(&self, hash: HashValue, key: &Q) -> Option<usize>
    where
        Q: ?Sized + Equivalent<K>,
    {
        let eq = equivalent(key, &self.entries);
        self.indices.find(hash.get(), eq).copied()
    }

    pub(crate) fn entry(&mut self, hash: HashValue, key: K) -> Entry<'_, K, V>
    where
        K: Eq,
    {
        let entries = &mut self.entries;
        let eq = equivalent(&key, entries);
        match self.indices.find_entry(hash.get(), eq) {
            Ok(index) => Entry::Occupied(OccupiedEntry {
                entries,
                index,
                key,
            }),
            Err(absent) => Entry::Vacant(VacantEntry {
                entries,
                indices: absent.into_table(),
                hash,
                key,
            }),
        }
    }

    pub(crate) fn insert_full(&mut self, hash: HashValue, key: K, value: V) -> (usize, Option<V>)
    where
        K: Eq,
    {
        let eq = equivalent(&key, &self.entries);
        let hasher = get_hash(&self.entries);
        match self.indices.entry(hash.get(), eq, hasher) {
            hash_table::Entry::Occupied(entry) => {
                let i = *entry.get();
                (i, Some(mem::replace(&mut self.entries[i].value, value)))
            }
            hash_table::Entry::Vacant(entry) => {
                let i = self.entries.len();
                entry.insert(i);
                self.push_entry(hash, key, value);
                debug_assert_eq!(self.indices.len(), self.entries.len());
                (i, None)
            }
        }
    }

    /// Remove an entry by shifting all entries that follow it
    pub(crate) fn shift_remove_full<Q>(&mut self, hash: HashValue, key: &Q) -> Option<(usize, K, V)>
    where
        Q: ?Sized + Equivalent<K>,
    {
        let eq = equivalent(key, &self.entries);
        match self.indices.find_entry(hash.get(), eq) {
            Ok(entry) => {
                let (index, _) = entry.remove();
                let (key, value) = self.shift_remove_finish(index);
                Some((index, key, value))
            }
            Err(_) => None,
        }
    }

    /// Remove an entry by shifting all entries that follow it
    pub(crate) fn shift_remove_index(&mut self, index: usize) -> Option<(K, V)> {
        match self.entries.get(index) {
            Some(entry) => {
                erase_index(&mut self.indices, entry.hash, index);
                Some(self.shift_remove_finish(index))
            }
            None => None,
        }
    }

    /// Remove an entry by shifting all entries that follow it
    ///
    /// The index should already be removed from `self.indices`.
    fn shift_remove_finish(&mut self, index: usize) -> (K, V) {
        Self::_shift_remove_finish(&mut self.indices, &mut self.entries, index)
    }

    fn _shift_remove_finish(
        indices: &mut Indices,
        entries: &mut Entries<K, V>,
        index: usize,
    ) -> (K, V) {
        // Correct indices that point to the entries that followed the removed entry.
        Self::_decrement_indices(indices, entries, index + 1, entries.len());

        // Use Vec::remove to actually remove the entry.
        let entry = entries.remove(index);
        (entry.key, entry.value)
    }

    /// Decrement all indices in the range `start..end`.
    ///
    /// The index `start - 1` should not exist in `self.indices`.
    /// All entries should still be in their original positions.
    fn decrement_indices(&mut self, start: usize, end: usize) {
        Self::_decrement_indices(&mut self.indices, &mut self.entries, start, end);
    }

    fn _decrement_indices(
        indices: &mut Indices,
        entries: &mut Entries<K, V>,
        start: usize,
        end: usize,
    ) {
        // Use a heuristic between a full sweep vs. a `find()` for every shifted item.
        let shifted_entries = &entries[start..end];
        if shifted_entries.len() > indices.capacity() / 2 {
            // Shift all indices in range.
            for i in indices {
                if start <= *i && *i < end {
                    *i -= 1;
                }
            }
        } else {
            // Find each entry in range to shift its index.
            for (i, entry) in (start..end).zip(shifted_entries) {
                update_index(indices, entry.hash, i, i - 1);
            }
        }
    }

    /// Increment all indices in the range `start..end`.
    ///
    /// The index `end` should not exist in `self.indices`.
    /// All entries should still be in their original positions.
    fn increment_indices(&mut self, start: usize, end: usize) {
        Self::_increment_indices(&mut self.indices, &mut self.entries, start, end);
    }

    fn _increment_indices(
        indices: &mut Indices,
        entries: &mut Entries<K, V>,
        start: usize,
        end: usize,
    ) {
        // Use a heuristic between a full sweep vs. a `find()` for every shifted item.
        let shifted_entries = &entries[start..end];
        if shifted_entries.len() > indices.capacity() / 2 {
            // Shift all indices in range.
            for i in indices {
                if start <= *i && *i < end {
                    *i += 1;
                }
            }
        } else {
            // Find each entry in range to shift its index, updated in reverse so
            // we never have duplicated indices that might have a hash collision.
            for (i, entry) in (start..end).zip(shifted_entries).rev() {
                update_index(indices, entry.hash, i, i + 1);
            }
        }
    }

    pub(super) fn move_index(&mut self, from: usize, to: usize) {
        let from_hash = self.entries[from].hash;
        if from != to {
            // Use a sentinel index so other indices don't collide.
            update_index(&mut self.indices, from_hash, from, usize::MAX);

            // Update all other indices and rotate the entry positions.
            if from < to {
                self.decrement_indices(from + 1, to + 1);
                self.entries[from..=to].rotate_left(1);
            } else if to < from {
                self.increment_indices(to, from);
                self.entries[to..=from].rotate_right(1);
            }

            // Change the sentinel index to its final position.
            update_index(&mut self.indices, from_hash, usize::MAX, to);
        }
    }

    pub(crate) fn swap_indices(&mut self, a: usize, b: usize) {
        // If they're equal and in-bounds, there's nothing to do.
        if a == b && a < self.entries.len() {
            return;
        }

        // We'll get a "nice" bounds-check from indexing `self.entries`,
        // and then we expect to find it in the table as well.
        let [ref_a, ref_b] = self
            .indices
            .get_many_mut(
                [self.entries[a].hash.get(), self.entries[b].hash.get()],
                move |i, &x| if i == 0 { x == a } else { x == b },
            )
            .expect("indices not found");

        mem::swap(ref_a, ref_b);
        self.entries.swap(a, b);
    }

    /// Remove an entry by swapping it with the last
    pub(crate) fn swap_remove_full<Q>(&mut self, hash: HashValue, key: &Q) -> Option<(usize, K, V)>
    where
        Q: ?Sized + Equivalent<K>,
    {
        let eq = equivalent(key, &self.entries);
        match self.indices.find_entry(hash.get(), eq) {
            Ok(entry) => {
                let (index, _) = entry.remove();
                let (key, value) = self.swap_remove_finish(index);
                Some((index, key, value))
            }
            Err(_) => None,
        }
    }

    /// Remove an entry by swapping it with the last
    pub(crate) fn swap_remove_index(&mut self, index: usize) -> Option<(K, V)> {
        match self.entries.get(index) {
            Some(entry) => {
                erase_index(&mut self.indices, entry.hash, index);
                Some(self.swap_remove_finish(index))
            }
            None => None,
        }
    }

    /// Finish removing an entry by swapping it with the last
    ///
    /// The index should already be removed from `self.indices`.
    fn swap_remove_finish(&mut self, index: usize) -> (K, V) {
        Self::_swap_remove_finish(&mut self.indices, &mut self.entries, index)
    }

    fn _swap_remove_finish(
        indices: &mut Indices,
        entries: &mut Entries<K, V>,
        index: usize,
    ) -> (K, V) {
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        let entry = entries.swap_remove(index);

        // correct index that points to the entry that had to swap places
        if let Some(entry) = entries.get(index) {
            // was not last element
            // examine new element in `index` and find it in indices
            let last = entries.len();
            update_index(indices, entry.hash, last, index);
        }

        (entry.key, entry.value)
    }

    /// Erase `start..end` from `indices`, and shift `end..` indices down to `start..`
    ///
    /// All of these items should still be at their original location in `entries`.
    /// This is used by `drain`, which will let `Vec::drain` do the work on `entries`.
    fn erase_indices(&mut self, start: usize, end: usize) {
        let (init, shifted_entries) = self.entries.split_at(end);
        let (start_entries, erased_entries) = init.split_at(start);

        let erased = erased_entries.len();
        let shifted = shifted_entries.len();
        let half_capacity = self.indices.capacity() / 2;

        // Use a heuristic between different strategies
        if erased == 0 {
            // Degenerate case, nothing to do
        } else if start + shifted < half_capacity && start < erased {
            // Reinsert everything, as there are few kept indices
            self.indices.clear();

            // Reinsert stable indices, then shifted indices
            insert_bulk_no_grow(&mut self.indices, start_entries);
            insert_bulk_no_grow(&mut self.indices, shifted_entries);
        } else if erased + shifted < half_capacity {
            // Find each affected index, as there are few to adjust

            // Find erased indices
            for (i, entry) in (start..).zip(erased_entries) {
                erase_index(&mut self.indices, entry.hash, i);
            }

            // Find shifted indices
            for ((new, old), entry) in (start..).zip(end..).zip(shifted_entries) {
                update_index(&mut self.indices, entry.hash, old, new);
            }
        } else {
            // Sweep the whole table for adjustments
            let offset = end - start;
            self.indices.retain(move |i| {
                if *i >= end {
                    *i -= offset;
                    true
                } else {
                    *i < start
                }
            });
        }

        debug_assert_eq!(self.indices.len(), start + shifted);
    }

    pub(crate) fn retain_in_order<F>(&mut self, mut keep: F)
    where
        F: FnMut(&mut K, &mut V) -> bool,
    {
        self.entries
            .retain_mut(|entry| keep(&mut entry.key, &mut entry.value));
        if self.entries.len() < self.indices.len() {
            self.rebuild_hash_table();
        }
    }

    fn rebuild_hash_table(&mut self) {
        self.indices.clear();
        insert_bulk_no_grow(&mut self.indices, &self.entries);
    }

    pub(crate) fn reverse(&mut self) {
        self.entries.reverse();

        // No need to save hash indices, can easily calculate what they should
        // be, given that this is an in-place reversal.
        let len = self.entries.len();
        for i in &mut self.indices {
            *i = len - *i - 1;
        }
    }
}

/// Entry for an existing key-value pair or a vacant location to
/// insert one.
pub enum Entry<'a, K, V> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Inserts the given default value in the entry if it is vacant and returns a mutable
    /// reference to it. Otherwise a mutable reference to an already existent value is returned.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Inserts the result of the `call` function in the entry if it is vacant and returns a mutable
    /// reference to it. Otherwise a mutable reference to an already existent value is returned.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert_with<F>(self, call: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(call()),
        }
    }

    /// Inserts the result of the `call` function with a reference to the entry's key if it is
    /// vacant, and returns a mutable reference to the new value. Otherwise a mutable reference to
    /// an already existent value is returned.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert_with_key<F>(self, call: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = call(&entry.key);
                entry.insert(value)
            }
        }
    }

    /// Gets a reference to the entry's key, either within the map if occupied,
    /// or else the new key that was used to find the entry.
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref entry) => entry.key(),
            Entry::Vacant(ref entry) => entry.key(),
        }
    }

    /// Return the index where the key-value pair exists or will be inserted.
    pub fn index(&self) -> usize {
        match *self {
            Entry::Occupied(ref entry) => entry.index(),
            Entry::Vacant(ref entry) => entry.index(),
        }
    }

    /// Modifies the entry if it is occupied.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut o) => {
                f(o.get_mut());
                Entry::Occupied(o)
            }
            x => x,
        }
    }

    /// Inserts a default-constructed value in the entry if it is vacant and returns a mutable
    /// reference to it. Otherwise a mutable reference to an already existent value is returned.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Entry::Vacant(ref v) => f.debug_tuple(stringify!(Entry)).field(v).finish(),
            Entry::Occupied(ref o) => f.debug_tuple(stringify!(Entry)).field(o).finish(),
        }
    }
}

/// A view into an occupied entry in a `IndexMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
// SAFETY: The lifetime of the map reference also constrains the raw bucket,
// which is essentially a raw pointer into the map indices.
pub struct OccupiedEntry<'a, K, V> {
    entries: &'a mut Entries<K, V>,
    index: hash_table::OccupiedEntry<'a, usize>,
    key: K,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the entry's key in the map.
    ///
    /// Note that this is not the key that was used to find the entry. There may be an observable
    /// difference if the key type has any distinguishing features outside of `Hash` and `Eq`, like
    /// extra fields or the memory address of an allocation.
    pub fn key(&self) -> &K {
        &self.entries[self.index()].key
    }

    /// Gets a reference to the entry's value in the map.
    pub fn get(&self) -> &V {
        &self.entries[self.index()].value
    }

    /// Gets a mutable reference to the entry's value in the map.
    ///
    /// If you need a reference which may outlive the destruction of the
    /// `Entry` value, see `into_mut`.
    pub fn get_mut(&mut self) -> &mut V {
        let index = self.index();
        &mut self.entries[index].value
    }

    /// Put the new key in the occupied entry's key slot
    pub(crate) fn replace_key(self) -> K {
        let index = self.index();
        let old_key = &mut self.entries[index].key;
        mem::replace(old_key, self.key)
    }

    /// Return the index of the key-value pair
    #[inline]
    pub fn index(&self) -> usize {
        *self.index.get()
    }

    /// Converts into a mutable reference to the entry's value in the map,
    /// with a lifetime bound to the map itself.
    pub fn into_mut(self) -> &'a mut V {
        let index = self.index();
        &mut self.entries[index].value
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the position of what used to be the last element!**
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove_entry(self) -> (K, V) {
        let (index, entry) = self.index.remove();
        IndexMapCore::_swap_remove_finish(entry.into_table(), self.entries, index)
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the
    /// elements that follow it, preserving their relative order.
    /// **This perturbs the index of all of those elements!**
    ///
    /// Computes in **O(n)** time (average).
    pub fn shift_remove_entry(self) -> (K, V) {
        let (index, entry) = self.index.remove();
        IndexMapCore::_shift_remove_finish(entry.into_table(), self.entries, index)
    }

    /// Sets the value of the entry to `value`, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// **NOTE:** This is equivalent to `.swap_remove()`.
    pub fn remove(self) -> V {
        self.swap_remove()
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the position of what used to be the last element!**
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove(self) -> V {
        self.swap_remove_entry().1
    }

    /// Remove the key, value pair stored in the map for this entry, and return the value.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the
    /// elements that follow it, preserving their relative order.
    /// **This perturbs the index of all of those elements!**
    ///
    /// Computes in **O(n)** time (average).
    pub fn shift_remove(self) -> V {
        self.shift_remove_entry().1
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// **NOTE:** This is equivalent to `.swap_remove_entry()`.
    pub fn remove_entry(self) -> (K, V) {
        self.swap_remove_entry()
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct(stringify!(OccupiedEntry))
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

/// A view into a vacant entry in a `IndexMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct VacantEntry<'a, K, V> {
    entries: &'a mut Entries<K, V>,
    indices: &'a mut Indices,
    hash: HashValue,
    key: K,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that was used to find the entry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Takes ownership of the key, leaving the entry vacant.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Return the index where the key-value pair will be inserted.
    pub fn index(&self) -> usize {
        self.indices.len()
    }

    /// Inserts the entry's key and the given value into the map, and returns a mutable reference
    /// to the value.
    pub fn insert(self, value: V) -> &'a mut V {
        let i = self.index();
        let Self {
            entries,
            indices,
            hash,
            key,
        } = self;
        indices.insert_unique(hash.get(), i, get_hash(entries));
        debug_assert_eq!(i, entries.len());
        IndexMapCore::_push_entry(indices, entries, hash, key, value);
        &mut entries[i].value
    }
}

impl<K: fmt::Debug, V> fmt::Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple(stringify!(VacantEntry))
            .field(self.key())
            .finish()
    }
}

#[test]
fn assert_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<IndexMapCore<i32, i32>>();
    assert_send_sync::<Entry<'_, i32, i32>>();
}
