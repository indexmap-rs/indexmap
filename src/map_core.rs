//! This is the core implementation that doesn't depend on the hasher at all.
//!
//! The methods of `IndexMapCore` don't use any properties (Hash / Eq) of K.
//!
//! It's cleaner to separate them out, then the compiler checks that we are not
//! using Hash + Eq at all in these methods.
//!
//! However, we should probably not let this show in the public API or docs.

#[cfg(not(has_std))]
use alloc::boxed::Box;
#[cfg(not(has_std))]
use std::vec::Vec;

use std::cmp::{max, Ordering};
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::mem::replace;
use std::ops::RangeFull;
use std::vec::Drain;

use util::{enumerate, ptrdistance};
use {Bucket, Entries, HashValue};

/// Trait for the "size class". Either u32 or u64 depending on the index
/// size needed to address an entry's index in self.core.entries.
trait Size {
    fn is_64_bit() -> bool;
    fn is_same_size<T: Size>() -> bool {
        Self::is_64_bit() == T::is_64_bit()
    }
}

impl Size for u32 {
    #[inline]
    fn is_64_bit() -> bool {
        false
    }
}

impl Size for u64 {
    #[inline]
    fn is_64_bit() -> bool {
        true
    }
}

/// Call self.method(args) with `::<u32>` or `::<u64>` depending on `self`
/// size class.
///
/// The u32 or u64 is *prepended* to the type parameter list!
macro_rules! dispatch_32_vs_64 {
    // self.methodname with other explicit type params,
    // size is prepended
    ($self_:ident . $method:ident::<$($t:ty),*>($($arg:expr),*)) => {
        if $self_.size_class_is_64bit() {
            $self_.$method::<u64, $($t),*>($($arg),*)
        } else {
            $self_.$method::<u32, $($t),*>($($arg),*)
        }
    };
    // self.methodname with only one type param, the size.
    ($self_:ident . $method:ident ($($arg:expr),*)) => {
        if $self_.size_class_is_64bit() {
            $self_.$method::<u64>($($arg),*)
        } else {
            $self_.$method::<u32>($($arg),*)
        }
    };
    // functionname with size_class_is_64bit as the first argument, only one
    // type param, the size.
    ($self_:ident => $function:ident ($($arg:expr),*)) => {
        if $self_.size_class_is_64bit() {
            $function::<u64>($($arg),*)
        } else {
            $function::<u32>($($arg),*)
        }
    };
}

/// A possibly truncated hash value.
///
#[derive(Debug)]
struct ShortHash<Sz>(usize, PhantomData<Sz>);

impl<Sz> ShortHash<Sz> {
    /// Pretend this is a full HashValue, which
    /// is completely ok w.r.t determining bucket index
    ///
    /// - Sz = u32: 32-bit hash is enough to select bucket index
    /// - Sz = u64: hash is not truncated
    fn into_hash(self) -> HashValue {
        HashValue(self.0)
    }
}

impl<Sz> Copy for ShortHash<Sz> {}
impl<Sz> Clone for ShortHash<Sz> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<Sz> PartialEq for ShortHash<Sz> {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
}

// Compare ShortHash == HashValue by truncating appropriately
// if applicable before the comparison
impl<Sz> PartialEq<HashValue> for ShortHash<Sz>
where
    Sz: Size,
{
    #[inline]
    fn eq(&self, rhs: &HashValue) -> bool {
        if Sz::is_64_bit() {
            self.0 == rhs.0
        } else {
            lo32(self.0 as u64) == lo32(rhs.0 as u64)
        }
    }
}
impl<Sz> From<ShortHash<Sz>> for HashValue {
    fn from(x: ShortHash<Sz>) -> Self {
        HashValue(x.0)
    }
}

/// `Pos` is stored in the `indices` array and it points to the index of a
/// `Bucket` in self.core.entries.
///
/// Pos can be interpreted either as a 64-bit index, or as a 32-bit index and
/// a 32-bit hash.
///
/// Storing the truncated hash next to the index saves loading the hash from the
/// entry, increasing the cache efficiency.
///
/// Note that the lower 32 bits of the hash is enough to compute desired
/// position and probe distance in a hash map with less than 2**32 buckets.
///
/// The IndexMap will simply query its **current raw capacity** to see what its
/// current size class is, and dispatch to the 32-bit or 64-bit lookup code as
/// appropriate. Only the growth code needs some extra logic to handle the
/// transition from one class to another
#[derive(Copy)]
struct Pos {
    index: u64,
}

impl Clone for Pos {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.pos() {
            Some(i) => write!(f, "Pos({} / {:x})", i, self.index),
            None => write!(f, "Pos(None)"),
        }
    }
}

impl Pos {
    #[inline]
    fn none() -> Self {
        Pos { index: !0 }
    }

    #[inline]
    fn is_none(&self) -> bool {
        self.index == !0
    }

    /// Return the index part of the Pos value inside `Some(_)` if the position
    /// is not none, otherwise return `None`.
    #[inline]
    fn pos(&self) -> Option<usize> {
        if self.index == !0 {
            None
        } else {
            Some(lo32(self.index as u64))
        }
    }

    /// Set the index part of the Pos value to `i`
    #[inline]
    fn set_pos<Sz>(&mut self, i: usize)
    where
        Sz: Size,
    {
        debug_assert!(!self.is_none());
        if Sz::is_64_bit() {
            self.index = i as u64;
        } else {
            self.index = i as u64 | ((self.index >> 32) << 32)
        }
    }

    #[inline]
    fn with_hash<Sz>(i: usize, hash: HashValue) -> Self
    where
        Sz: Size,
    {
        if Sz::is_64_bit() {
            Pos { index: i as u64 }
        } else {
            Pos {
                index: i as u64 | ((hash.0 as u64) << 32),
            }
        }
    }

    /// “Resolve” the Pos into a combination of its index value and
    /// a proxy value to the hash (whether it contains the hash or not
    /// depends on the size class of the hash map).
    #[inline]
    fn resolve<Sz>(&self) -> Option<(usize, ShortHashProxy<Sz>)>
    where
        Sz: Size,
    {
        if Sz::is_64_bit() {
            if !self.is_none() {
                Some((self.index as usize, ShortHashProxy::new(0)))
            } else {
                None
            }
        } else {
            if !self.is_none() {
                let (i, hash) = split_lo_hi(self.index);
                Some((i as usize, ShortHashProxy::new(hash as usize)))
            } else {
                None
            }
        }
    }

    /// Like resolve, but the Pos **must** be non-none. Return its index.
    #[inline]
    fn resolve_existing_index<Sz>(&self) -> usize
    where
        Sz: Size,
    {
        debug_assert!(
            !self.is_none(),
            "datastructure inconsistent: none where valid Pos expected"
        );
        if Sz::is_64_bit() {
            self.index as usize
        } else {
            let (i, _) = split_lo_hi(self.index);
            i as usize
        }
    }
}

#[inline]
fn lo32(x: u64) -> usize {
    (x & 0xFFFF_FFFF) as usize
}

// split into low, hi parts
#[inline]
fn split_lo_hi(x: u64) -> (u32, u32) {
    (x as u32, (x >> 32) as u32)
}

// Possibly contains the truncated hash value for an entry, depending on
// the size class.
struct ShortHashProxy<Sz>(usize, PhantomData<Sz>);

impl<Sz> ShortHashProxy<Sz>
where
    Sz: Size,
{
    fn new(x: usize) -> Self {
        ShortHashProxy(x, PhantomData)
    }

    /// Get the hash from either `self` or from a lookup into `entries`,
    /// depending on `Sz`.
    fn get_short_hash<K, V>(&self, entries: &[Bucket<K, V>], index: usize) -> ShortHash<Sz> {
        if Sz::is_64_bit() {
            ShortHash(entries[index].hash.0, PhantomData)
        } else {
            ShortHash(self.0, PhantomData)
        }
    }
}

#[inline]
fn usable_capacity(cap: usize) -> usize {
    cap - cap / 4
}

#[inline]
fn to_raw_capacity(n: usize) -> usize {
    n + n / 3
}

#[inline(always)]
fn desired_pos(mask: usize, hash: HashValue) -> usize {
    hash.0 & mask
}

/// The number of steps that `current` is forward of the desired position for hash
#[inline(always)]
fn probe_distance(mask: usize, hash: HashValue, current: usize) -> usize {
    current.wrapping_sub(desired_pos(mask, hash)) & mask
}

// this could not be captured in an efficient iterator
macro_rules! probe_loop {
    ($probe_var: ident < $len: expr, $body: expr) => {
        loop {
            if $probe_var < $len {
                $body
                $probe_var += 1;
            } else {
                $probe_var = 0;
            }
        }
    }
}

/// Find, in the indices, an entry that already exists at a known position
/// inside self.entries in the IndexMap.
///
/// This is effectively reverse lookup, from the entries into the hash buckets.
///
/// Return the probe index (into self.indices)
///
/// + indices: The self.indices of the map,
/// + hash: The full hash value from the bucket
/// + mask: self.mask.
/// + entry_index: The index of the entry in self.entries
fn find_existing_entry_at<Sz>(
    indices: &[Pos],
    hash: HashValue,
    mask: usize,
    entry_index: usize,
) -> usize
where
    Sz: Size,
{
    let mut probe = desired_pos(mask, hash);
    probe_loop!(probe < indices.len(), {
        // the entry *must* be present; if we hit a Pos::none this was not true
        // and there is a debug assertion in resolve_existing_index for that.
        let i = indices[probe].resolve_existing_index::<Sz>();
        if i == entry_index {
            return probe;
        }
    });
}

/// Core of the map that does not depend on S
pub(crate) struct IndexMapCore<K, V> {
    mask: usize,
    /// indices are the buckets. indices.len() == raw capacity
    indices: Box<[Pos]>,
    /// entries is a dense vec of entries in their order. entries.len() == len
    entries: Vec<Bucket<K, V>>,
}

impl<K, V> Clone for IndexMapCore<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        IndexMapCore {
            mask: self.mask,
            indices: self.indices.clone(),
            entries: self.entries.clone(),
        }
    }

    fn clone_from(&mut self, other: &Self) {
        self.mask = other.mask;
        self.indices.clone_from(&other.indices);
        self.entries.clone_from(&other.entries);
    }
}

impl<K, V> Entries for IndexMapCore<K, V> {
    type Entry = Bucket<K, V>;

    fn into_entries(self) -> Vec<Self::Entry> {
        self.entries
    }

    fn as_entries(&self) -> &[Self::Entry] {
        &self.entries
    }

    fn as_entries_mut(&mut self) -> &mut [Self::Entry] {
        &mut self.entries
    }

    fn with_entries<F>(&mut self, f: F)
    where
        F: FnOnce(&mut [Self::Entry]),
    {
        let side_index = self.save_hash_index();
        f(&mut self.entries);
        self.restore_hash_index(side_index);
    }
}

impl<K, V> IndexMapCore<K, V> {
    #[inline]
    pub(crate) fn new() -> Self {
        IndexMapCore {
            mask: 0,
            indices: Box::new([]),
            entries: Vec::new(),
        }
    }

    #[inline]
    pub(crate) fn with_capacity(n: usize) -> Self {
        let raw = to_raw_capacity(n);
        let raw_cap = max(raw.next_power_of_two(), 8);
        IndexMapCore {
            mask: raw_cap.wrapping_sub(1),
            indices: vec![Pos::none(); raw_cap].into_boxed_slice(),
            entries: Vec::with_capacity(usable_capacity(raw_cap)),
        }
    }

    // Return whether we need 32 or 64 bits to specify a bucket or entry index
    #[cfg(not(feature = "test_low_transition_point"))]
    fn size_class_is_64bit(&self) -> bool {
        usize::max_value() > u32::max_value() as usize
            && self.raw_capacity() >= u32::max_value() as usize
    }

    // for testing
    #[cfg(feature = "test_low_transition_point")]
    fn size_class_is_64bit(&self) -> bool {
        self.raw_capacity() >= 64
    }

    #[inline(always)]
    fn raw_capacity(&self) -> usize {
        self.indices.len()
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn capacity(&self) -> usize {
        usable_capacity(self.raw_capacity())
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.clear_indices();
    }

    pub(crate) fn drain(&mut self, range: RangeFull) -> Drain<Bucket<K, V>> {
        self.clear_indices();
        self.entries.drain(range)
    }

    // clear self.indices to the same state as "no elements"
    fn clear_indices(&mut self) {
        for pos in self.indices.iter_mut() {
            *pos = Pos::none();
        }
    }

    fn first_allocation(&mut self) {
        debug_assert_eq!(self.len(), 0);
        let raw_cap = 8usize;
        self.mask = raw_cap.wrapping_sub(1);
        self.indices = vec![Pos::none(); raw_cap].into_boxed_slice();
        self.entries = Vec::with_capacity(usable_capacity(raw_cap));
    }

    pub(crate) fn reserve_one(&mut self) {
        if self.len() == self.capacity() {
            dispatch_32_vs_64!(self.double_capacity());
        }
    }

    #[inline(never)]
    // `Sz` is *current* Size class, before grow
    fn double_capacity<Sz>(&mut self)
    where
        Sz: Size,
    {
        debug_assert!(self.raw_capacity() == 0 || self.len() > 0);
        if self.raw_capacity() == 0 {
            return self.first_allocation();
        }

        // find first ideally placed element -- start of cluster
        let mut first_ideal = 0;
        for (i, index) in enumerate(&*self.indices) {
            if let Some(pos) = index.pos() {
                if 0 == probe_distance(self.mask, self.entries[pos].hash, i) {
                    first_ideal = i;
                    break;
                }
            }
        }

        // visit the entries in an order where we can simply reinsert them
        // into self.indices without any bucket stealing.
        let new_raw_cap = self.indices.len() * 2;
        let old_indices = replace(
            &mut self.indices,
            vec![Pos::none(); new_raw_cap].into_boxed_slice(),
        );
        self.mask = new_raw_cap.wrapping_sub(1);

        // `Sz` is the old size class, and either u32 or u64 is the new
        for &pos in &old_indices[first_ideal..] {
            dispatch_32_vs_64!(self.reinsert_entry_in_order::<Sz>(pos));
        }

        for &pos in &old_indices[..first_ideal] {
            dispatch_32_vs_64!(self.reinsert_entry_in_order::<Sz>(pos));
        }
        let more = self.capacity() - self.len();
        self.entries.reserve_exact(more);
    }

    // write to self.indices
    // read from self.entries at `pos`
    //
    // reinserting rewrites all `Pos` entries anyway. This handles transitioning
    // from u32 to u64 size class if needed by using the two type parameters.
    fn reinsert_entry_in_order<SzNew, SzOld>(&mut self, pos: Pos)
    where
        SzNew: Size,
        SzOld: Size,
    {
        if let Some((i, hash_proxy)) = pos.resolve::<SzOld>() {
            // only if the size class is conserved can we use the short hash
            let entry_hash = if SzOld::is_same_size::<SzNew>() {
                hash_proxy.get_short_hash(&self.entries, i).into_hash()
            } else {
                self.entries[i].hash
            };
            // find first empty bucket and insert there
            let mut probe = desired_pos(self.mask, entry_hash);
            probe_loop!(probe < self.indices.len(), {
                if self.indices[probe].is_none() {
                    // empty bucket, insert here
                    self.indices[probe] = Pos::with_hash::<SzNew>(i, entry_hash);
                    return;
                }
            });
        }
    }

    pub(crate) fn pop_impl(&mut self) -> Option<(K, V)> {
        let (probe, found) = match self.as_entries().last() {
            Some(e) => self.find_existing_entry(e),
            None => return None,
        };
        debug_assert_eq!(found, self.entries.len() - 1);
        Some(self.swap_remove_found(probe, found))
    }

    fn insert_phase_1<'a, Sz, A>(&'a mut self, hash: HashValue, key: K, action: A) -> A::Output
    where
        Sz: Size,
        K: Eq,
        A: ProbeAction<'a, Sz, K, V>,
    {
        let mut probe = desired_pos(self.mask, hash);
        let mut dist = 0;
        debug_assert!(self.len() < self.raw_capacity());
        probe_loop!(probe < self.indices.len(), {
            if let Some((i, hash_proxy)) = self.indices[probe].resolve::<Sz>() {
                let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                // if existing element probed less than us, swap
                let their_dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                if their_dist < dist {
                    // robin hood: steal the spot if it's better for us
                    return action.steal(VacantEntry {
                        map: self,
                        hash: hash,
                        key: key,
                        probe: probe,
                    });
                } else if entry_hash == hash && self.entries[i].key == key {
                    return action.hit(OccupiedEntry {
                        map: self,
                        key: key,
                        probe: probe,
                        index: i,
                    });
                }
            } else {
                // empty bucket, insert here
                return action.empty(VacantEntry {
                    map: self,
                    hash: hash,
                    key: key,
                    probe: probe,
                });
            }
            dist += 1;
        });
    }

    /// phase 2 is post-insert where we forward-shift `Pos` in the indices.
    fn insert_phase_2<Sz>(&mut self, mut probe: usize, mut old_pos: Pos)
    where
        Sz: Size,
    {
        probe_loop!(probe < self.indices.len(), {
            let pos = &mut self.indices[probe];
            if pos.is_none() {
                *pos = old_pos;
                break;
            } else {
                old_pos = replace(pos, old_pos);
            }
        });
    }

    pub(crate) fn insert_full(&mut self, hash: HashValue, key: K, value: V) -> (usize, Option<V>)
    where
        K: Eq,
    {
        self.reserve_one();
        dispatch_32_vs_64!(self.insert_phase_1::<_>(hash, key, InsertValue(value)))
    }

    pub(crate) fn entry(&mut self, hash: HashValue, key: K) -> Entry<K, V>
    where
        K: Eq,
    {
        self.reserve_one();
        dispatch_32_vs_64!(self.insert_phase_1::<_>(hash, key, MakeEntry))
    }

    /// Return probe (indices) and position (entries)
    pub(crate) fn find_using<F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize)>
    where
        F: Fn(&Bucket<K, V>) -> bool,
    {
        dispatch_32_vs_64!(self.find_using_impl::<_>(hash, key_eq))
    }

    fn find_using_impl<Sz, F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize)>
    where
        F: Fn(&Bucket<K, V>) -> bool,
        Sz: Size,
    {
        debug_assert!(self.len() > 0);
        let mut probe = desired_pos(self.mask, hash);
        let mut dist = 0;
        probe_loop!(probe < self.indices.len(), {
            if let Some((i, hash_proxy)) = self.indices[probe].resolve::<Sz>() {
                let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                if dist > probe_distance(self.mask, entry_hash.into_hash(), probe) {
                    // give up when probe distance is too long
                    return None;
                } else if entry_hash == hash && key_eq(&self.entries[i]) {
                    return Some((probe, i));
                }
            } else {
                return None;
            }
            dist += 1;
        });
    }

    /// Find `entry` which is already placed inside self.entries;
    /// return its probe and entry index.
    pub(crate) fn find_existing_entry(&self, entry: &Bucket<K, V>) -> (usize, usize) {
        debug_assert!(self.len() > 0);

        let hash = entry.hash;
        let actual_pos = ptrdistance(&self.entries[0], entry);
        let probe = dispatch_32_vs_64!(self =>
            find_existing_entry_at(&self.indices, hash, self.mask, actual_pos));
        (probe, actual_pos)
    }

    /// Remove an entry by shifting all entries that follow it
    pub(crate) fn shift_remove_found(&mut self, probe: usize, found: usize) -> (K, V) {
        dispatch_32_vs_64!(self.shift_remove_found_impl(probe, found))
    }

    fn shift_remove_found_impl<Sz>(&mut self, probe: usize, found: usize) -> (K, V)
    where
        Sz: Size,
    {
        // index `probe` and entry `found` is to be removed
        // use Vec::remove, but then we need to update the indices that point
        // to all of the other entries that have to move
        self.indices[probe] = Pos::none();
        let entry = self.entries.remove(found);

        // correct indices that point to the entries that followed the removed entry.
        // use a heuristic between a full sweep vs. a `probe_loop!` for every shifted item.
        if self.indices.len() < (self.entries.len() - found) * 2 {
            // shift all indices greater than `found`
            for pos in self.indices.iter_mut() {
                if let Some((i, _)) = pos.resolve::<Sz>() {
                    if i > found {
                        // shift the index
                        pos.set_pos::<Sz>(i - 1);
                    }
                }
            }
        } else {
            // find each following entry to shift its index
            for (offset, entry) in enumerate(&self.entries[found..]) {
                let index = found + offset;
                let mut probe = desired_pos(self.mask, entry.hash);
                probe_loop!(probe < self.indices.len(), {
                    let pos = &mut self.indices[probe];
                    if let Some((i, _)) = pos.resolve::<Sz>() {
                        if i == index + 1 {
                            // found it, shift it
                            pos.set_pos::<Sz>(index);
                            break;
                        }
                    }
                });
            }
        }

        self.backward_shift_after_removal::<Sz>(probe);

        (entry.key, entry.value)
    }

    /// Remove an entry by swapping it with the last
    pub(crate) fn swap_remove_found(&mut self, probe: usize, found: usize) -> (K, V) {
        dispatch_32_vs_64!(self.swap_remove_found_impl(probe, found))
    }

    fn swap_remove_found_impl<Sz>(&mut self, probe: usize, found: usize) -> (K, V)
    where
        Sz: Size,
    {
        // index `probe` and entry `found` is to be removed
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        self.indices[probe] = Pos::none();
        let entry = self.entries.swap_remove(found);

        // correct index that points to the entry that had to swap places
        if let Some(entry) = self.entries.get(found) {
            // was not last element
            // examine new element in `found` and find it in indices
            let mut probe = desired_pos(self.mask, entry.hash);
            probe_loop!(probe < self.indices.len(), {
                let pos = &mut self.indices[probe];
                if let Some((i, _)) = pos.resolve::<Sz>() {
                    if i >= self.entries.len() {
                        // found it
                        pos.set_pos::<Sz>(found);
                        break;
                    }
                }
            });
        }

        self.backward_shift_after_removal::<Sz>(probe);

        (entry.key, entry.value)
    }

    fn backward_shift_after_removal<Sz>(&mut self, probe_at_remove: usize)
    where
        Sz: Size,
    {
        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        let mut last_probe = probe_at_remove;
        let mut probe = probe_at_remove + 1;
        probe_loop!(probe < self.indices.len(), {
            if let Some((i, hash_proxy)) = self.indices[probe].resolve::<Sz>() {
                let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                if probe_distance(self.mask, entry_hash.into_hash(), probe) > 0 {
                    self.indices[last_probe] = self.indices[probe];
                    self.indices[probe] = Pos::none();
                } else {
                    break;
                }
            } else {
                break;
            }
            last_probe = probe;
        });
    }

    pub(crate) fn retain_in_order<F>(&mut self, keep: F)
    where
        F: FnMut(&mut K, &mut V) -> bool,
    {
        dispatch_32_vs_64!(self.retain_in_order_impl::<_>(keep));
    }

    fn retain_in_order_impl<Sz, F>(&mut self, mut keep: F)
    where
        F: FnMut(&mut K, &mut V) -> bool,
        Sz: Size,
    {
        // Like Vec::retain in self.entries; for each removed key-value pair,
        // we clear its corresponding spot in self.indices, and run the
        // usual backward shift in self.indices.
        let len = self.entries.len();
        let mut n_deleted = 0;
        for i in 0..len {
            let will_keep;
            let hash;
            {
                let ent = &mut self.entries[i];
                hash = ent.hash;
                will_keep = keep(&mut ent.key, &mut ent.value);
            };
            let probe = find_existing_entry_at::<Sz>(&self.indices, hash, self.mask, i);
            if !will_keep {
                n_deleted += 1;
                self.indices[probe] = Pos::none();
                self.backward_shift_after_removal::<Sz>(probe);
            } else if n_deleted > 0 {
                self.indices[probe].set_pos::<Sz>(i - n_deleted);
                self.entries.swap(i - n_deleted, i);
            }
        }
        self.entries.truncate(len - n_deleted);
    }

    pub(crate) fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&K, &V, &K, &V) -> Ordering,
    {
        let side_index = self.save_hash_index();
        self.entries
            .sort_by(move |ei, ej| compare(&ei.key, &ei.value, &ej.key, &ej.value));
        self.restore_hash_index(side_index);
    }

    pub(crate) fn reverse(&mut self) {
        self.entries.reverse();

        // No need to save hash indices, can easily calculate what they should
        // be, given that this is an in-place reversal.
        dispatch_32_vs_64!(self => apply_new_index(&mut self.indices, self.entries.len()));

        fn apply_new_index<Sz>(indices: &mut [Pos], len: usize)
        where
            Sz: Size,
        {
            for pos in indices {
                if let Some((i, _)) = pos.resolve::<Sz>() {
                    pos.set_pos::<Sz>(len - i - 1);
                }
            }
        }
    }

    fn save_hash_index(&mut self) -> Vec<usize> {
        // Temporarily use the hash field in a bucket to store the old index.
        // Save the old hash values in `side_index`.  Then we can sort
        // `self.entries` in place.
        Vec::from_iter(
            enumerate(&mut self.entries).map(|(i, elt)| replace(&mut elt.hash, HashValue(i)).get()),
        )
    }

    fn restore_hash_index(&mut self, mut side_index: Vec<usize>) {
        // Write back the hash values from side_index and fill `side_index` with
        // a mapping from the old to the new index instead.
        for (i, ent) in enumerate(&mut self.entries) {
            let old_index = ent.hash.get();
            ent.hash = HashValue(replace(&mut side_index[old_index], i));
        }

        // Apply new index to self.indices
        dispatch_32_vs_64!(self => apply_new_index(&mut self.indices, &side_index));

        fn apply_new_index<Sz>(indices: &mut [Pos], new_index: &[usize])
        where
            Sz: Size,
        {
            for pos in indices {
                if let Some((i, _)) = pos.resolve::<Sz>() {
                    pos.set_pos::<Sz>(new_index[i]);
                }
            }
        }
    }

    pub(crate) fn debug_entries(&self, f: &mut fmt::Formatter) -> fmt::Result
    where
        K: fmt::Debug,
    {
        for (i, index) in enumerate(&*self.indices) {
            write!(f, "{}: {:?}", i, index)?;
            if let Some(pos) = index.pos() {
                let hash = self.entries[pos].hash;
                let key = &self.entries[pos].key;
                let desire = desired_pos(self.mask, hash);
                write!(
                    f,
                    ", desired={}, probe_distance={}, key={:?}",
                    desire,
                    probe_distance(self.mask, hash, i),
                    key
                )?;
            }
            writeln!(f)?;
        }
        writeln!(
            f,
            "cap={}, raw_cap={}, entries.cap={}",
            self.capacity(),
            self.raw_capacity(),
            self.entries.capacity()
        )?;
        Ok(())
    }
}

trait ProbeAction<'a, Sz: Size, K, V>: Sized {
    type Output;
    // handle an occupied spot in the map
    fn hit(self, entry: OccupiedEntry<'a, K, V>) -> Self::Output;
    // handle an empty spot in the map
    fn empty(self, entry: VacantEntry<'a, K, V>) -> Self::Output;
    // robin hood: handle a spot that you should steal because it's better for you
    fn steal(self, entry: VacantEntry<'a, K, V>) -> Self::Output;
}

struct InsertValue<V>(V);

impl<'a, Sz: Size, K, V> ProbeAction<'a, Sz, K, V> for InsertValue<V> {
    type Output = (usize, Option<V>);

    fn hit(self, entry: OccupiedEntry<'a, K, V>) -> Self::Output {
        let old = replace(&mut entry.map.entries[entry.index].value, self.0);
        (entry.index, Some(old))
    }

    fn empty(self, entry: VacantEntry<'a, K, V>) -> Self::Output {
        let pos = &mut entry.map.indices[entry.probe];
        let index = entry.map.entries.len();
        *pos = Pos::with_hash::<Sz>(index, entry.hash);
        entry.map.entries.push(Bucket {
            hash: entry.hash,
            key: entry.key,
            value: self.0,
        });
        (index, None)
    }

    fn steal(self, entry: VacantEntry<'a, K, V>) -> Self::Output {
        let index = entry.map.entries.len();
        entry.insert_impl::<Sz>(self.0);
        (index, None)
    }
}

struct MakeEntry;

impl<'a, Sz: Size, K: 'a, V: 'a> ProbeAction<'a, Sz, K, V> for MakeEntry {
    type Output = Entry<'a, K, V>;

    fn hit(self, entry: OccupiedEntry<'a, K, V>) -> Self::Output {
        Entry::Occupied(entry)
    }

    fn empty(self, entry: VacantEntry<'a, K, V>) -> Self::Output {
        Entry::Vacant(entry)
    }

    fn steal(self, entry: VacantEntry<'a, K, V>) -> Self::Output {
        Entry::Vacant(entry)
    }
}

/// Entry for an existing key-value pair or a vacant location to
/// insert one.
pub enum Entry<'a, K: 'a, V: 'a> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

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

impl<'a, K: 'a + fmt::Debug, V: 'a + fmt::Debug> fmt::Debug for Entry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    map: &'a mut IndexMapCore<K, V>,
    key: K,
    probe: usize,
    index: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }
    pub fn get(&self) -> &V {
        &self.map.entries[self.index].value
    }
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map.entries[self.index].value
    }

    /// Put the new key in the occupied entry's key slot
    pub(crate) fn replace_key(self) -> K {
        let old_key = &mut self.map.entries[self.index].key;
        replace(old_key, self.key)
    }

    /// Return the index of the key-value pair
    pub fn index(&self) -> usize {
        self.index
    }
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map.entries[self.index].value
    }

    /// Sets the value of the entry to `value`, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        replace(self.get_mut(), value)
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
    /// the postion of what used to be the last element!**
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

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the postion of what used to be the last element!**
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove_entry(self) -> (K, V) {
        self.map.swap_remove_found(self.probe, self.index)
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the
    /// elements that follow it, preserving their relative order.
    /// **This perturbs the index of all of those elements!**
    ///
    /// Computes in **O(n)** time (average).
    pub fn shift_remove_entry(self) -> (K, V) {
        self.map.shift_remove_found(self.probe, self.index)
    }
}

impl<'a, K: 'a + fmt::Debug, V: 'a + fmt::Debug> fmt::Debug for OccupiedEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    map: &'a mut IndexMapCore<K, V>,
    key: K,
    hash: HashValue,
    probe: usize,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }
    pub fn into_key(self) -> K {
        self.key
    }
    /// Return the index where the key-value pair will be inserted.
    pub fn index(&self) -> usize {
        self.map.len()
    }
    pub fn insert(self, value: V) -> &'a mut V {
        if self.map.size_class_is_64bit() {
            self.insert_impl::<u64>(value)
        } else {
            self.insert_impl::<u32>(value)
        }
    }

    fn insert_impl<Sz>(self, value: V) -> &'a mut V
    where
        Sz: Size,
    {
        let index = self.map.entries.len();
        self.map.entries.push(Bucket {
            hash: self.hash,
            key: self.key,
            value,
        });
        let old_pos = Pos::with_hash::<Sz>(index, self.hash);
        self.map.insert_phase_2::<Sz>(self.probe, old_pos);
        &mut { self.map }.entries[index].value
    }
}

impl<'a, K: 'a + fmt::Debug, V: 'a> fmt::Debug for VacantEntry<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple(stringify!(VacantEntry))
            .field(self.key())
            .finish()
    }
}
