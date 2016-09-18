
#![doc(html_root_url = "https://docs.rs/ordermap/0.1/")]

mod macros;
mod util;

use std::hash::Hash;
use std::hash::BuildHasher;
use std::hash::Hasher;
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;

use std::cmp::max;
use std::fmt;
use std::mem;
use std::mem::{swap, replace};
use std::marker::PhantomData;

use util::{second, ptr_eq, enumerate};

fn hash_elem_using<B: BuildHasher, K: ?Sized + Hash>(build: &B, k: &K) -> HashValue {
    let mut h = build.build_hasher();
    k.hash(&mut h);
    HashValue(h.finish() as usize)
}

/// Hash value newtype. Not larger than usize, since anything larger
/// isn't used for selecting position anyway.
#[derive(Copy, Debug)]
struct HashValue(usize);

impl Clone for HashValue {
    #[inline]
    fn clone(&self) -> Self { *self }
}
impl PartialEq for HashValue {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
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

impl<Sz> Copy for ShortHash<Sz> { }
impl<Sz> Clone for ShortHash<Sz> {
    #[inline]
    fn clone(&self) -> Self { *self }
}

impl<Sz> PartialEq for ShortHash<Sz> {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
}

// Compare ShortHash == HashValue by truncating appropriately
// if applicable before the comparison
impl<Sz> PartialEq<HashValue> for ShortHash<Sz> where Sz: Size {
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
    fn from(x: ShortHash<Sz>) -> Self { HashValue(x.0) }
}

/// `Pos` is stored in the `indices` array and it points to the index of an
/// `Entry` in self.entries.
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
/// The OrderMap will simply query its **current raw capacity** to see what its
/// current size class is, and dispatch to the 32-bit or 64-bit lookup code as
/// appropriate. Only the growth code needs some extra logic to handle the
/// transition from one class to another
#[derive(Copy)]
struct Pos {
    index: u64,
}

impl Clone for Pos {
    #[inline(always)]
    fn clone(&self) -> Self { *self }
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
    fn none() -> Self { Pos { index: !0 } }

    #[inline]
    fn is_none(&self) -> bool { self.index == !0 }

    #[inline]
    fn pos(&self) -> Option<usize> {
        if self.index == !0 { None } else { Some(lo32(self.index as u64)) }
    }

    #[inline]
    fn with_hash<Sz>(i: usize, hash: HashValue) -> Self
        where Sz: Size
    {
        if Sz::is_64_bit() {
            Pos {
                index: i as u64,
            }
        } else {
            Pos {
                index: (i | (lo32(hash.0 as u64) << 32)) as u64
            }
        }
    }

    #[inline]
    fn resolve<Sz>(&self) -> Option<(usize, ShortHashProxy<Sz>)>
        where Sz: Size
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
}

#[inline]
fn lo32(x: u64) -> usize { (x & 0xFFFF_FFFF) as usize }

// split into low, hi parts
#[inline]
fn split_lo_hi(x: u64) -> (u32, u32) { (x as u32, (x >> 32) as u32) }

// Possibly contains the truncated hash value for an entry, depending on
// the size class.
struct ShortHashProxy<Sz>(usize, PhantomData<Sz>);

impl<Sz> ShortHashProxy<Sz>
    where Sz: Size
{
    fn new(x: usize) -> Self {
        ShortHashProxy(x, PhantomData)
    }

    /// Get the hash from either `self` or from a lookup into `entries`,
    /// depending on `Sz`.
    fn get_short_hash<K, V>(&self, entries: &[Entry<K, V>], index: usize) -> ShortHash<Sz> {
        if Sz::is_64_bit() {
            ShortHash(entries[index].hash.0, PhantomData)
        } else {
            ShortHash(self.0, PhantomData)
        }
    }
}

/// A hash map that preserves insertion order of the key-value pairs.
///
/// The key-value pairs have a consistent order that is determined by
/// the sequence of insertion and removal calls on the map. The order does
/// not depend on the keys or the hash function at all.
///
/// All iterators traverse the map in the same order.
#[derive(Clone)]
pub struct OrderMap<K, V, S = RandomState> {
    mask: usize,
    /// indices are the buckets. indices.len() == raw capacity
    indices: Vec<Pos>,
    /// entries is a dense vec of entries in their order. entries.len() == len
    entries: Vec<Entry<K, V>>,
    hash_builder: S,
}

#[derive(Copy, Clone, Debug)]
struct Entry<K, V> {
    hash: HashValue,
    key: K,
    value: V,
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

enum Inserted {
    Done,
    AlreadyExists,
    RobinHood {
        probe: usize,
        old_pos: Pos,
        dist: usize,
    }
}

impl<K, V, S> fmt::Debug for OrderMap<K, V, S>
    where K: fmt::Debug + Hash + Eq,
          V: fmt::Debug,
          S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(f.debug_map().entries(self.iter()).finish());
        try!(writeln!(f, ""));
        for (i, index) in enumerate(&self.indices) {
            try!(write!(f, "{}: {:?}", i, index));
            if let Some(pos) = index.pos() {
                let hash = self.entries[pos].hash;
                let key = &self.entries[pos].key;
                let desire = desired_pos(self.mask, hash);
                try!(writeln!(f, ", desired={}, probe_distance={}, key={:?}",
                              desire,
                              probe_distance(self.mask, hash, i),
                              key));
            }
            try!(writeln!(f, ""));
        }
        try!(writeln!(f, "cap={}, raw_cap={}, entries.cap={}",
                      self.capacity(),
                      self.raw_capacity(),
                      self.entries.capacity()));
        Ok(())
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

impl<K, V> OrderMap<K, V> {
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    pub fn with_capacity(n: usize) -> Self {
        Self::with_capacity_and_hasher(n, <_>::default())
    }
}

impl<K, V, S> OrderMap<K, V, S>
{
    pub fn with_capacity_and_hasher(n: usize, hash_builder: S) -> Self
        where S: BuildHasher
    {
        if n == 0 {
            OrderMap {
                mask: 0,
                indices: Vec::new(),
                entries: Vec::new(),
                hash_builder: hash_builder,
            }
        } else {
            let raw = to_raw_capacity(n);
            let raw_cap = max(raw.next_power_of_two(), 8);
            OrderMap {
                mask: raw_cap.wrapping_sub(1),
                indices: vec![Pos::none(); raw_cap],
                entries: Vec::with_capacity(usable_capacity(raw_cap)),
                hash_builder: hash_builder,
            }
        }
    }

    pub fn len(&self) -> usize { self.entries.len() }

    // Return whether we need 32 or 64 bits to specify a bucket or entry index
    #[cfg(not(feature = "test_low_transition_point"))]
    fn size_class_is_64bit(&self) -> bool {
        usize::max_value() > u32::max_value() as usize &&
            self.raw_capacity() >= u32::max_value() as usize
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

    pub fn capacity(&self) -> usize {
        usable_capacity(self.raw_capacity())
    }
}

/// Trait for the "size class". Either u32 or u64 depending on the index
/// size needed to address an entry's indes in self.entries.
trait Size {
    fn is_64_bit() -> bool;
    fn is_same_size<T>() -> bool
        where Self: Sized
    {
        mem::size_of::<T>() == mem::size_of::<Self>()
    }
}

impl Size for u32 {
    #[inline]
    fn is_64_bit() -> bool { false }
}

impl Size for u64 {
    #[inline]
    fn is_64_bit() -> bool { true }
}

/// Call self.method(args) with `::<u32>` or `::<u64>` depending on `self`
/// size class.
///
/// The u32 or u64 is *prepended* to the type parameter list!
macro_rules! dispatch_32_vs_64 {
    ($self_:ident . $method:ident::<$($t:ty),*>($($arg:expr),*)) => {
        if $self_.size_class_is_64bit() {
            $self_.$method::<u64, $($t),*>($($arg),*)
        } else {
            $self_.$method::<u32, $($t),*>($($arg),*)
        }
    };
    ($self_:ident . $method:ident ($($arg:expr),*)) => {
        if $self_.size_class_is_64bit() {
            $self_.$method::<u64>($($arg),*)
        } else {
            $self_.$method::<u32>($($arg),*)
        }
    };
}



impl<K, V, S> OrderMap<K, V, S>
    where K: Eq + Hash,
          S: BuildHasher,
{
    pub fn clear(&mut self) {
        self.entries.clear();
        for pos in &mut self.indices {
            *pos = Pos::none();
        }
    }

    // First phase: Look for the preferred location for key.
    //
    // We will know if `key` is already in the map, before we need to insert it.
    // When we insert they key, it might be that we need to continue displacing
    // entries (robin hood hashing), in which case Inserted::RobinHood is returned
    fn insert_phase_1<Sz>(&mut self, key: K, value: V) -> Inserted
        where Sz: Size
    {
        let hash = hash_elem_using(&self.hash_builder, &key);
        let mut probe = desired_pos(self.mask, hash);
        let mut dist = 0;
        let insert_kind;
        debug_assert!(self.len() < self.raw_capacity());
        probe_loop!(probe < self.indices.len(), {
            if let Some((i, hash_proxy)) = self.indices[probe].resolve::<Sz>() {
                let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                // if existing element probed less than us, swap
                let their_dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                if their_dist < dist {
                    // robin hood: steal the spot if it's better for us
                    let index = self.entries.len();
                    let mut pos = Pos::with_hash::<Sz>(index, hash);
                    swap(&mut pos, &mut self.indices[probe]);
                    insert_kind = Inserted::RobinHood {
                        probe: probe,
                        old_pos: pos,
                        dist: their_dist,
                    };
                    break;
                } else if entry_hash == hash && self.entries[i].key == key {
                    return Inserted::AlreadyExists;
                }
            } else {
                // empty bucket, insert here
                let index = self.entries.len();
                self.indices[probe] = Pos::with_hash::<Sz>(index, hash);
                insert_kind = Inserted::Done;
                break;
            }
            dist += 1;
        });
        self.entries.push(Entry { hash: hash, key: key, value: value });
        insert_kind
    }

    fn insert_phase_2<Sz>(&mut self, mut probe: usize, mut old_pos: Pos, mut dist: usize)
        where Sz: Size
    {
        probe_loop!(probe < self.indices.len(), {
            if let Some((i, hash_proxy)) = self.indices[probe].resolve::<Sz>() {
                let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                // if existing element probed less than us, swap
                let their_dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                if their_dist < dist {
                    swap(&mut old_pos, &mut self.indices[probe]);
                    dist = their_dist;
                }
            } else {
                self.indices[probe] = old_pos;
                break;
            }
            dist += 1;
        });
    }

    fn first_allocation(&mut self) {
        debug_assert_eq!(self.len(), 0);
        let raw_cap = 8usize;
        self.mask = raw_cap.wrapping_sub(1);
        self.indices = vec![Pos::none(); raw_cap];
        self.entries = Vec::with_capacity(usable_capacity(raw_cap));
    }

    #[inline(never)]
    // `Sz` is *current* Size class, before grow
    fn double_capacity<Sz>(&mut self)
        where Sz: Size
    {
        debug_assert!(self.raw_capacity() == 0 || self.len() > 0);
        if self.raw_capacity() == 0 {
            return self.first_allocation();
        }

        // find first ideally placed element -- start of cluster
        let mut first_ideal = 0;
        for (i, index) in enumerate(&self.indices) {
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
        let old_indices = replace(&mut self.indices, vec![Pos::none(); new_raw_cap]);
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
    // read from self.entries at `index`
    //
    // reinserting rewrites all `Pos` entries anyway. This handles transitioning
    // from u32 to u64 size class automatically, just by using the two type
    // parameters.
    fn reinsert_entry_in_order<SzNew, SzOld>(&mut self, pos: Pos)
        where SzNew: Size,
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
                if let Some(_) = self.indices[probe].resolve::<SzNew>() {
                    /* nothing */
                } else {
                    // empty bucket, insert here
                    self.indices[probe] = Pos::with_hash::<SzNew>(i, entry_hash);
                    return;
                }
            });
        }
    }

    fn reserve_one(&mut self) {
        if self.len() == self.capacity() {
            dispatch_32_vs_64!(self.double_capacity());
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.reserve_one();
        if self.size_class_is_64bit() {
            match self.insert_phase_1::<u64>(key, value) {
                Inserted::AlreadyExists | Inserted::Done => { }
                Inserted::RobinHood { probe, old_pos, dist } => {
                    self.insert_phase_2::<u64>(probe, old_pos, dist);
                }
            }
        } else {
            match self.insert_phase_1::<u32>(key, value) {
                Inserted::AlreadyExists | Inserted::Done => { }
                Inserted::RobinHood { probe, old_pos, dist } => {
                    self.insert_phase_2::<u32>(probe, old_pos, dist);
                }
            }
        }

    }

    /// Return an iterator over the keys of the map, in their order
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            iter: self.entries.iter()
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.entries.iter()
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.entries.iter_mut()
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair(key).map(second)
    }

    pub fn get_pair<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if let Some((_, found)) = self.find(key) {
            let entry = &self.entries[found];
            Some((&entry.key, &entry.value))
        } else {
            None
        }
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair_mut(key).map(second)
    }

    pub fn get_pair_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<(&mut K, &mut V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if let Some((_, found)) = self.find(key) {
            let entry = &mut self.entries[found];
            Some((&mut entry.key, &mut entry.value))
        } else {
            None
        }
    }

    /// Return probe (indices) and position (entries)
    fn find<Q: ?Sized>(&self, key: &Q) -> Option<(usize, usize)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if self.len() == 0 { return None; }
        let h = hash_elem_using(&self.hash_builder, &key);
        self.find_using(h, move |entry| { *entry.key.borrow() == *key })
    }

    /// Remove the key-value pair equivalent to `key` and return
    /// its value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the postion of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    pub fn swap_remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.swap_remove_pair(key).map(second)
    }

    /// Remove the key-value pair equivalent to `key` and return it.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the postion of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    pub fn swap_remove_pair<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        let (probe, found) = match self.find(key) {
            None => return None,
            Some(t) => t,
        };
        self.remove_found(probe, found)
    }

    /// Remove the last key-value pair
    pub fn pop(&mut self) -> Option<(K, V)> {
        self.pop_impl()
    }
}

// Methods that don't use any properties (Hash / Eq) of K.
//
// It's cleaner to separate them out, then the compiler checks that we are not
// using Hash + Eq at all in these methods.
//
// However, we should probably not let this show in the public API or docs.
impl<K, V, S> OrderMap<K, V, S> {
    fn pop_impl(&mut self) -> Option<(K, V)> {
        let (probe, found) = match self.entries.last()
            .and_then(|e| self.find_existing_entry(e))
        {
            None => return None,
            Some(t) => t,
        };
        debug_assert_eq!(found, self.entries.len() - 1);
        self.remove_found(probe, found)
    }

    /// Return probe (indices) and position (entries)
    fn find_using<F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize)>
        where F: Fn(&Entry<K, V>) -> bool,
    {
        dispatch_32_vs_64!(self.find_using_impl::<_>(hash, key_eq))
    }

    fn find_using_impl<Sz, F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize)>
        where F: Fn(&Entry<K, V>) -> bool,
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

    fn find_existing_entry(&self, entry: &Entry<K, V>) -> Option<(usize, usize)>
    {
        if self.len() == 0 { return None; }
        self.find_using(entry.hash, move |other_ent| ptr_eq(entry, other_ent))
    }

    fn remove_found(&mut self, probe: usize, found: usize) -> Option<(K, V)> {
        dispatch_32_vs_64!(self.remove_found_impl(probe, found))
    }

    fn remove_found_impl<Sz>(&mut self, probe: usize, found: usize) -> Option<(K, V)>
        where Sz: Size
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
                if let Some((i, _)) = self.indices[probe].resolve::<Sz>() {
                    if i >= self.entries.len() {
                        // found it
                        self.indices[probe] = Pos::with_hash::<Sz>(found, entry.hash);
                        break;
                    }
                }
            });
        }
        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        if self.len() > 0 {
            let mut last_probe = probe;
            let mut probe = probe + 1;
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

        Some((entry.key, entry.value))
    }

}

use std::slice::Iter as SliceIter;
use std::slice::IterMut as SliceIterMut;
use std::vec::IntoIter as VecIntoIter;

pub struct Keys<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next().map(|ent| &ent.key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        self.iter.next_back().map(|ent| &ent.key)
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| (&e.key, &e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|e| (&e.key, &e.value))
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: SliceIterMut<'a, Entry<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| (&e.key, &mut e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|e| (&e.key, &mut e.value))
    }
}

pub struct IntoIter<K, V> {
    iter: VecIntoIter<Entry<K, V>>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| (e.key, e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|e| (e.key, e.value))
    }
}

impl<'a, K, V, S> IntoIterator for &'a OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a mut OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V, S> IntoIterator for OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.entries.into_iter(),
        }
    }
}

use std::ops::{Index, IndexMut};

impl<'a, K, V, Q: ?Sized, S> Index<&'a Q> for OrderMap<K, V, S>
    where K: Eq + Hash,
          K: Borrow<Q>,
          Q: Eq + Hash,
          S: BuildHasher,
{
    type Output = V;
    fn index(&self, key: &'a Q) -> &V {
        if let Some(v) = self.get(key) {
            v
        } else {
            panic!("OrderMap: key not found")
        }
    }
}

/// Mutable indexing allows changing / updating values of key-value
/// pairs that are already present.
///
/// You can **not** insert new pairs with index syntax, use `.insert()`.
impl<'a, K, V, Q: ?Sized, S> IndexMut<&'a Q> for OrderMap<K, V, S>
    where K: Eq + Hash,
          K: Borrow<Q>,
          Q: Eq + Hash,
          S: BuildHasher,
{
    fn index_mut(&mut self, key: &'a Q) -> &mut V {
        if let Some(v) = self.get_mut(key) {
            v
        } else {
            panic!("OrderMap: key not found")
        }
    }
}

use std::iter::FromIterator;

impl<K, V, S> FromIterator<(K, V)> for OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iterable: I) -> Self {
        let iter = iterable.into_iter();
        let (low, _) = iter.size_hint();
        let mut map = Self::with_capacity_and_hasher(low, <_>::default());
        for (k, v) in iter { map.insert(k, v); }
        map
    }
}

impl<K, V, S> Extend<(K, V)> for OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item=(K, V)>>(&mut self, iterable: I) {
        for (k, v) in iterable { self.insert(k, v); }
    }
}

impl<K, V, S> Default for OrderMap<K, V, S>
    where S: BuildHasher + Default,
{
    fn default() -> Self {
        Self::with_capacity_and_hasher(0, S::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use util::enumerate;

    #[test]
    fn it_works() {
        let mut map = OrderMap::new();
        map.insert(1, ());
        map.insert(1, ());
        assert_eq!(map.len(), 1);
        assert!(map.get(&1).is_some());
    }

    #[test]
    fn new() {
        let map = OrderMap::<String, String>::new();
        println!("{:?}", map);
        assert_eq!(map.capacity(), 0);
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn insert() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5];
        let not_present = [1, 3, 6, 9, 10];
        let mut map = OrderMap::with_capacity(insert.len());

        for (i, &elt) in enumerate(&insert) {
            assert_eq!(map.len(), i);
            map.insert(elt, elt);
            assert_eq!(map.len(), i + 1);
            assert_eq!(map.get(&elt), Some(&elt));
            assert_eq!(map[&elt], elt);
        }
        println!("{:?}", map);

        for &elt in &not_present {
            assert!(map.get(&elt).is_none());
        }
    }

    #[test]
    fn insert_2() {
        let mut map = OrderMap::with_capacity(16);

        let mut keys = vec![];
        keys.extend(0..16);
        keys.extend(128..267);

        for &i in &keys {
            let old_map = map.clone();
            map.insert(i, ());
            for key in old_map.keys() {
                if !map.get(key).is_some() {
                    println!("old_map: {:?}", old_map);
                    println!("map: {:?}", map);
                    panic!("did not find {} in map", key);
                }
            }
        }

        for &i in &keys {
            assert!(map.get(&i).is_some(), "did not find {}", i);
        }
    }

    #[test]
    fn insert_order() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderMap::new();

        for &elt in &insert {
            map.insert(elt, ());
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn grow() {
        let insert = [0, 4, 2, 12, 8, 7, 11];
        let not_present = [1, 3, 6, 9, 10];
        let mut map = OrderMap::with_capacity(insert.len());


        for (i, &elt) in enumerate(&insert) {
            assert_eq!(map.len(), i);
            map.insert(elt, elt);
            assert_eq!(map.len(), i + 1);
            assert_eq!(map.get(&elt), Some(&elt));
            assert_eq!(map[&elt], elt);
        }

        println!("{:?}", map);
        for &elt in &insert {
            map.insert(elt * 10, elt);
        }
        for &elt in &insert {
            map.insert(elt * 100, elt);
        }
        for (i, &elt) in insert.iter().cycle().enumerate().take(100) {
            map.insert(elt * 100 + i as i32, elt);
        }
        println!("{:?}", map);
        for &elt in &not_present {
            assert!(map.get(&elt).is_none());
        }
    }

    #[test]
    fn remove() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderMap::new();

        for &elt in &insert {
            map.insert(elt, elt);
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }

        let remove_fail = [99, 77];
        let remove = [4, 12, 8, 7];

        for &key in &remove_fail {
            assert!(map.swap_remove_pair(&key).is_none());
        }
        println!("{:?}", map);
        for &key in &remove {
        //println!("{:?}", map);
            assert_eq!(map.swap_remove_pair(&key), Some((key, key)));
        }
        println!("{:?}", map);

        for key in &insert {
            assert_eq!(map.get(key).is_some(), !remove.contains(key));
        }
        assert_eq!(map.len(), insert.len() - remove.len());
        assert_eq!(map.keys().count(), insert.len() - remove.len());
    }
}
