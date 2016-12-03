
#![doc(html_root_url = "https://docs.rs/ordermap/0.2/")]

#[cfg(feature="test_efficient_enum")]
extern crate efficient_enum;

mod macros;
mod util;

use std::hash::Hash;
use std::hash::BuildHasher;
use std::hash::Hasher;
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;

use std::cmp::max;
use std::fmt;
use std::mem::replace;
use std::marker::PhantomData;

use util::enumerate;

fn hash_elem_using<B: BuildHasher, K: ?Sized + Hash>(build: &B, k: &K) -> HashValue {
    let mut h = build.build_hasher();
    k.hash(&mut h);
    HashValue::new(h.finish() as usize)
}

#[cfg(not(feature="test_unsafe_index"))]
macro_rules! i {
    ($e:ident$(.$e2:ident)*[$i:expr]) => {$e$(.$e2)*[$i]};
    (&$e:ident$(.$e2:ident)*[$i:expr]) => {&$e$(.$e2)*[$i]};
}

#[cfg(not(feature="test_unsafe_index"))]
macro_rules! im {
    ($e:ident$(.$e2:ident)*[$i:expr]) => {$e$(.$e2)*[$i]};
    (&mut $e:ident$(.$e2:ident)*[$i:expr]) => {&mut $e(.$e2)+[$i]};
}

#[cfg(feature="unsafe")]
include!("unsafe.rs");

/// Hash value newtype. Not larger than usize, since anything larger
/// isn't used for selecting position anyway.
#[derive(Copy, Debug)]
pub struct HashValue(usize);

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
impl HashValue {
    #[cfg(not(feature="test_efficient_enum"))]
    pub fn new(v: usize) -> HashValue {
        HashValue(v)
    }

    pub fn eq_lo32(&self, rhs: &HashValue) -> bool {
        lo32(self.0 as u64) == lo32(rhs.0 as u64)
    }

    pub fn desired_pos(self, mask: usize) -> usize {
        self.0 & mask
    }

    pub fn combine_pos(self, i: usize) -> u64 {
        i as u64 | (lo32(self.0 as u64) << 32) as u64
    }
}

#[cfg(not(feature="test_efficient_enum"))]
#[derive(Copy,Clone,Debug)]
pub struct Bucket<K, V> {
    hash: HashValue,
    option: Option<(K, V)>,
}

/// A type which can take values from a Bucket, leaving the bucket empty
#[cfg(not(feature="test_efficient_enum"))]
pub struct BucketTaker<'a, K: 'a, V: 'a>(&'a mut Bucket<K, V>);

#[cfg(not(feature="test_efficient_enum"))]
impl<K, V> Bucket<K, V> {
    pub fn new(hash: HashValue, key: K, value: V) -> Self {
        Bucket { hash: hash, option: Some((key, value)) }
    }

    pub fn unwrap_hash_key(&self) -> (HashValue, &K) {
        debug_assert!(self.option.is_some());
        (self.hash, &self.option.as_ref().unwrap().0)
    }

    // if the bucket is none, gives a meaningless hash in release and panics in debug
    pub fn hash(&self) -> Option<HashValue> {
        if self.option.is_some() {
            Some(self.hash)
        } else { None }
    }

    // if the bucket is none, gives a meaningless hash in release and panics in debug
    pub fn unwrap_hash(&self) -> HashValue {
        debug_assert!(self.option.is_some());
        self.hash
    }

    pub fn kv(&self) -> Option<(&K, &V)> {
        self.option.as_ref().map(|e| (&e.0, &e.1))
    }

    pub fn unwrap_kv(&self) -> (&K, &V) {
        debug_assert!(self.option.is_some());
        let kv = self.option.as_ref().unwrap();
        (&kv.0, &kv.1)
    }

    pub fn kv_mut(&mut self) -> Option<(&mut K, &mut V)> {
        self.option.as_mut().map(|e| (&mut e.0, &mut e.1))
    }

    pub fn unwrap_kv_mut(&mut self) -> (&mut K, &mut V) {
        debug_assert!(self.option.is_some());
        let kv = self.option.as_mut().unwrap();
        (&mut kv.0, &mut kv.1)
    }

    pub fn taker<'a>(&'a mut self) -> Option<BucketTaker<'a, K, V>> {
        if self.option.is_some() {
            Some(BucketTaker(self))
        } else { None }
    }

    pub fn unwrap_taker<'a>(&'a mut self) -> BucketTaker<'a, K, V> {
        debug_assert!(self.option.is_some());
        BucketTaker(self)
    }

    pub fn take(&mut self) -> Option<(K, V)> {
        self.option.take()
    }

    pub fn into_kv(self) -> Option<(K, V)> {
        debug_assert!(self.option.is_some());
        self.option
    }

    pub fn unwrap_into_kv(self) -> (K, V) {
        debug_assert!(self.option.is_some());
        self.option.unwrap()
    }
}

#[cfg(not(feature="test_efficient_enum"))]
impl<'a, K, V> BucketTaker<'a, K, V> {
    pub fn hash(&self) -> HashValue {
        debug_assert!(self.0.option.is_some());
        self.0.hash
    }
    pub fn key(&self) -> &K {
        debug_assert!(self.0.option.is_some());
        &self.0.option.as_ref().unwrap().0
    }
    pub fn value(&self) -> &V {
        debug_assert!(self.0.option.is_some());
        &self.0.option.as_ref().unwrap().1
    }
    pub fn value_mut(&mut self) -> &mut V {
        debug_assert!(self.0.option.is_some());
        &mut self.0.option.as_mut().unwrap().1
    }
    pub fn into_value_mut(self) -> &'a mut V {
        debug_assert!(self.0.option.is_some());
        &mut self.0.option.as_mut().unwrap().1
    }
    pub fn kv_mut(&mut self) -> (&mut K, &mut V) {
        debug_assert!(self.0.option.is_some());
        let e = self.0.option.as_mut().unwrap();
        (&mut e.0, &mut e.1)
    }
    pub fn take(self) -> (K, V) {
        debug_assert!(self.0.option.is_some());
        self.0.option.take().unwrap()
    }
}



/// A possibly truncated hash value.
///
#[derive(Debug)]
struct ShortHash<Sz>(HashValue, PhantomData<Sz>);

impl<Sz> ShortHash<Sz> {
    /// Pretend this is a full HashValue, which
    /// is completely ok w.r.t determining bucket index
    ///
    /// - Sz = u32: 32-bit hash is enough to select bucket index
    /// - Sz = u64: hash is not truncated
    fn into_hash(self) -> HashValue {
        self.0
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
            self.0 == *rhs
        } else {
            self.0.eq_lo32(rhs)
        }
    }
}

/// `Pos` is stored in the `indices` array and it points to the index of a
/// `Bucket` in self.entries.
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
        match self.debug_pos() {
            PosState::Value(i) => write!(f, "Pos({} / {:x})", i, self.index),
            PosState::IsNone => write!(f, "Pos(None)"),
            PosState::IsTombstone => write!(f, "Pos(Tombstone)"),
        }
    }
}

#[derive(PartialEq, Eq)]
enum PosState<T> {
    IsNone,
    IsTombstone,
    Value(T),
}

const POS_NONE: u64 = !0;
const POS_TOMBSTONE: u64 = !1;

impl Pos {
    #[inline]
    fn none() -> Self { Pos { index: POS_NONE } }

    #[inline]
    fn tombstone() -> Self { Pos { index: POS_TOMBSTONE } }

    #[inline]
    fn with_hash<Sz>(i: usize, hash: HashValue) -> Self
        where Sz: Size
    {
        let i = if Sz::is_64_bit() {
            i as u64
        } else {
            hash.combine_pos(i)
        };
        debug_assert!(i != POS_NONE);
        debug_assert!(i != POS_TOMBSTONE);
        Pos { index: i }
    }

    #[inline]
    fn is_none(&self) -> bool {
        self.index == POS_NONE
    }

    #[inline]
    fn is_tombstone(&self) -> bool {
        self.index == POS_TOMBSTONE
    }

    #[inline]
    fn state(&self) -> PosState<()> {
        match self.index {
            POS_NONE => PosState::IsNone,
            POS_TOMBSTONE => PosState::IsTombstone,
            _ => PosState::Value(()),
        }
    }

    #[inline]
    fn debug_pos(&self) -> PosState<usize>
    {
        match self.index {
            POS_NONE => PosState::IsNone,
            POS_TOMBSTONE => PosState::IsTombstone,
            v => PosState::Value(lo32(v as u64)),
        }
    }

    #[inline]
    fn sub_eq<Sz>(&mut self, delta: usize)
        where Sz: Size
    {
        debug_assert!(self.index != POS_NONE);
        debug_assert!(self.index != POS_TOMBSTONE);
        if Sz::is_64_bit() {
            self.index -= delta as u64
        } else {
            let (i, hash) = split_lo_hi(self.index);
            let i = i as usize - delta;
            self.index = (i | (lo32(hash as u64) << 32)) as u64;
        }
    }

    #[inline]
    fn pos<Sz>(&self) -> PosState<usize>
        where Sz: Size
    {
        match self.index {
            POS_NONE => PosState::IsNone,
            POS_TOMBSTONE => PosState::IsTombstone,
            v => if Sz::is_64_bit() {
                PosState::Value(v as usize)
            } else {
                PosState::Value(lo32(v as u64))
            },
        }
    }

    #[inline]
    fn resolve<Sz>(&self) -> PosState<(usize, ShortHashProxy<Sz>)>
        where Sz: Size
    {
        match self.index {
            POS_NONE => PosState::IsNone,
            POS_TOMBSTONE => PosState::IsTombstone,
            v => if Sz::is_64_bit() {
                PosState::Value((v as usize, ShortHashProxy::new(0)))
            } else {
                let (i, hash) = split_lo_hi(v);
                PosState::Value((i as usize, ShortHashProxy::new(hash as usize)))
            },
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
    fn get_short_hash<K, V>(&self, entries: &[Bucket<K, V>], index: usize) -> ShortHash<Sz> {
        if Sz::is_64_bit() {
            ShortHash(entries[index].unwrap_hash(), PhantomData)
        } else {
            ShortHash(HashValue::new(self.0), PhantomData)
        }
    }
}

/// A hash map with consistent order of the key-value pairs.
///
/// # Order
///
/// The key-value pairs have a consistent order that is determined by
/// the sequence of insertion and removal calls on the map. The order does
/// not depend on the keys or the hash function at all.
///
/// All iterators traverse the map in *the order*.
///
/// # Mutable Keys
///
/// Some methods expose `&mut K`, mutable references to the key as it is stored
/// in the map. The key is allowed to be modified, but *only in a way that
/// preserves its hash and equality* (it is only useful for composite key
/// structs).
///
/// This is sound (memory safe) but a logical error hazard (just like
/// implementing PartialEq, Eq, or Hash incorrectly would be).
///
/// # Examples
///
/// ```
/// use ordermap::OrderMap;
///
/// // count the frequency of each letter in a sentence.
/// let mut letters = OrderMap::new();
/// for ch in "a short treatise on fungi".chars() {
///     *letters.entry(ch).or_insert(0) += 1;
/// }
///
/// assert_eq!(letters[&'s'], 2);
/// assert_eq!(letters[&'t'], 3);
/// assert_eq!(letters[&'u'], 1);
/// assert_eq!(letters.get(&'y'), None);
/// ```
#[derive(Clone)]
pub struct OrderMap<K, V, S = RandomState> {
    mask: usize,
    /// indices are the buckets. indices.len() == raw capacity
    indices: Vec<Pos>,
    /// entries is a dense vec of entries in their order. entries.len() == len
    entries: Vec<Bucket<K, V>>,
    /// the number of tombstones in `indices` waiting to be cleaned up
    index_tombstones: usize,
    /// the number of tombstones in `entries` waiting to be cleaned up
    entry_tombstones: usize,
    hash_builder: S,
}

/// The number of steps that `current` is forward of the prev
#[inline(always)]
fn probe_delta(mask: usize, prev: usize, current: usize) -> usize {
    current.wrapping_sub(prev) & mask
}

/// The number of steps that `current` is forward of the desired position for hash
#[inline(always)]
fn probe_distance(mask: usize, hash: HashValue, current: usize) -> usize {
    probe_delta(mask, hash.desired_pos(mask), current)
}

impl<K, V, S> fmt::Debug for OrderMap<K, V, S>
    where K: fmt::Debug + Hash + Eq,
          V: fmt::Debug,
          S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()?;
        if cfg!(not(feature = "test_debug")) {
            return Ok(());
        }
        writeln!(f, "")?;
        for (i, index) in enumerate(&self.indices) {
            write!(f, "{}: {:?}", i, index)?;
            if let PosState::Value(pos) = index.debug_pos() {
                let (hash, key) = self.entries[pos].unwrap_hash_key();
                writeln!(f, ", desired={}, probe_distance={}, key={:?}",
                              hash.desired_pos(self.mask),
                              probe_distance(self.mask, hash, i),
                              key)?;
            } else {
                writeln!(f, ", tombstone")?;
            }
            writeln!(f, "")?;
        }
        writeln!(f, "cap={}, raw_cap={}, entries.cap={}",
                      self.capacity(),
                      self.raw_capacity(),
                      self.entries.capacity())?;
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

// this could not be captured in an efficient iterator
macro_rules! rev_probe_loop {
    ($probe_var: ident < $len: expr, $body: expr) => {
        loop {
            $body
            if $probe_var == 0 {
                $probe_var = $len;
            }
            $probe_var -= 1;
        }
    }
}

impl<K, V> OrderMap<K, V> {
    /// Create a new map. (Does not allocate.)
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Create a new map with capacity for `n` key-value pairs. (Does not
    /// allocate if `n` is zero.)
    ///
    /// Computes in **O(n)** time.
    pub fn with_capacity(n: usize) -> Self {
        Self::with_capacity_and_hasher(n, <_>::default())
    }
}

impl<K, V, S> OrderMap<K, V, S>
{
    /// Create a new map with capacity for `n` key-value pairs. (Does not
    /// allocate if `n` is zero.)
    ///
    /// Computes in **O(n)** time.
    pub fn with_capacity_and_hasher(n: usize, hash_builder: S) -> Self
        where S: BuildHasher
    {
        if n == 0 {
            OrderMap {
                mask: 0,
                indices: Vec::new(),
                entries: Vec::new(),
                entry_tombstones: 0,
                index_tombstones: 0,
                hash_builder: hash_builder,
            }
        } else {
            let raw = to_raw_capacity(n);
            let raw_cap = max(raw.next_power_of_two(), 8);
            OrderMap {
                mask: raw_cap.wrapping_sub(1),
                indices: vec![Pos::none(); raw_cap],
                entries: Vec::with_capacity(usable_capacity(raw_cap)),
                entry_tombstones: 0,
                index_tombstones: 0,
                hash_builder: hash_builder,
            }
        }
    }

    /// Return the number of key-value pairs in the map.
    ///
    /// Computes in **O(1)** time.
    pub fn len(&self) -> usize { self.entries.len() - self.entry_tombstones }

    /// Return the number of tombstoned key-value pairs in the map.
    ///
    /// Computes in **O(1)** time.
    pub fn tombstones(&self) -> usize { self.entry_tombstones }

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

    /// Computes in **O(1)** time.
    pub fn capacity(&self) -> usize {
        usable_capacity(self.raw_capacity())
    }
}

/// Trait for the "size class". Either u32 or u64 depending on the index
/// size needed to address an entry's indes in self.entries.
trait Size {
    fn is_64_bit() -> bool;
    fn is_same_size<T: Size>() -> bool {
        Self::is_64_bit() == T::is_64_bit()
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

pub enum Entry<'a, K: 'a, V: 'a,> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Computes in **O(1)** time (amortized average).
    pub fn insert(self, value: V) -> Option<V> {
        match self {
            Entry::Occupied(entry) => Some(entry.insert(value)),
            Entry::Vacant(entry) => {
                entry.insert(value);
                None
            },
        }
    }

    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Computes in **O(1)** time (amortized average).
    pub fn or_insert_with<F>(self, call: F) -> &'a mut V
        where F: FnOnce() -> V,
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
}

pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    index_tombstones: &'a mut usize,
    entry_tombstones: &'a mut usize,
    pos: &'a mut Pos,
    bucket_taker: BucketTaker<'a, K, V>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.bucket_taker.key()
    }
    pub fn get(&self) -> &V {
        self.bucket_taker.value()
    }
    pub fn get_mut(&mut self) -> &mut V {
        self.bucket_taker.value_mut()
    }
    pub fn into_mut(self) -> &'a mut V {
        self.bucket_taker.into_value_mut()
    }

    pub fn insert(self, value: V) -> V {
        replace(self.into_mut(), value)
    }

    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Remove and return the key, value pair stored in the map for this entry
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    pub fn remove_entry(self) -> (K, V) {
        *self.index_tombstones +=1;
        *self.entry_tombstones += 1;
        *self.pos = Pos::tombstone();
        self.bucket_taker.take()
    }
}


pub struct VacantEntry<'a, K: 'a, V: 'a> {
    indices: &'a mut Vec<Pos>,
    entries: &'a mut Vec<Bucket<K, V>>,
    index_tombstones: &'a mut usize,
    size_class_is_64bit: bool,
    key: K,
    hash: HashValue,
    probe: usize,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K { &self.key }
    pub fn into_key(self) -> K { self.key }
    pub fn insert(self, value: V) -> &'a mut V {
        if self.size_class_is_64bit {
            self.insert_impl::<u64>(value)
        } else {
            self.insert_impl::<u32>(value)
        }
    }

    fn insert_impl<Sz>(self, value: V) -> &'a mut V
        where Sz: Size
    {
        let index = self.entries.len();
        self.entries.push(Bucket::new(self.hash, self.key, value));
        let old_pos = Pos::with_hash::<Sz>(index, self.hash);
        entry_phase_2::<Sz>(self.indices, self.index_tombstones, self.probe, old_pos);
        self.entries[index].kv_mut().unwrap().1
    }
}

impl<K, V, S> OrderMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher,
{
    /// Get the given key’s corresponding entry in the map for in-place manipulation.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        self.reserve_one();
        dispatch_32_vs_64!(self.entry_phase_1(key))
    }

    // First phase: Look for the preferred location for key.
    //
    // We will know if `key` is already in the map, before we need to insert it.
    //
    // If we don't find the key, or we find a location from which we should steal
    // (robin hood hashing), `VacantEntry` is returned. Any displacing that needs
    // to be done occurs in `entry_phase_2`
    fn entry_phase_1<Sz>(&mut self, key: K) -> Entry<K, V>
        where Sz: Size
    {
        let hash = hash_elem_using(&self.hash_builder, &key);
        let mut probe = hash.desired_pos(self.mask);
        let mut dist = 0;
        let first_tombstone;
        debug_assert!(self.len() < self.raw_capacity());
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    // if existing element probed less than us, swap
                    let their_dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                    if their_dist < dist {
                        // robin hood: steal the spot if it's better for us
                        return Entry::Vacant(VacantEntry {
                            size_class_is_64bit: self.size_class_is_64bit(),
                            indices: &mut self.indices,
                            entries: &mut self.entries,
                            index_tombstones: &mut self.index_tombstones,
                            hash: hash,
                            key: key,
                            probe: probe,
                        });
                    } else if entry_hash == hash && *self.entries[i].unwrap_kv().0 == key {
                        let taker = self.entries[i].unwrap_taker();
                        return Entry::Occupied(OccupiedEntry {
                            entry_tombstones: &mut self.entry_tombstones,
                            index_tombstones: &mut self.index_tombstones,
                            bucket_taker: taker,
                            pos: &mut im!(self.indices[probe]),
                        });
                    }
                },
                PosState::IsNone => {
                    // empty bucket, insert here
                    return Entry::Vacant(VacantEntry {
                        size_class_is_64bit: self.size_class_is_64bit(),
                        indices: &mut self.indices,
                        entries: &mut self.entries,
                        index_tombstones: &mut self.index_tombstones,
                        hash: hash,
                        key: key,
                        probe: probe,
                    });
                },
                PosState::IsTombstone => {
                    if self.index_tombstones == self.indices.len() {
                        return Entry::Vacant(VacantEntry {
                            size_class_is_64bit: self.size_class_is_64bit(),
                            indices: &mut self.indices,
                            entries: &mut self.entries,
                            index_tombstones: &mut self.index_tombstones,
                            hash: hash,
                            key: key,
                            probe: probe,
                        });
                    }

                    first_tombstone = probe;
                    break;
                },
            }
            dist += 1;
        });

        let mut first_tombstone = first_tombstone;
        dist += 1;
        probe += 1;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    // if existing element probed less than us, swap
                    let their_dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                    if their_dist < dist {
                        // take the tombstone
                        return Entry::Vacant(VacantEntry {
                            size_class_is_64bit: self.size_class_is_64bit(),
                            indices: &mut self.indices,
                            entries: &mut self.entries,
                            index_tombstones: &mut self.index_tombstones,
                            hash: hash,
                            key: key,
                            probe: first_tombstone,
                        });
                    } else if entry_hash == hash && *self.entries[i].unwrap_kv().0 == key {
                        let taker = self.entries[i].unwrap_taker();
                        return Entry::Occupied(OccupiedEntry {
                            entry_tombstones: &mut self.entry_tombstones,
                            index_tombstones: &mut self.index_tombstones,
                            bucket_taker: taker,
                            pos: &mut im!(self.indices[probe]),
                        });
                    } else {
                        // since their_dist >= dist and dist > tombstone_dist
                        // any bucket ahead of our target should be moved up
                        self.indices.swap(first_tombstone, probe);

                        // Since we're compacting everything, the next
                        // tombstone will always be directly after
                        first_tombstone += 1;
                        first_tombstone &= self.mask
                    }
                },
                PosState::IsNone => {
                    // empty bucket, insert at last tombstone
                    return Entry::Vacant(VacantEntry {
                        size_class_is_64bit: self.size_class_is_64bit(),
                        indices: &mut self.indices,
                        entries: &mut self.entries,
                        index_tombstones: &mut self.index_tombstones,
                        hash: hash,
                        key: key,
                        probe: first_tombstone,
                    });
                },
                PosState::IsTombstone => {
                    // tombstone bucket, insert here if we've checked everywhere else
                    if dist >= self.indices.len() {
                        return Entry::Vacant(VacantEntry {
                            size_class_is_64bit: self.size_class_is_64bit(),
                            indices: &mut self.indices,
                            entries: &mut self.entries,
                            index_tombstones: &mut self.index_tombstones,
                            hash: hash,
                            key: key,
                            probe: first_tombstone,
                        });
                    }
                },
            }
            dist += 1;
        });
    }

    /// Reserves capacity for at least `additional` more elements to be
    /// inserted.
    ///
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// Computes in **O(n)** time.
    pub fn reserve(&mut self, additional: usize) {
        if additional == 0 { return }
        self.entries.reserve(additional);
        let raw_cap = to_raw_capacity(self.len() + self.index_tombstones + additional);
        if raw_cap < self.raw_capacity() { return }

        if self.index_tombstones >= additional {
            self.remove_index_tombstones();
        } else {
            dispatch_32_vs_64!(self.change_capacity(raw_cap.next_power_of_two()));
        }
    }

    /// Insert they key-value pair into the map.
    ///
    /// If a value already existed for `key`, that old value is returned
    /// in `Some`; otherwise, return `None`.
    ///
    /// Computes in **O(1)** time (amortized average).
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.entry(key).insert(value)
    }

    /// Return an iterator over the keys of the map, in their order
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            iter: self.entries.iter(),
            tombstones: self.entry_tombstones,
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.entries.iter(),
            tombstones: self.entry_tombstones,
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.entries.iter_mut(),
            tombstones: self.entry_tombstones,
        }
    }

    /// Return `true` if and equivalent to `key` exists in the map.
    ///
    /// Computes in **O(1)** time (average).
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.find(key).is_some()
    }

    /// Return a reference to the value stored for `key`, if it is present,
    /// else `None`.
    ///
    /// Computes in **O(1)** time (average).
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair(key).map(|(_, v)| v)
    }

    pub fn get_pair<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair_index(key).map(|(_, k, v)| (k, v))
    }

    /// Return item index, key and value
    pub fn get_pair_index<Q: ?Sized>(&self, key: &Q) -> Option<(usize, &K, &V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.find(key).map(|(_, found, k, v)| (found, k, v))
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair_mut(key).map(|(_, v)| v)
    }

    pub fn get_pair_mut<Q: ?Sized>(&mut self, key: &Q)
        -> Option<(&mut K, &mut V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.get_pair_index_mut(key).map(|(_, k, v)| (k, v))
    }

    pub fn get_pair_index_mut<Q: ?Sized>(&mut self, key: &Q)
        -> Option<(usize, &mut K, &mut V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.find_mut(key).map(|(_, found, k, v)| (found, k, v))
    }

    /// Return probe (indices), position (entries), and key-value pairs by `&`.
    fn find<Q: ?Sized>(&self, key: &Q) -> Option<(usize, usize, &K, &V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if self.len() <= 0 { return None; }

        let h = hash_elem_using(&self.hash_builder, key);
        self.find_using(h, move |k, _| { *k.borrow() == *key })
    }

    /// Return probe (indices), position (entries), and key-value pairs by
    /// `&mut`.
    fn find_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<(usize, usize, &mut K, &mut V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if self.len() <= 0 { return None; }

        let h = hash_elem_using(&self.hash_builder, key);
        self.find_mut_using(h, move |k, _| { *k.borrow() == *key })
    }

    /// Return probe (indices), position (entries), and key-value pairs by
    /// value.
    fn find_remove<Q: ?Sized>(&mut self, key: &Q) -> Option<(usize, usize, K, V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        if self.len() <= 0 { return None; }

        let h = hash_elem_using(&self.hash_builder, key);
        self.find_remove_using(h, move |k, _| { *k.borrow() == *key })
    }

    /// Remove the key-value pair equivalent to `key` and return the `value`.
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// Computes in **O(1)** time (average).
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.remove_pair(key).map(|(_, v)| v)
    }

    /// Remove the key-value pair equivalent to `key` and return it.
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// Computes in **O(1)** time (average).
    fn remove_pair<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.remove_pair_index(key).map(|(_, k, v)| (k, v))
    }

    /// Remove the key-value pair equivalent to `key` and return it along with
    /// the formerly occupied index.
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// Computes in **O(1)** time (average).
    fn remove_pair_index<Q: ?Sized>(&mut self, key: &Q) -> Option<(usize, K, V)>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.find_remove(key).map(|(_, found, k, v)| (found, k, v))
    }

    /// Remove the key-value pair equivalent to `key` and return the `value`.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the
    /// last element of the map and popping it off. **This perturbs
    /// the postion of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Eq + Hash,
    {
        self.swap_remove_pair(key).map(|(_, v)| v)
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
        let (probe, found, _, _) = match self.find(key) {
            None => return None,
            Some(t) => t,
        };
        self.swap_remove_found(probe, found)
    }
}

// Methods that don't use any properties (Hash / Eq) of K.
//
// It's cleaner to separate them out, then the compiler checks that we are not
// using Hash + Eq at all in these methods.
//
// However, we should probably not let this show in the public API or docs.
impl<K, V, S> OrderMap<K, V, S> {
    /// Remove all key-value pairs in the map, while preserving its capacity.
    ///
    /// Computes in **O(n)** time.
    pub fn clear(&mut self) {
        self.entry_tombstones = 0;
        self.index_tombstones = 0;
        self.entries.clear();
        for pos in &mut self.indices {
            *pos = Pos::none();
        }
    }

    /// Remove the last key-value pair
    ///
    /// Computes in **O(1)** time (average).
    pub fn pop(&mut self) -> Option<(K, V)> {
        self.pop_impl()
    }

    /// Scan through each key-value pair in the map and keep those where the
    /// closure `keep` returns `true`.
    ///
    /// The order the elements are visited is not specified.
    ///
    /// Computes in **O(n)** time (average).
    pub fn retain<F>(&mut self, keep: F)
        where F: FnMut(&mut K, &mut V) -> bool
    {
        dispatch_32_vs_64!(self.retain_impl::<_>(keep))
    }

    /// Get a key-value pair by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// Computes in **O(1)** time.
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.entries.get(index).and_then(|e| e.kv())
    }

    /// Get a key-value pair by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// Computes in **O(1)** time.
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&mut K, &mut V)> {
        self.entries.get_mut(index).and_then(|e| e.kv_mut())
    }

    /// Remove the key-value pair by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove_index(&mut self, index: usize) -> Option<(K, V)> {
        self.entries.get(index).and_then(|e| e.hash())
            .map(|hash| self.find_existing_entry_mut(index, hash))
            .and_then(|probe| self.swap_remove_found(probe, index))
    }

    /// Remove the key-value pair by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    ///
    /// Computes in **O(1)** time (average).
    pub fn remove_index(&mut self, index: usize) -> Option<(K, V)> {
        dispatch_32_vs_64!(self.remove_index_impl(index))
    }

    /// Swaps the index of two key-value pairs by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_index(&mut self, a: usize, b: usize) {
        dispatch_32_vs_64!(self.swap_index_impl(a, b))
    }

    /// Removes all the entry tombstones.
    ///
    /// Note that this means indices (e.g. those returned by `get_index`) may
    /// no longer be valid.
    ///
    /// Computes in **O(n)** time (average).
    pub fn remove_tombstones(&mut self) {
        dispatch_32_vs_64!(self.remove_tombstones_impl())
    }
}

// Methods that don't use any properties (Hash / Eq) of K.
//
// It's cleaner to separate them out, then the compiler checks that we are not
// using Hash + Eq at all in these methods.
//
// However, we should probably not let this show in the public API or docs.
impl<K, V, S> OrderMap<K, V, S> {
    fn first_allocation(&mut self) {
        debug_assert_eq!(self.len(), 0);
        let raw_cap = 8usize;
        self.mask = raw_cap.wrapping_sub(1);
        self.indices = vec![Pos::none(); raw_cap];
        self.entries = Vec::with_capacity(usable_capacity(raw_cap));
    }

    // `Sz` is *current* Size class, before grow
    /// Computes in **O(n)** time.
    fn double_capacity(&mut self) {
        if self.raw_capacity() == 0 {
            return self.first_allocation();
        }
        let raw_cap = self.indices.len() * 2;

        dispatch_32_vs_64!(self.change_capacity(raw_cap));
    }

    #[inline(never)]
    // `Sz` is *current* Size class, before grow
    // it is the caller's responsibility to only pass powers of 2 to new_raw_cap
    /// Computes in **O(n)** time.
    fn change_capacity<Sz>(&mut self, raw_cap: usize)
        where Sz: Size
    {
        debug_assert!(self.raw_capacity() == 0 || self.len() > 0);
        debug_assert!(raw_cap.is_power_of_two());
        if self.raw_capacity() == 0 {
            self.mask = raw_cap.wrapping_sub(1);
            self.indices = vec![Pos::none(); raw_cap];
            self.entries = Vec::with_capacity(usable_capacity(raw_cap));
            return;
        }

        // find first ideally placed element -- start of cluster
        let first_ideal = enumerate(&self.indices).find(|&(i, pos)| match pos.pos::<Sz>() {
            PosState::Value(pos) => 0 == probe_distance(self.mask, self.entries[pos].unwrap_hash(), i),
            PosState::IsTombstone => false,
            PosState::IsNone => false,
        }).map_or(0, |(i, _)| i);

        // visit the entries in an order where we can simply reinsert them
        // into self.indices without any bucket stealing.
        let old_indices = replace(&mut self.indices, vec![Pos::none(); raw_cap]);
        self.mask = raw_cap.wrapping_sub(1);

        // `Sz` is the old size class, and either u32 or u64 is the new
        for &pos in &old_indices[first_ideal..] {
            dispatch_32_vs_64!(self.reinsert_entry_in_order::<Sz>(pos));
        }

        for &pos in &old_indices[..first_ideal] {
            dispatch_32_vs_64!(self.reinsert_entry_in_order::<Sz>(pos));
        }

        // We've removed all the index tombstones
        self.index_tombstones = 0;

        let more = self.capacity() - self.len();
        self.entries.reserve_exact(more);
    }

    /// Removes all the index tombstones
    ///
    /// Computes in **O(n)** time.
    fn remove_cheap_index_tombstones(&mut self) {
        dispatch_32_vs_64!(self.remove_cheap_index_tombstones_impl())
    }

    /// Removes all the index tombstones
    ///
    /// Computes in **O(n)** time.
    #[cfg(test)]
    fn remove_index_tombstones(&mut self) {
        dispatch_32_vs_64!(self.remove_index_tombstones_impl())
    }

    /// Removes all the index tombstones
    ///
    /// Computes in **O(n)** time.
    #[cfg(not(test))]
    pub fn remove_index_tombstones(&mut self) {
        dispatch_32_vs_64!(self.remove_index_tombstones_impl())
    }

    /// Remove the last key-value pair
    ///
    /// Computes in **O(1)** time (average).
    fn pop_impl(&mut self) -> Option<(K, V)> {
        // if there entries are empty, just return
        // otherwise, try to get the hash (last entry might be a tombstone)
        self.entries.last_mut()
            .and_then(|mut e| e.taker().map(|e| (e.hash(), e.take())))
            .map(|(hash, value)| {
                let index = self.entries.len() - 1;
                let probe = self.find_existing_entry_mut(index, hash);
                self.entries.pop();
                im!(self.indices[probe]) = Pos::tombstone();
                self.index_tombstones += 1;
                value
            })
    }

    /// Removes cheap the index tombstones
    ///
    /// Computes in **O(n)** time.
    fn remove_cheap_index_tombstones_impl<Sz>(&mut self)
        where Sz: Size
    {
        if self.index_tombstones == 0 { return }

        // Find the first ideal or none (looking backwards)
        let mut probe = enumerate(&self.indices).rev().find(|&(i, index)| match index.pos::<Sz>() {
            PosState::Value(pos) => 0 == probe_distance(self.mask, self.entries[pos].unwrap_hash(), i),
            PosState::IsTombstone => false,
            PosState::IsNone => true,
        }).map_or(0, |(i, _)| i);

        let mut need_processing = self.len() + self.index_tombstones;
        rev_probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).state() {
                PosState::Value(()) => {
                    need_processing -= 1;
                    if need_processing == 0 { return }

                    rev_probe_loop!(probe < self.indices.len(), {
                        if i!(self.indices[probe]).is_none() { break }
                        need_processing -= 1;
                        if need_processing == 0 { return }
                    });
                },
                PosState::IsTombstone => {
                    im!(self.indices[probe]) = Pos::none();

                    self.index_tombstones -= 1;
                    if self.index_tombstones == 0 { return }

                    need_processing -= 1;
                    if need_processing == 0 { return }
                },
                PosState::IsNone => {},
            }
        });
    }

    /// Removes all the index tombstones
    ///
    /// Computes in **O(n)** time.
    fn remove_index_tombstones_impl<Sz>(&mut self)
        where Sz: Size
    {
        if self.index_tombstones == 0 { return }

        if self.len() == 0 {
            for p in self.indices.iter_mut() {
                *p = Pos::none();
            }
            return;
        }

        // Find the first tombstone after an ideal or none
        let mut tombstone_head = enumerate(&self.indices).find(|&(i, index)| match index.pos::<Sz>() {
            PosState::Value(pos) => 0 == probe_distance(self.mask, self.entries[pos].unwrap_hash(), i),
            PosState::IsTombstone => false,
            PosState::IsNone => true,
        }).map_or(0, |(i, _)| i);
        probe_loop!(tombstone_head < self.indices.len(), {
            if i!(self.indices[tombstone_head]).is_tombstone() { break }
        });

        let mut tombstone_tail = tombstone_head;
        let mut probe = tombstone_head + 1;
        let mut tombstones = 1;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    let dist = probe_distance(self.mask, entry_hash.into_hash(), probe);
                    if dist == 0 {
                        // clear the tombstone list
                        while tombstone_head != tombstone_tail {
                            im!(self.indices[tombstone_head]) = Pos::none();
                            tombstone_head += 1;
                            tombstone_head &= self.mask;
                        }
                        im!(self.indices[tombstone_head]) = Pos::none();
                        self.index_tombstones -= tombstones;

                        // if we're out of tombstones, return
                        if self.index_tombstones == 0 { return }

                        // find a new tombstone_head
                        probe_loop!(probe < self.indices.len(), {
                            if i!(self.indices[probe]).is_tombstone() {
                                break
                            }
                        });
                        tombstone_head = probe;
                        tombstone_tail = tombstone_head;
                        tombstones = 1;
                    } else {
                        if dist < tombstones {
                            let delta = tombstones - dist;
                            for _ in 0..delta {
                                // pop off the head and clear it
                                im!(self.indices[tombstone_head]) = Pos::none();
                                tombstone_head += 1;
                                tombstone_head &= self.mask;
                            }
                            self.index_tombstones -= delta;
                            tombstones = dist;
                        }

                        // move the value up
                        self.indices.swap(tombstone_head, probe);

                        tombstone_head += 1;
                        tombstone_head &= self.mask;

                        tombstone_tail = probe;
                    }
                },
                PosState::IsTombstone => {
                    tombstone_tail = probe;
                    tombstones += 1;
                },
                PosState::IsNone => {
                    // clear the tombstone list
                    while tombstone_head != tombstone_tail {
                        im!(self.indices[tombstone_head]) = Pos::none();
                        tombstone_head += 1;
                        tombstone_head &= self.mask;
                    }
                    im!(self.indices[tombstone_head]) = Pos::none();
                    self.index_tombstones -= tombstones;

                    // if we're out of tombstones, return
                    if self.index_tombstones == 0 { return }

                    // find a new tombstone_head
                    probe_loop!(probe < self.indices.len(), {
                        if i!(self.indices[probe]).is_tombstone() {
                            break
                        }
                    });
                    tombstone_head = probe;
                    tombstone_tail = tombstone_head;
                    tombstones = 1;
                },
            }
        });
    }

    // write to self.indices
    // read from self.entries at `pos`
    //
    // reinserting rewrites all `Pos` entries anyway. This handles transitioning
    // from u32 to u64 size class if needed by using the two type parameters.
    fn reinsert_entry_in_order<SzNew, SzOld>(&mut self, pos: Pos)
        where SzNew: Size,
              SzOld: Size,
    {
        if let PosState::Value((i, hash_proxy)) = pos.resolve::<SzOld>() {
            // only if the size class is conserved can we use the short hash
            let entry_hash = if SzOld::is_same_size::<SzNew>() {
                hash_proxy.get_short_hash(&self.entries, i).into_hash()
            } else {
                i!(self.entries[i]).unwrap_hash()
            };
            // find first empty bucket or tombstone and insert there
            let mut probe = entry_hash.desired_pos(self.mask);
            probe_loop!(probe < self.indices.len(), {
                match i!(self.indices[probe]).state() {
                    // skip values
                    PosState::Value(()) => {},
                    PosState::IsNone => {
                        im!(self.indices[probe]) = Pos::with_hash::<SzNew>(i, entry_hash);
                        return
                    },
                    PosState::IsTombstone => debug_assert!(false, "reinserting into tombstones"),
                }
            });
        }
    }

    /// Reserves at least one capacity
    /// Computes in **O(n)** time (average).
    fn reserve_one(&mut self) {
        if self.len() == self.capacity() {
            self.double_capacity();
        }
    }

    /// Scan through each key-value pair in the map and keep those where the
    /// closure `keep` returns `true`.
    ///
    /// The order the elements are visited is not specified.
    ///
    /// Computes in **O(n)** time (average).
    fn retain_impl<Sz, F>(&mut self, mut keep: F)
        where F: FnMut(&mut K, &mut V) -> bool,
        Sz: Size,
    {
        for (i, e) in self.entries.iter_mut().enumerate() {
            if let Some((key, value)) = e.kv_mut() {
                if keep(key, value) { continue }
            } else { continue };

            let hash = e.unwrap_hash();
            let probe = find_existing_entry_mut_impl::<Sz>(self.mask, &mut self.indices, i, hash);
            im!(self.indices[probe]) = Pos::tombstone();
            self.index_tombstones += 1;
            self.entry_tombstones += 1;
            e.take();
        }
    }

    /// Remove the key-value pair by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// This leaves a tombstone in the place of the removed element, which preserves
    /// indices.
    ///
    /// Computes in **O(1)** time (average).
    fn remove_index_impl<Sz>(&mut self, index: usize) -> Option<(K, V)>
        where Sz: Size
    {
        self.entries.get_mut(index)
            .and_then(|e| e.taker().map(|e| (e.hash(), e.take())))
            .map(|(hash, value)| {
                let probe = self.find_existing_entry_mut(index, hash);
                im!(self.indices[probe]) = Pos::tombstone();
                self.entry_tombstones += 1;
                self.index_tombstones += 1;
                value
            })
    }

    /// Swaps the index of two key-value pairs by index
    ///
    /// Valid indices are *0 <= index < self.len() + self.tombstones()*
    ///
    /// Computes in **O(1)** time (average).
    fn swap_index_impl<Sz>(&mut self, a: usize, b: usize)
        where Sz: Size
    {
        if a == b { return }

        match (self.entries[a].hash(), self.entries[b].hash()) {
            (None, None) => {},
            (None, Some(b_hash)) => {
                let probe_b = self.find_existing_entry_mut(b, b_hash);
                self.indices[probe_b] = Pos::with_hash::<Sz>(a, b_hash)
            },
            (Some(a_hash), None) => {
                let probe_a = self.find_existing_entry_mut(a, a_hash);
                self.indices[probe_a] = Pos::with_hash::<Sz>(b, a_hash)
            },
            (Some(a_hash), Some(b_hash)) => {
                let probe_a = self.find_existing_entry_mut(a, a_hash);
                let probe_b = self.find_existing_entry_mut(b, b_hash);
                self.indices.swap(probe_a, probe_b);
            }
        }
        self.entries.swap(a, b);
    }

    /// Removes all the entry tombstones.
    ///
    /// Note that this means indices (e.g. those returned by `get_index`) may
    /// no longer be valid.
    ///
    /// Computes in **O(n)** time (average).
    fn remove_tombstones_impl<Sz>(&mut self)
        where Sz: Size
    {
        if self.entry_tombstones == 0 { return }

        let mask = self.mask;
        let indices = &mut self.indices;
        let mut removed = 0;
        let mut index = 0;

        self.entries.retain(|e| {
            index += 1;
            if let Some(hash) = e.hash() {
                if removed != 0 {
                    let probe = find_existing_entry_mut_impl::<Sz>(mask, indices, index-1, hash);
                    im!(indices[probe]).sub_eq::<Sz>(removed);
                }
                true
            } else {
                removed += 1;
                false
            }
        });

        self.entry_tombstones = 0;
    }

    /// Return probe (indices) and position (entries), and kv reference
    fn find_using<F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize, &K, &V)>
        where F: Fn(&K, &V) -> bool,
    {
        dispatch_32_vs_64!(self.find_using_impl::<_>(hash, key_eq))
    }

    fn find_using_impl<Sz, F>(&self, hash: HashValue, key_eq: F) -> Option<(usize, usize, &K, &V)>
        where F: Fn(&K, &V) -> bool,
              Sz: Size,
    {
        debug_assert!(self.len() > 0);
        let mut probe = hash.desired_pos(self.mask);
        let mut dist = 0;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    if dist > probe_distance(self.mask, entry_hash.into_hash(), probe) {
                        // give up when probe distance is too long
                        return None;
                    } else if entry_hash == hash {
                        let (key, value) = i!(self.entries[i]).unwrap_kv();
                        if key_eq(key, value) {
                            return Some((probe, i, key, value));
                        }
                    }
                },
                PosState::IsTombstone => {},
                PosState::IsNone => return None,
            }
            dist += 1;
        });
    }

    /// Return probe (indices), position (entries), and kv reference
    fn find_mut_using<F>(&mut self, hash: HashValue, key_eq: F) -> Option<(usize, usize, &mut K, &mut V)>
        where F: Fn(&K, &V) -> bool,
    {
        dispatch_32_vs_64!(self.find_mut_using_impl::<_>(hash, key_eq))
    }

    fn find_mut_using_impl<Sz, F>(&mut self, hash: HashValue, key_eq: F) -> Option<(usize, usize, &mut K, &mut V)>
        where F: Fn(&K, &V) -> bool,
              Sz: Size,
    {
        debug_assert!(self.len() > 0);
        let mut probe = hash.desired_pos(self.mask);
        let mut dist = 0;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    if dist > probe_distance(self.mask, entry_hash.into_hash(), probe) {
                        // give up when probe distance is too long
                        return None;
                    } else if entry_hash == hash {
                        if { let (key, value) = im!(self.entries[i]).unwrap_kv_mut(); key_eq(key, value) } {
                            let (key, value) = im!(self.entries[i]).unwrap_kv_mut();
                            return Some((probe, i, key, value));
                        }
                    }
                },
                PosState::IsTombstone => {},
                PosState::IsNone => return None,
            }
            dist += 1;
        });
    }

    /// Return probe (indices) and position (entries)
    fn find_remove_using<F>(&mut self, hash: HashValue, key_eq: F) -> Option<(usize, usize, K, V)>
        where F: Fn(&K, &V) -> bool,
    {
        dispatch_32_vs_64!(self.find_remove_using_impl::<_>(hash, key_eq))
    }

    fn find_remove_using_impl<Sz, F>(&mut self, hash: HashValue, key_eq: F) -> Option<(usize, usize, K, V)>
        where F: Fn(&K, &V) -> bool,
              Sz: Size,
    {
        debug_assert!(self.len() > 0);
        let mut probe = hash.desired_pos(self.mask);
        let mut dist = 0;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    if dist > probe_distance(self.mask, entry_hash.into_hash(), probe) {
                        // give up when probe distance is too long
                        return None;
                    } else if entry_hash == hash {
                        let mut taker = im!(self.entries[i]).unwrap_taker();
                        if { let (key, value) = taker.kv_mut(); key_eq(key, value) } {
                            self.index_tombstones += 1;
                            self.entry_tombstones += 1;
                            im!(self.indices[probe]) = Pos::tombstone();
                            let (key, value) = taker.take();
                            return Some((probe, i, key, value));
                        }
                    }
                },
                PosState::IsTombstone => {},
                PosState::IsNone => return None,
            }
            dist += 1;
        });
    }

    /// Find an entry already placed inside `self.entries` given its position and hash.
    /// Return the probe for the entry.
    ///
    /// Computes in **O(1)** time (average).
    fn find_existing_entry(&self, actual_pos: usize, hash: HashValue) -> usize
    {
        dispatch_32_vs_64!(self.find_existing_entry_impl(actual_pos, hash))
    }

    /// Find an entry already placed inside `self.entries` given its position and hash.
    /// Return the probe for the entry.
    ///
    /// Computes in **O(1)** time (average).
    fn find_existing_entry_impl<Sz>(&self, actual_pos: usize, hash: HashValue) -> usize
        where Sz: Size,
    {
        debug_assert!(self.len() > actual_pos);
        find_existing_entry_impl::<Sz>(self.mask, &self.indices, actual_pos, hash)
    }

    /// Find an entry already placed inside `self.entries` given its position and hash.
    /// Return the probe for the entry.
    ///
    /// Computes in **O(1)** time (average).
    fn find_existing_entry_mut(&mut self, actual_pos: usize, hash: HashValue) -> usize
    {
        dispatch_32_vs_64!(self.find_existing_entry_mut_impl(actual_pos, hash))
    }

    /// Find an entry already placed inside `self.entries` given its position and hash.
    /// Return the probe for the entry.
    ///
    /// Computes in **O(1)** time (average).
    fn find_existing_entry_mut_impl<Sz>(&mut self, actual_pos: usize, hash: HashValue) -> usize
        where Sz: Size,
    {
        debug_assert!(self.len() > actual_pos);
        find_existing_entry_mut_impl::<Sz>(self.mask, &mut self.indices, actual_pos, hash)
    }

    fn swap_remove_found(&mut self, probe: usize, found: usize) -> Option<(K, V)> {
        dispatch_32_vs_64!(self.swap_remove_found_impl(probe, found))
    }

    fn swap_remove_found_impl<Sz>(&mut self, probe: usize, found: usize) -> Option<(K, V)>
        where Sz: Size
    {
        // index `probe` and entry `found` is to be removed
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        im!(self.indices[probe]) = Pos::none();
        let kv = self.entries.swap_remove(found).take();


        // correct index that points to the entry that had to swap places
        // check if it was the last element or a tombstone
        if let Some(hash) = self.entries.get(found).and_then(Bucket::hash) {
            // examine new element in `found` and find it in indices
            let mut probe = hash.desired_pos(self.mask);
            probe_loop!(probe < self.indices.len(), {
                if let PosState::Value(i) = i!(self.indices[probe]).pos::<Sz>() {
                    if i >= self.entries.len() {
                        // found it
                        im!(self.indices[probe]) = Pos::with_hash::<Sz>(found, hash);
                        break;
                    }
                }
            });
        }

        // if we're empty there is there's no work to do
        if self.len() == 0 { return kv }

        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        let mut last_probe = probe;
        let mut probe = probe + 1;
        probe_loop!(probe < self.indices.len(), {
            match i!(self.indices[probe]).resolve::<Sz>() {
                PosState::Value((i, hash_proxy)) => {
                    let entry_hash = hash_proxy.get_short_hash(&self.entries, i);
                    if probe_distance(self.mask, entry_hash.into_hash(), probe) > 0 {
                        im!(self.indices[last_probe]) = self.indices[probe];
                        im!(self.indices[probe]) = Pos::none();
                    } else {
                        break;
                    }
                },
                // Always move tombstones
                PosState::IsTombstone => {
                    im!(self.indices[last_probe]) = Pos::tombstone();
                    im!(self.indices[probe]) = Pos::none();
                },
                PosState::IsNone => break,
            }
            last_probe = probe;
        });

        kv
    }
}

/// Second Phase: forward-shift `Pos` in the indices if need be.
fn entry_phase_2<Sz>(indices: &mut Vec<Pos>, index_tombstones: &mut usize, mut probe: usize, mut old_pos: Pos)
    where Sz: Size
{
    probe_loop!(probe < indices.len(), {
        let pos = &mut im!(indices[probe]);
        match pos.state() {
            PosState::Value(()) => old_pos = replace(pos, old_pos),
            PosState::IsTombstone => {
                *index_tombstones -= 1;
                *pos = old_pos;
                break;
            },
            PosState::IsNone => {
                *pos = old_pos;
                break;
            },
        }
    });
}

/// Find an entry already placed inside `self.entries` given its position and hash.
/// Return the probe for the entry.
///
/// Computes in **O(1)** time (average).
fn find_existing_entry_impl<Sz>(mask: usize, indices: &Vec<Pos>, actual_pos: usize, hash: HashValue) -> usize
    where Sz: Size,
{
    let mut probe = hash.desired_pos(mask);
    probe_loop!(probe < indices.len(), {
        match i!(indices[probe]).pos::<Sz>() {
            PosState::Value(i) => if i == actual_pos { return probe },
            PosState::IsTombstone => {},
            PosState::IsNone => debug_assert!(false, "the entry does not exist"),
        }
    });
}

/// Find an entry already placed inside `self.entries` given its position and hash.
/// Return the probe for the entry.
///
/// This method will swap items with tombstones as it searches, moving items
/// closer to their ideal position.
///
/// Computes in **O(1)** time (average).
fn find_existing_entry_mut_impl<Sz>(mask: usize, indices: &mut Vec<Pos>, actual_pos: usize, hash: HashValue) -> usize
    where Sz: Size,
{
    let mut probe = hash.desired_pos(mask);
    let first_tombstone;
    probe_loop!(probe < indices.len(), {
        match i!(indices[probe]).pos::<Sz>() {
            PosState::Value(i) => if i == actual_pos { return probe },
            PosState::IsTombstone => {
                first_tombstone = probe;
                break
            },
            PosState::IsNone => debug_assert!(false, "the entry does not exist"),
        }
    });

    let mut first_tombstone = first_tombstone;
    probe += 1;
    probe_loop!(probe < indices.len(), {
        match i!(indices[probe]).pos::<Sz>() {
            PosState::Value(i) => {
                // We're already in the neighborhood,
                // any bucket ahead of our target should be moved up
                indices.swap(first_tombstone, probe);
                if i == actual_pos { return first_tombstone }
                first_tombstone += 1;
                first_tombstone &= mask;
            },
            PosState::IsTombstone => {},
            PosState::IsNone => debug_assert!(false, "the entry does not exist"),
        }
    });
}

use std::slice::Iter as SliceIter;
use std::slice::IterMut as SliceIterMut;
use std::vec::IntoIter as VecIntoIter;

pub struct Keys<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Bucket<K, V>>,
    tombstones: usize,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, _)) = e.kv() {
                Some(key)
            } else {
                *tombstones -= 1;
                None
            }
        }).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.tombstones == 0 {
            self.iter.nth(n).map(|e| {
                e.unwrap_kv().0
            })
        } else {
            let tombstones = &mut self.tombstones;
            self.iter.by_ref().filter_map(move |e| {
                if let Some((key, _)) = e.kv() {
                    Some(key)
                } else {
                    *tombstones -= 1;
                    None
                }
            }).nth(n)
        }
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, _)) = e.kv() {
                Some(key)
            } else {
                *tombstones -= 1;
                None
            }
        }).next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len() - self.tombstones
    }
}


pub struct Iter<'a, K: 'a, V: 'a> {
    iter: SliceIter<'a, Bucket<K, V>>,
    tombstones: usize,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, value)) = e.kv() {
                Some((key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.tombstones == 0 {
            self.iter.nth(n).map(|e| {
                e.unwrap_kv()
            })
        } else {
            let tombstones = &mut self.tombstones;
            self.iter.by_ref().filter_map(move |e| {
                if let Some((key, value)) = e.kv() {
                    Some((key, value))
                } else {
                    *tombstones -= 1;
                    None
                }
            }).nth(n)
        }
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, value)) = e.kv() {
                Some((key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len() - self.tombstones
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: SliceIterMut<'a, Bucket<K, V>>,
    tombstones: usize,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, value)) = e.kv_mut() {
                Some((&*key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.tombstones == 0 {
            self.iter.nth(n).map(|e| {
                let (key, value) = e.unwrap_kv_mut();
                (&*key, value)
            })
        } else {
            let tombstones = &mut self.tombstones;
            self.iter.by_ref().filter_map(move |e| {
                if let Some((key, value)) = e.kv_mut() {
                    Some((&*key, value))
                } else {
                    *tombstones -= 1;
                    None
                }
            }).nth(n)
        }
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, value)) = e.kv_mut() {
                Some((&*key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len() - self.tombstones
    }
}

pub struct IntoIter<K, V> {
    iter: VecIntoIter<Bucket<K, V>>,
    tombstones: usize,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(move |e| {
            if let Some((key, value)) = e.into_kv() {
                Some((key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.tombstones == 0 {
            self.iter.nth(n).map(|e| {
                e.unwrap_into_kv()
            })
        } else {
            let tombstones = &mut self.tombstones;
            self.iter.by_ref().filter_map(move |e| {
                if let Some((key, value)) = e.into_kv() {
                    Some((key, value))
                } else {
                    *tombstones -= 1;
                    None
                }
            }).nth(n)
        }
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.iter.len() - self.tombstones
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let tombstones = &mut self.tombstones;
        self.iter.by_ref().filter_map(|e| {
            if let Some((key, value)) = e.into_kv() {
                Some((key, value))
            } else {
                *tombstones -= 1;
                None
            }
        }).next_back()
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
            tombstones: self.entry_tombstones,
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

    /// ***Panics*** if `key` is not present in the map.
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
    /// ***Panics*** if `key` is not present in the map.
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
          S: BuildHasher,
{
    fn extend<I: IntoIterator<Item=(K, V)>>(&mut self, iterable: I) {
        let mut iterator = iterable.into_iter();
        while let Some((k, v)) = iterator.next() {
            let len = self.len();
            if len == self.capacity() {
                let (lower, _) = iterator.size_hint();
                self.reserve(lower.saturating_add(1));
            }
            self.insert(k, v);
        }
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
        for (i, k) in (0..insert.len()).zip(map.keys()) {
            assert_eq!(map.get_index(i).unwrap().0, k);
        }
    }

    #[test]
    fn swap() {
        let mut insert = [0, 4, 2, 12];
        let mut map = OrderMap::new();

        for &elt in &insert {
            map.insert(elt, ());
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
        for (i, k) in (0..insert.len()).zip(map.keys()) {
            assert_eq!(map.get_index(i).unwrap().0, k);
        }

        println!("{:?}", map);
        println!("{:?}", insert);

        insert.swap(1, 2);
        map.swap_index(1, 2);

        println!("{:?}", insert);
        println!("{:?}", map);

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
        for (i, k) in (0..insert.len()).zip(map.keys()) {
            assert_eq!(map.get_index(i).unwrap().0, k);
        }


        insert.swap(0, 3);
        map.swap_index(0, 3);

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
        for (i, k) in (0..insert.len()).zip(map.keys()) {
            assert_eq!(map.get_index(i).unwrap().0, k);
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
    fn retain() {
        let insert = vec![0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderMap::new();

        for &elt in &insert {
            map.insert(elt, elt);
        }

        assert_eq!(map.keys().count(), map.len());
        assert_eq!(map.keys().count(), insert.len());
        for (a, b) in insert.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
        let removed: Vec<_> = insert.iter().filter(|&v| *v >= 10).collect();
        map.retain(|k, _| *k < 10);

        println!("{:?}", insert);
        println!("{:?}", map);

        assert_eq!(map.len(), insert.len() - removed.len());

        for (&a, &b) in insert.iter().filter(|&v| *v < 10).zip(map.keys()) {
            assert_eq!(a, b);
        }
    }


    #[test]
    fn swap_remove() {
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
            assert!(map.get_pair_index(&key).is_none());
            assert!(map.remove(&key).is_none());
        }
        println!("{:?}", map);
        for &key in &remove {
            assert!(map.get_pair_index(&key).is_some());
            let (index, _, _) = map.get_pair_index(&key).unwrap();
            assert!(map.get_index(index).is_some());
            assert_eq!(map.remove(&key), Some(key));
            assert!(map.get_pair_index(&key).is_none());
            assert!(map.get_index(index).is_none());
        }
        println!("{:?}", map);

        for key in &insert {
            assert_eq!(map.get(key).is_some(), !remove.contains(key));
        }

        assert_eq!(map.tombstones(), remove.len());
        assert_eq!(map.len(), insert.len() - remove.len());
        assert_eq!(map.keys().count(), insert.len() - remove.len());

        for (&a, (&b, _)) in insert.iter().filter(|key| !remove.contains(key)).zip(map.iter()) {
            assert_eq!(a, b);
        }

        map.remove_tombstones();

        assert_eq!(map.tombstones(), 0);
        assert_eq!(map.len(), insert.len() - remove.len());
        assert_eq!(map.keys().count(), insert.len() - remove.len());

        for (&a, (&b, _)) in insert.iter().filter(|key| !remove.contains(key)).zip(map.iter()) {
            assert_eq!(a, b);
        }

        for (i, &a) in insert.iter().filter(|key| !remove.contains(key)).enumerate() {
            assert!(map.get_index(i).is_some());
            assert_eq!(a, *map.get_index(i).unwrap().0);
        }

    }

    #[test]
    fn swap_remove_index() {
        let insert = [0, 4, 2, 12, 8, 7, 11, 5, 3, 17, 19, 22, 23];
        let mut map = OrderMap::new();

        for &elt in &insert {
            map.insert(elt, elt * 2);
        }

        let mut vector = insert.to_vec();
        let remove_sequence = &[3, 3, 10, 4, 5, 4, 3, 0, 1];

        // check that the same swap remove sequence on vec and map
        // have the same result.
        for &rm in remove_sequence {
            let out_vec = vector.swap_remove(rm);
            let (out_map, _) = map.swap_remove_index(rm).unwrap();
            assert_eq!(out_vec, out_map);
        }
        assert_eq!(vector.len(), map.len());
        for (a, b) in vector.iter().zip(map.keys()) {
            assert_eq!(a, b);
        }
    }
}
