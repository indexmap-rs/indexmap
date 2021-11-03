use std::collections::hash_map::RandomState;
use std::hash::BuildHasher;
use std::hash::Hash;
use std::iter::repeat;

use indexmap::Equivalent;
use indexmap::IndexMap;
use indexmap::IndexSet;

#[derive(Clone, Debug, Default)]
pub struct IndexMultimap<K, V, S = RandomState> {
    inner: IndexMap<K, IndexSet<V, S>, S>,
    len: usize,
}

impl<K, V> IndexMultimap<K, V> {
    pub fn new() -> IndexMultimap<K, V> {
        IndexMultimap {
            inner: IndexMap::new(),
            len: 0,
        }
    }

    pub fn with_capacity(capacity: usize) -> IndexMultimap<K, V> {
        IndexMultimap {
            inner: IndexMap::with_capacity(capacity),
            len: 0,
        }
    }
}

impl<K, V, S> IndexMultimap<K, V, S> {
    pub fn with_capacity_and_hasher(n: usize, hash_builder: S) -> Self {
        IndexMultimap {
            inner: IndexMap::with_capacity_and_hasher(n, hash_builder),
            len: 0,
        }
    }

    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn keys_len(&self) -> usize {
        self.inner.len()
    }

    pub fn get_index(&self, index: usize) -> Option<(&K, &IndexSet<V, S>)> {
        self.inner.get_index(index)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.inner.iter().flat_map(|(k, v)| repeat(k).zip(v.iter()))
    }
}

impl<K, V, S> IndexMultimap<K, V, S>
where
    K: Hash + Eq,
    V: Hash + Eq,
    S: BuildHasher + Default,
{
    /// Insert the value into the multimap.
    ///
    /// If an equivalent entry already exists in the multimap, it returns
    /// `false` leaving the original value in the set and without  altering its
    /// insertion order. Otherwise, it inserts the new entry and returns `true`.
    pub fn insert(&mut self, key: K, value: V) -> bool {
        if self
            .inner
            .entry(key)
            .or_insert_with(|| IndexSet::with_hasher(S::default()))
            .insert(value)
        {
            self.len += 1;
            true
        } else {
            false
        }
    }

    /// Remove the key and all associated values from the multimap.
    ///
    /// Returns the set of values if at least one value is associated to `key`,
    /// returns `None` otherwise.
    pub fn remove_key(&mut self, key: &K) -> Option<IndexSet<V, S>> {
        if let Some(inner_set) = self.inner.remove(key) {
            self.len -= inner_set.len();
            Some(inner_set)
        } else {
            None
        }
    }

    /// Remove the entry from the multimap, and return `true` if it was present.
    pub fn remove(&mut self, key: &K, value: &V) -> bool {
        if let Some(set) = self.inner.get_mut(key) {
            let present = if set.remove(value) {
                self.len -= 1;
                true
            } else {
                false
            };
            if set.is_empty() {
                self.inner.remove(key);
            }
            present
        } else {
            false
        }
    }

    /// Return a reference to the set stored for `key`, if it is present, else
    /// `None`.
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&IndexSet<V, S>>
    where
        Q: Hash + Equivalent<K>,
    {
        self.inner.get(key)
    }

    /// Return item index, if it exists in the map.
    pub fn get_index_of_key<Q: ?Sized>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<K>,
    {
        if self.is_empty() {
            None
        } else {
            self.inner.get_index_of(key)
        }
    }

    /// Return `true` if an equivalent to `key` exists in the map.
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K>,
    {
        self.get_index_of_key(key).is_some()
    }

    /// Return `true` if an equivalent `key` and `value` combination exists in
    /// the multimap.
    pub fn contains_entry<Q: ?Sized, R: ?Sized>(&self, key: &Q, value: &R) -> bool
    where
        Q: Hash + Equivalent<K>,
        R: Hash + Equivalent<V>,
    {
        if let Some(index) = self.get_index_of_key(key) {
            self.inner[index].contains(value)
        } else {
            false
        }
    }

    /// Reserve capacity for `additional` more keys.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }
}

impl<K, V, S> FromIterator<(K, V)> for IndexMultimap<K, V, S>
where
    K: Hash + Eq,
    V: Hash + Eq,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iterable: I) -> Self {
        let iter = iterable.into_iter();
        let (low, _) = iter.size_hint();
        let mut map = Self::with_capacity_and_hasher(low, <_>::default());
        map.extend(iter);
        map
    }
}

impl<K, V, S> Extend<(K, V)> for IndexMultimap<K, V, S>
where
    K: Hash + Eq,
    V: Hash + Eq,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iterable: I) {
        // Using the  same reservation logic as in IndexMap
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for IndexMultimap<K, V, S>
where
    K: Hash + Eq + Copy,
    V: Hash + Eq + Copy,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iterable: I) {
        self.extend(iterable.into_iter().map(|(&key, &value)| (key, value)));
    }
}

#[cfg(test)]
mod test {
    use indexmap::indexset;

    use crate::IndexMultimap;

    #[test]
    fn with_capacity_constructs_instance_with_correct_capacity() {
        let map7: IndexMultimap<usize, usize> = IndexMultimap::with_capacity(7);
        let map17: IndexMultimap<usize, usize> = IndexMultimap::with_capacity(17);
        assert_eq!(7, map7.capacity());
        assert_eq!(17, map17.capacity());
    }

    #[test]
    fn insert_ignores_duplicates() {
        let mut map = IndexMultimap::new();
        assert_eq!(0, map.len());

        assert!(map.insert(0, "A".to_string()));
        assert_eq!(1, map.len());
        assert!(map.contains_entry(&0, &"A".to_string()));

        assert!(!map.insert(0, "A".to_string()));
        assert_eq!(1, map.len());
        assert!(map.contains_entry(&0, &"A".to_string()));
    }

    #[test]
    fn remove_removes_key_when_needed() {
        let data = vec![(0, "A1".to_string()), (0, "A2".to_string())];
        let mut map = data.into_iter().collect::<IndexMultimap<_, _>>();
        assert_eq!(2, map.len());
        assert_eq!(1, map.keys_len());
        assert!(!map.is_empty());

        assert!(map.remove(&0, &"A2".to_string()));
        assert!(!map.contains_entry(&0, &"A2".to_string()));
        assert_eq!(1, map.len());
        assert_eq!(1, map.keys_len());
        assert!(!map.is_empty());
        assert_eq!(Some(&indexset! {"A1".to_string()}), map.get(&0));

        assert!(map.remove(&0, &"A1".to_string()));
        assert!(!map.contains_entry(&0, &"A1".to_string()));
        assert_eq!(0, map.len());
        assert_eq!(0, map.keys_len());
        assert!(map.is_empty());
        assert_eq!(None, map.get(&0));
    }

    #[test]
    fn remove_key_returns_entires_value_set_when_present() {
        let mut map = vec![(0, "A1".to_string()), (0, "A2".to_string())]
            .into_iter()
            .collect::<IndexMultimap<_, _>>();
        assert_eq!(2, map.len());
        assert_eq!(1, map.keys_len());
        assert!(!map.is_empty());

        let expected = Some(indexset! {"A1".to_string(), "A2".to_string()});
        assert_eq!(expected, map.remove_key(&0));
        assert_eq!(0, map.len());
        assert_eq!(0, map.keys_len());
        assert!(map.is_empty());

        assert_eq!(None, map.remove_key(&0));
    }

    #[test]
    fn remove_is_noop_when_key_value_is_not_there() {
        let data = vec![(0, "A1".to_string()), (0, "A2".to_string())];
        let mut map = data.into_iter().collect::<IndexMultimap<_, _>>();
        assert!(!map.remove(&0, &"A3".to_string()));
        assert_eq!(2, map.len());
        assert_eq!(1, map.keys_len());
    }

    #[test]
    fn len_is_consistent() {
        let data = vec![
            (0, "A".to_string()),
            (1, "B".to_string()),
            (2, "C".to_string()),
            (3, "D".to_string()),
            (4, "E".to_string()),
            (4, "E2".to_string()),
            (0, "A2".to_string()),
        ];
        let mut map = IndexMultimap::new();
        for (i, (k, v)) in data.iter().enumerate() {
            assert_eq!(map.len(), i);
            map.insert(*k, v.to_string());
            assert_eq!(map.len(), i + 1);
        }
        let map = data.into_iter().collect::<IndexMultimap<_, _>>();
        assert_eq!(7, map.len());
        assert_eq!(5, map.keys_len());
    }
}
