use std::collections::hash_map::RandomState;
use std::hash::BuildHasher;
use std::hash::Hash;

use indexmap::map::Entry;
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

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn num_keys(&self) -> usize {
        self.inner.len()
    }

    pub fn get_index(&self, index: usize) -> Option<(&K, &IndexSet<V, S>)> {
        self.inner.get_index(index)
    }
}

impl<K, V, S> IndexMultimap<K, V, S>
where
    K: Hash + Eq,
    V: Hash + Eq,
    S: BuildHasher + Default,
{
    pub fn insert_entry(&mut self, key: K, value: V) -> bool {
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

    pub fn remove_key(&mut self, key: &K) -> Option<IndexSet<V, S>> {
        if let Some(inner_set) = self.inner.remove(key) {
            self.len -= inner_set.len();
            Some(inner_set)
        } else {
            None
        }
    }

    pub fn remove_entry(&mut self, key: K, value: &V) {
        if let Entry::Occupied(mut entry) = self.inner.entry(key) {
            if entry.get_mut().remove(value) {
                self.len -= 1;
            }
            if entry.get().is_empty() {
                entry.remove_entry();
            }
        }
    }
}
