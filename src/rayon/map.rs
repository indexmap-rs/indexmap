
use super::collect;
use super::rayon::prelude::*;
use super::rayon::iter::plumbing::{Consumer, UnindexedConsumer, ProducerCallback};

use std::hash::Hash;
use std::hash::BuildHasher;

use Bucket;
use Entries;
use IndexMap;

impl<K, V, S> IntoParallelIterator for IndexMap<K, V, S>
    where K: Hash + Eq + Send,
          V: Send,
          S: BuildHasher,
{
    type Item = (K, V);
    type Iter = IntoParIter<K, V>;

    fn into_par_iter(self) -> Self::Iter {
        IntoParIter {
            entries: self.into_entries(),
        }
    }
}

pub struct IntoParIter<K, V> {
    entries: Vec<Bucket<K, V>>,
}

impl<K: Send, V: Send> ParallelIterator for IntoParIter<K, V> {
    type Item = (K, V);

    parallel_iterator_methods!(Bucket::key_value);
}

impl<K: Send, V: Send> IndexedParallelIterator for IntoParIter<K, V> {
    indexed_parallel_iterator_methods!(Bucket::key_value);
}


impl<'a, K, V, S> IntoParallelIterator for &'a IndexMap<K, V, S>
    where K: Hash + Eq + Sync,
          V: Sync,
          S: BuildHasher,
{
    type Item = (&'a K, &'a V);
    type Iter = ParIter<'a, K, V>;

    fn into_par_iter(self) -> Self::Iter {
        ParIter {
            entries: self.as_entries(),
        }
    }
}

pub struct ParIter<'a, K: 'a, V: 'a> {
    entries: &'a [Bucket<K, V>],
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    parallel_iterator_methods!(Bucket::refs);
}

impl<'a, K: Sync, V: Sync> IndexedParallelIterator for ParIter<'a, K, V> {
    indexed_parallel_iterator_methods!(Bucket::refs);
}


impl<'a, K, V, S> IntoParallelIterator for &'a mut IndexMap<K, V, S>
    where K: Hash + Eq + Sync + Send,
          V: Send,
          S: BuildHasher,
{
    type Item = (&'a K, &'a mut V);
    type Iter = ParIterMut<'a, K, V>;

    fn into_par_iter(self) -> Self::Iter {
        ParIterMut {
            entries: self.as_entries_mut(),
        }
    }
}

pub struct ParIterMut<'a, K: 'a, V: 'a> {
    entries: &'a mut [Bucket<K, V>],
}

impl<'a, K: Sync + Send, V: Send> ParallelIterator for ParIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    parallel_iterator_methods!(Bucket::ref_mut);
}

impl<'a, K: Sync + Send, V: Send> IndexedParallelIterator for ParIterMut<'a, K, V> {
    indexed_parallel_iterator_methods!(Bucket::ref_mut);
}


impl<K, V, S> IndexMap<K, V, S>
    where K: Hash + Eq + Sync,
          V: Sync,
          S: BuildHasher,
{
    pub fn par_keys(&self) -> ParKeys<K, V> {
        ParKeys {
            entries: self.as_entries(),
        }
    }

    pub fn par_values(&self) -> ParValues<K, V> {
        ParValues {
            entries: self.as_entries(),
        }
    }
}

pub struct ParKeys<'a, K: 'a, V: 'a> {
    entries: &'a [Bucket<K, V>],
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParKeys<'a, K, V> {
    type Item = &'a K;

    parallel_iterator_methods!(Bucket::key_ref);
}

impl<'a, K: Sync, V: Sync> IndexedParallelIterator for ParKeys<'a, K, V> {
    indexed_parallel_iterator_methods!(Bucket::key_ref);
}

pub struct ParValues<'a, K: 'a, V: 'a> {
    entries: &'a [Bucket<K, V>],
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParValues<'a, K, V> {
    type Item = &'a V;

    parallel_iterator_methods!(Bucket::value_ref);
}

impl<'a, K: Sync, V: Sync> IndexedParallelIterator for ParValues<'a, K, V> {
    indexed_parallel_iterator_methods!(Bucket::value_ref);
}


impl<K, V, S> IndexMap<K, V, S>
    where K: Hash + Eq + Send,
          V: Send,
          S: BuildHasher,
{
    pub fn par_values_mut(&mut self) -> ParValuesMut<K, V> {
        ParValuesMut {
            entries: self.as_entries_mut(),
        }
    }
}

pub struct ParValuesMut<'a, K: 'a, V: 'a> {
    entries: &'a mut [Bucket<K, V>],
}

impl<'a, K: Send, V: Send> ParallelIterator for ParValuesMut<'a, K, V> {
    type Item = &'a mut V;

    parallel_iterator_methods!(Bucket::value_mut);
}

impl<'a, K: Send, V: Send> IndexedParallelIterator for ParValuesMut<'a, K, V> {
    indexed_parallel_iterator_methods!(Bucket::value_mut);
}


impl<K, V, S> FromParallelIterator<(K, V)> for IndexMap<K, V, S>
    where K: Eq + Hash + Send,
          V: Send,
          S: BuildHasher + Default + Send,
{
    fn from_par_iter<I>(iter: I) -> Self
        where I: IntoParallelIterator<Item = (K, V)>
    {
        let list = collect(iter);
        let len = list.iter().map(Vec::len).sum();
        let mut map = Self::with_capacity_and_hasher(len, S::default());
        for vec in list {
            map.extend(vec);
        }
        map
    }
}

impl<K, V, S> ParallelExtend<(K, V)> for IndexMap<K, V, S>
    where K: Eq + Hash + Send,
          V: Send,
          S: BuildHasher + Send,
{
    fn par_extend<I>(&mut self, iter: I)
        where I: IntoParallelIterator<Item = (K, V)>
    {
        for vec in collect(iter) {
            self.extend(vec);
        }
    }
}

impl<'a, K: 'a, V: 'a, S> ParallelExtend<(&'a K, &'a V)> for IndexMap<K, V, S>
    where K: Copy + Eq + Hash + Send + Sync,
          V: Copy + Send + Sync,
          S: BuildHasher + Send,
{
    fn par_extend<I>(&mut self, iter: I)
        where I: IntoParallelIterator<Item = (&'a K, &'a V)>
    {
        for vec in collect(iter) {
            self.extend(vec);
        }
    }
}

