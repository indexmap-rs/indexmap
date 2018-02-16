
use super::collect;
use super::rayon::prelude::*;
use super::rayon::iter::plumbing::{Consumer, UnindexedConsumer, ProducerCallback};

use std::hash::Hash;
use std::hash::BuildHasher;

use Entries;
use IndexSet;

type Bucket<T> = ::Bucket<T, ()>;

impl<T, S> IntoParallelIterator for IndexSet<T, S>
    where T: Hash + Eq + Send,
          S: BuildHasher,
{
    type Item = T;
    type Iter = IntoParIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoParIter {
            entries: self.into_entries(),
        }
    }
}

pub struct IntoParIter<T> {
    entries: Vec<Bucket<T>>,
}

impl<T: Send> ParallelIterator for IntoParIter<T> {
    type Item = T;

    parallel_iterator_methods!(Bucket::key);
}

impl<T: Send> IndexedParallelIterator for IntoParIter<T> {
    indexed_parallel_iterator_methods!(Bucket::key);
}


impl<'a, T, S> IntoParallelIterator for &'a IndexSet<T, S>
    where T: Hash + Eq + Sync,
          S: BuildHasher,
{
    type Item = &'a T;
    type Iter = ParIter<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        ParIter {
            entries: self.as_entries(),
        }
    }
}

pub struct ParIter<'a, T: 'a> {
    entries: &'a [Bucket<T>],
}

impl<'a, T: Sync> ParallelIterator for ParIter<'a, T> {
    type Item = &'a T;

    parallel_iterator_methods!(Bucket::key_ref);
}

impl<'a, T: Sync> IndexedParallelIterator for ParIter<'a, T> {
    indexed_parallel_iterator_methods!(Bucket::key_ref);
}


impl<T, S> FromParallelIterator<T> for IndexSet<T, S>
    where T: Eq + Hash + Send,
          S: BuildHasher + Default + Send,
{
    fn from_par_iter<I>(iter: I) -> Self
        where I: IntoParallelIterator<Item = T>
    {
        let list = collect(iter);
        let len = list.iter().map(Vec::len).sum();
        let mut set = Self::with_capacity_and_hasher(len, S::default());
        for vec in list {
            set.extend(vec);
        }
        set
    }
}

impl<T, S> ParallelExtend<(T)> for IndexSet<T, S>
    where T: Eq + Hash + Send,
          S: BuildHasher + Send,
{
    fn par_extend<I>(&mut self, iter: I)
        where I: IntoParallelIterator<Item = T>
    {
        for vec in collect(iter) {
            self.extend(vec);
        }
    }
}

impl<'a, T: 'a, S> ParallelExtend<&'a T> for IndexSet<T, S>
    where T: Copy + Eq + Hash + Send + Sync,
          S: BuildHasher + Send,
{
    fn par_extend<I>(&mut self, iter: I)
        where I: IntoParallelIterator<Item = &'a T>
    {
        for vec in collect(iter) {
            self.extend(vec);
        }
    }
}

