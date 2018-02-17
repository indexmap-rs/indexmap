
use super::collect;
use super::rayon::prelude::*;
use super::rayon::iter::plumbing::{Consumer, UnindexedConsumer, ProducerCallback};

use std::cmp::Ordering;
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


impl<T, S> IndexSet<T, S>
    where T: Hash + Eq + Sync,
          S: BuildHasher + Sync,
{
    pub fn par_difference<'a, S2>(&'a self, other: &'a IndexSet<T, S2>)
        -> ParDifference<'a, T, S, S2>
        where S2: BuildHasher + Sync
    {
        ParDifference {
            set1: self,
            set2: other,
        }
    }

    pub fn par_symmetric_difference<'a, S2>(&'a self, other: &'a IndexSet<T, S2>)
        -> ParSymmetricDifference<'a, T, S, S2>
        where S2: BuildHasher + Sync
    {
        ParSymmetricDifference {
            set1: self,
            set2: other,
        }
    }

    pub fn par_intersection<'a, S2>(&'a self, other: &'a IndexSet<T, S2>)
        -> ParIntersection<'a, T, S, S2>
        where S2: BuildHasher + Sync
    {
        ParIntersection {
            set1: self,
            set2: other,
        }
    }

    pub fn par_union<'a, S2>(&'a self, other: &'a IndexSet<T, S2>)
        -> ParUnion<'a, T, S, S2>
        where S2: BuildHasher + Sync
    {
        ParUnion {
            set1: self,
            set2: other,
        }
    }
}

pub struct ParDifference<'a, T: 'a, S1: 'a, S2: 'a> {
    set1: &'a IndexSet<T, S1>,
    set2: &'a IndexSet<T, S2>,
}

impl<'a, T, S1, S2> ParallelIterator for ParDifference<'a, T, S1, S2>
    where T: Hash + Eq + Sync,
          S1: BuildHasher + Sync,
          S2: BuildHasher + Sync,
{
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        let Self { set1, set2 } = self;

        set1.par_iter()
            .filter(move |&item| !set2.contains(item))
            .drive_unindexed(consumer)
    }
}

pub struct ParIntersection<'a, T: 'a, S1: 'a, S2: 'a> {
    set1: &'a IndexSet<T, S1>,
    set2: &'a IndexSet<T, S2>,
}

impl<'a, T, S1, S2> ParallelIterator for ParIntersection<'a, T, S1, S2>
    where T: Hash + Eq + Sync,
          S1: BuildHasher + Sync,
          S2: BuildHasher + Sync,
{
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        let Self { set1, set2 } = self;

        set1.par_iter()
            .filter(move |&item| set2.contains(item))
            .drive_unindexed(consumer)
    }
}

pub struct ParSymmetricDifference<'a, T: 'a, S1: 'a, S2: 'a> {
    set1: &'a IndexSet<T, S1>,
    set2: &'a IndexSet<T, S2>,
}

impl<'a, T, S1, S2> ParallelIterator for ParSymmetricDifference<'a, T, S1, S2>
    where T: Hash + Eq + Sync,
          S1: BuildHasher + Sync,
          S2: BuildHasher + Sync,
{
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        let Self { set1, set2 } = self;

        set1.par_difference(set2)
            .chain(set2.par_difference(set1))
            .drive_unindexed(consumer)
    }
}

pub struct ParUnion<'a, T: 'a, S1: 'a, S2: 'a> {
    set1: &'a IndexSet<T, S1>,
    set2: &'a IndexSet<T, S2>,
}

impl<'a, T, S1, S2> ParallelIterator for ParUnion<'a, T, S1, S2>
    where T: Hash + Eq + Sync,
          S1: BuildHasher + Sync,
          S2: BuildHasher + Sync,
{
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        let Self { set1, set2 } = self;

        set1.par_iter()
            .chain(set2.par_difference(set1))
            .drive_unindexed(consumer)
    }
}


impl<T, S> IndexSet<T, S>
    where T: Hash + Eq + Send,
          S: BuildHasher + Send,
{
    pub fn par_sort(&mut self)
        where T: Ord,
    {
        self.with_entries(|entries| {
            entries.par_sort_by(|a, b| T::cmp(&a.key, &b.key));
        });
    }

    pub fn par_sort_by<F>(&mut self, cmp: F)
        where F: Fn(&T, &T) -> Ordering + Sync,
    {
        self.with_entries(|entries| {
            entries.par_sort_by(move |a, b| cmp(&a.key, &b.key));
        });
    }

    pub fn par_sorted_by<F>(self, cmp: F) -> IntoParIter<T>
        where F: Fn(&T, &T) -> Ordering + Sync
    {
        let mut entries = self.into_entries();
        entries.par_sort_by(move |a, b| cmp(&a.key, &b.key));
        IntoParIter { entries }
    }
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

