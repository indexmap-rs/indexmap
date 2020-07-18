use std::iter::Enumerate;

pub(crate) fn third<A, B, C>(t: (A, B, C)) -> C {
    t.2
}

pub(crate) fn enumerate<I>(iterable: I) -> Enumerate<I::IntoIter>
where
    I: IntoIterator,
{
    iterable.into_iter().enumerate()
}
