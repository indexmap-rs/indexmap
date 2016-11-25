
use std::iter::Enumerate;

pub fn enumerate<I>(iterable: I) -> Enumerate<I::IntoIter>
    where I: IntoIterator
{
    iterable.into_iter().enumerate()
}
