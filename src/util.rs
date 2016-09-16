
use std::iter::Enumerate;

pub fn second<A, B>(t: (A, B)) -> B { t.1 }
pub fn ptr_eq<T: ?Sized>(a: *const T, b: *const T) -> bool { a == b }
pub fn enumerate<I>(iterable: I) -> Enumerate<I::IntoIter>
    where I: IntoIterator
{
    iterable.into_iter().enumerate()
}
