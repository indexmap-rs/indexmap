

pub fn second<A, B>(t: (A, B)) -> B { t.1 }
pub fn ptr_eq<T: ?Sized>(a: *const T, b: *const T) -> bool { a == b }
