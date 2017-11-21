
#[macro_export]
/// Create an `OrderMap` from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate ordermap;
/// # fn main() {
///
/// let map = ordermap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(map["a"], 1);
/// assert_eq!(map["b"], 2);
/// assert_eq!(map.get("c"), None);
///
/// // "a" is the first key
/// assert_eq!(map.keys().next(), Some(&"a"));
/// # }
/// ```
macro_rules! ordermap {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(ordermap!(@single $rest)),*]));

    ($($key:expr => $value:expr,)+) => { ordermap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            let _cap = ordermap!(@count $($key),*);
            let mut _map = $crate::OrderMap::with_capacity(_cap);
            $(
                _map.insert($key, $value);
            )*
            _map
        }
    };
}

#[macro_export]
/// Create an `OrderSet` from a list of values
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate ordermap;
/// # fn main() {
///
/// let set = orderset!{
///     "a",
///     "b",
/// };
/// assert!(set.contains("a"));
/// assert!(set.contains("b"));
/// assert!(!set.contains("c"));
///
/// // "a" is the first value
/// assert_eq!(set.iter().next(), Some(&"a"));
/// # }
/// ```
macro_rules! orderset {
    ($($value:expr,)+) => { orderset!($($value),+) };
    ($($value:expr),*) => {
        {
            let _cap = ordermap!(@count $($value),*);
            let mut _set = $crate::OrderSet::with_capacity(_cap);
            $(
                _set.insert($value);
            )*
            _set
        }
    };
}
