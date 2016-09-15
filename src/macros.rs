
#[macro_export]
/// Create a `OrderedMap` from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate orderedmap;
/// # fn main() {
///
/// let map = orderedmap!{
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
macro_rules! orderedmap {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(orderedmap!(@single $rest)),*]));

    ($($key:expr => $value:expr,)+) => { orderedmap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            let _cap = orderedmap!(@count $($key),*);
            let mut _map = $crate::OrderedMap::with_capacity(_cap);
            $(
                _map.insert($key, $value);
            )*
            _map
        }
    };
}
