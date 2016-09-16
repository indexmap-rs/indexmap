
Experimental hash table implementation in just Rust (stable, no unsafe code).

This is inpired by Python 3.6's new dict implementation (which remembers
the insertion order and is fast to iterate).

This implementation corresponds to their "compact hash map" idea as it is now.

Using robin hood hashing just like Rust's libstd HashMap.

- Has insert, lookup, grow
- Remove is implemented, but it perturbs the insertion order.
  It's the usual backwards shift deletion, but only on the index vector, so
  it's cheaper.
  Order-preserving removal would want to be implemented with tombstones,
  but I'm hesitant and not sure if it can be performant.

Performance:

- Iteration is very fast
- Lookup is the same-ish as libstd HashMap, possibly suffers under load more due
  to the index vec to entries vec indirection
- Growing the map is faster than libstd HashMap, doesn't need to move keys and values
  at all, only the index vec

Interesting Features:

- Insertion order is preserved (swap_remove perturbs the order, like the method name says)
- Implements .pop() -> Option<(K, V)> in O(1) time
- OrderMap::new() is empty and uses no allocation until you insert something
- No ``unsafe``.


Where to go from here?

- It can be an *indexable* ordered map in the current fashion
- Ideas and PRs for how to implement insertion-order preserving remove (for example tombstones)
  are welcome.

Please read the `API documentation here`__

__ https://docs.rs/ordermap/0.1/

|crates|_

.. |crates| image:: https://img.shields.io/crates/v/ordermap.svg
.. _crates: https://crates.io/crates/ordermap


Recent Changes
--------------

- 0.1.1

  - Initial release
