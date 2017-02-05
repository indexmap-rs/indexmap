
Experimental hash table implementation in just Rust (stable, no unsafe code).

This is inpired by Python 3.6's new dict implementation (which remembers
the insertion order and is fast to iterate, and is compact in memory).

This implementation corresponds to their "compact hash map" idea as it is now,
and has consistent order.

Please read the `API documentation here`__

__ https://docs.rs/ordermap/

|build_status|_ |crates|_

.. |crates| image:: https://img.shields.io/crates/v/ordermap.svg
.. _crates: https://crates.io/crates/ordermap

.. |build_status| image:: https://travis-ci.org/bluss/ordermap.svg
.. _build_status: https://travis-ci.org/bluss/ordermap


Using robin hood hashing just like Rust's libstd HashMap.

- Has insert, lookup, grow
- Remove is implemented.
  - It's the usual backwards shift deletion, but only on the index vector, so
    it's cheaper.
  - Remove does not respect the insertion order and this is by design
  - The consistent iteration order (indepentent of hash function) is the main
    feature and affords us fast iteration, no pathological slowdowns or
    hash function/iteration order based attacks.
  - original-insertion-order-preserving removal would want to be implemented
    with tombstones, but I've decided this is going to be a separately named
    hash map. So: fork time.

Performance:

- Iteration is very fast
- Lookup is faster than libstd HashMap for "small" tables (below something like
  100 000 key-value pairs), but suffers under load more due
  to the index vec to entries vec indirection still.
- Growing the map is faster than libstd HashMap, doesn't need to move keys and values
  at all, only the index vec

Interesting Features:

- Insertion order is preserved (swap_remove perturbs the order, like the method name says)
- Implements .pop() -> Option<(K, V)> in O(1) time
- OrderMap::new() is empty and uses no allocation until you insert something
- Lookup key-value pairs by index and vice versa
- No ``unsafe``.
- Supports ``IndexMut``.


Where to go from here?

- It can be an *indexable* ordered map in the current fashion.
  (This was implemented in 0.2.0, for potential use as a graph datastructure).
- Ideas and PRs for how to implement insertion-order preserving remove (for example tombstones)
  are welcome.

- Idea for more cache efficient lookup (This was implemented in 0.1.2)

  Current ``indices: Vec<Pos>``. ``Pos`` is interpreted as ``(u32, u32)`` more
  or less when raw_capacity() fits in 32 bits.  Pos then stores both the lower
  half of the hash and the entry index.
  This means that the hash values in ``Bucket`` don't need to be accessed
  while scanning for an entry.


Recent Changes
--------------

- 0.2.7

  - Add ``.retain()``

- 0.2.6

  - Add ``OccupiedEntry::remove_entry`` and other minor entry methods,
    so that it now has all the features of ``HashMap``'s entries.

- 0.2.5

  - Improved .pop() slightly

- 0.2.4

  - Improved performance of .insert() (#3) by pczarn

- 0.2.3

  - Generalize ``Entry`` for now, so that it works on hashmaps with non-default
    hasher. However, there's a lingering compat issue since libstd HashMap
    does not parameterize its entries by the hasher (``S`` typarm).
  - Special case some iterator methods like ``.nth()``

- 0.2.2

  - Disable the verbose Debug impl by default.

- 0.2.1

  - Fix doc links and clarify docs

- 0.2.0

  - Add more HashMap methods & compat with its API
  - Experimental support for ``.entry()`` (the simplest parts of the API)
  - Add ``.reserve()`` (placeholder impl)
  - Add ``.remove()`` as synonym for ``.swap_remove()``
  - Changed ``.insert()`` to swap value if the entry already exists, and
    return Option.
  - Experimental support as an *indexed* hash map! Added methods
    ``.get_index(), .get_index_mut(), .swap_remove_index()``,
    ``.get_pair_index(), .get_pair_index_mut()``.

- 0.1.2

  - Implement the 32/32 split idea for ``Pos`` which improves cache utilization
    and lookup performance

- 0.1.1

  - Initial release
