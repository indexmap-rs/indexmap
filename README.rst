
Proof of concept.

Python 3.6-style hash map where it keeps insertion order. Fast insertion / growth
and iteration.

Using robin hood hashing just like Rust's libstd HashMap.

- Has insert
- Has lookup
- Has resize (grow on insert)
- Has no allocation in OrderMap::new()
- Remove is implemented, but it destroys the insertion order.
  It's the usual backwards shift deletion, but only on the index vector, so
  it's cheaper.
  Order-preserving removal would want to be implemented with tombstones,
  but I'm hesitant and not sure if it can be performant.
