
Proof of concept.

Python 3.6-style hash map where it keeps insertion order. Fast insertion / growth
and iteration.

- Has insert
- Has lookup
- Has resize (grow on insert)
- Has no allocation in OrderedMap::new()
- No remove
