
extern crate serde;

use self::serde::ser::{Serialize, Serializer, SerializeMap};
use self::serde::de::{Deserialize, Deserializer, MapAccess, Visitor};

use std::fmt::{self, Formatter};
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

use OrderMap;

impl<K, V, S> Serialize for OrderMap<K, V, S>
    where K: Serialize + Hash + Eq,
          V: Serialize,
          S: BuildHasher
{
    fn serialize<T>(&self, serializer: T) -> Result<T::Ok, T::Error>
        where T: Serializer
    {
        let mut map_serializer = try!(serializer.serialize_map(Some(self.len())));
        for (key, value) in self {
            try!(map_serializer.serialize_entry(key, value));
        }
        map_serializer.end()
    }
}

struct OrderMapVisitor<K, V>(PhantomData<(K, V)>);

impl<'de, K, V> Visitor<'de> for OrderMapVisitor<K, V>
    where K: Deserialize<'de> + Eq + Hash,
          V: Deserialize<'de>
{
    type Value = OrderMap<K, V>;

    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(formatter, "a map")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where A: MapAccess<'de>
    {
        let mut values = OrderMap::with_capacity(map.size_hint().unwrap_or(0));

        while let Some((key, value)) = try!(map.next_entry()) {
            values.insert(key, value);
        }

        Ok(values)
    }
}

impl<'de, K, V> Deserialize<'de> for OrderMap<K, V>
    where K: Deserialize<'de> + Eq + Hash,
          V: Deserialize<'de>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        deserializer.deserialize_map(OrderMapVisitor(PhantomData))
    }
}
