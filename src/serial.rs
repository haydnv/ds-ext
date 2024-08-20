use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::{LinkedHashMap, OrdHashMap, OrdHashSet};

struct LinkedHashMapVisitor<K, V> {
    key: PhantomData<K>,
    value: PhantomData<V>,
}

impl<K, V> Default for LinkedHashMapVisitor<K, V> {
    fn default() -> Self {
        Self {
            key: PhantomData,
            value: PhantomData,
        }
    }
}

impl<'de, K, V> Visitor<'de> for LinkedHashMapVisitor<K, V>
where
    K: Deserialize<'de> + Ord + Hash + Eq,
    V: Deserialize<'de>,
{
    type Value = LinkedHashMap<K, V>;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("an ordered HashMap")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut map = if let Some(size_hint) = access.size_hint() {
            LinkedHashMap::with_capacity(size_hint)
        } else {
            LinkedHashMap::new()
        };

        while let Some((key, value)) = access.next_entry()? {
            map.insert(key, value);
        }

        Ok(map)
    }
}

impl<'de, K, V> Deserialize<'de> for LinkedHashMap<K, V>
where
    K: Deserialize<'de> + Ord + Hash + Eq,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(LinkedHashMapVisitor::default())
    }
}

impl<K, V> Serialize for LinkedHashMap<K, V>
where
    K: Hash + Eq + Serialize,
    V: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self)
    }
}

struct OrdHashMapVisitor<K, V> {
    key: PhantomData<K>,
    value: PhantomData<V>,
}

impl<K, V> Default for OrdHashMapVisitor<K, V> {
    fn default() -> Self {
        Self {
            key: PhantomData,
            value: PhantomData,
        }
    }
}

impl<'de, K, V> Visitor<'de> for OrdHashMapVisitor<K, V>
where
    K: Deserialize<'de> + Ord + Hash + Eq,
    V: Deserialize<'de>,
{
    type Value = OrdHashMap<K, V>;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("an ordered HashMap")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut map = if let Some(size_hint) = access.size_hint() {
            OrdHashMap::with_capacity(size_hint)
        } else {
            OrdHashMap::new()
        };

        while let Some((key, value)) = access.next_entry()? {
            map.insert(key, value);
        }

        Ok(map)
    }
}

impl<'de, K, V> Deserialize<'de> for OrdHashMap<K, V>
where
    K: Deserialize<'de> + Ord + Hash + Eq,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(OrdHashMapVisitor::default())
    }
}

impl<K, V> Serialize for OrdHashMap<K, V>
where
    K: Ord + Hash + Eq + Serialize + fmt::Debug,
    V: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self)
    }
}

struct SetVisitor<T> {
    phantom: PhantomData<T>,
}

impl<T> Default for SetVisitor<T> {
    fn default() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<'de, T: Deserialize<'de> + Ord + Hash + Eq> Visitor<'de> for SetVisitor<T> {
    type Value = OrdHashSet<T>;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a set")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut list = if let Some(size_hint) = access.size_hint() {
            OrdHashSet::with_capacity(size_hint)
        } else {
            OrdHashSet::new()
        };

        while let Some(item) = access.next_element()? {
            list.insert(item);
        }

        Ok(list)
    }
}

impl<'de, T: Deserialize<'de> + Ord + Hash + Eq> Deserialize<'de> for OrdHashSet<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(SetVisitor::default())
    }
}

impl<T: Serialize> Serialize for OrdHashSet<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self)
    }
}
