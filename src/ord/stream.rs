use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;
use std::sync::Arc;

use async_trait::async_trait;
use destream::{de, en};

use super::{LinkedHashMap, List, OrdHashMap, OrdHashSet};

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

#[async_trait]
impl<K, V> de::Visitor for LinkedHashMapVisitor<K, V>
where
    K: Hash + Eq + de::FromStream<Context = ()>,
    V: de::FromStream<Context = ()>,
    LinkedHashMap<K, V>: Send,
{
    type Value = LinkedHashMap<K, V>;

    fn expecting() -> &'static str {
        "a LinkedHashMap"
    }

    async fn visit_seq<A: de::SeqAccess>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut map = if let Some(size_hint) = seq.size_hint() {
            LinkedHashMap::with_capacity(size_hint)
        } else {
            LinkedHashMap::new()
        };

        while let Some((key, value)) = seq.next_element(()).await? {
            map.insert(key, value);
        }

        Ok(map)
    }
}

#[async_trait]
impl<K, V> de::FromStream for LinkedHashMap<K, V>
where
    K: Hash + Eq + de::FromStream<Context = ()> + Send + Sync,
    V: de::FromStream<Context = ()>,
{
    type Context = ();

    async fn from_stream<D: de::Decoder>(_: (), decoder: &mut D) -> Result<Self, D::Error> {
        decoder.decode_seq(LinkedHashMapVisitor::default()).await
    }
}

impl<'en, K, V> en::IntoStream<'en> for LinkedHashMap<K, V>
where
    K: Hash + Eq + en::IntoStream<'en> + fmt::Debug + 'en,
    V: en::IntoStream<'en> + 'en,
{
    fn into_stream<E: en::Encoder<'en>>(self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_map(self)
    }
}

impl<'en, K, V> en::ToStream<'en> for LinkedHashMap<K, V>
where
    K: Hash + Eq + en::ToStream<'en> + 'en,
    V: en::ToStream<'en> + 'en,
{
    fn to_stream<E: en::Encoder<'en>>(&'en self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_map(self)
    }
}

struct ListVisitor<T> {
    phantom: PhantomData<T>,
}

impl<T> Default for ListVisitor<T> {
    fn default() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

#[async_trait]
impl<T: de::FromStream<Context = ()>> de::Visitor for ListVisitor<T> {
    type Value = List<T>;

    fn expecting() -> &'static str {
        "a List"
    }

    async fn visit_seq<A: de::SeqAccess>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut list = if let Some(size_hint) = seq.size_hint() {
            List::with_capacity(size_hint)
        } else {
            List::new()
        };

        while let Some(item) = seq.next_element(()).await? {
            list.push_back(item);
        }

        Ok(list)
    }
}

#[async_trait]
impl<T: de::FromStream<Context = ()>> de::FromStream for List<T> {
    type Context = ();

    async fn from_stream<D: de::Decoder>(_: (), decoder: &mut D) -> Result<Self, D::Error> {
        decoder.decode_seq(ListVisitor::default()).await
    }
}

impl<'en, T: en::IntoStream<'en> + 'en> en::IntoStream<'en> for List<T> {
    fn into_stream<E: en::Encoder<'en>>(self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_seq(self)
    }
}

impl<'en, T: en::ToStream<'en> + 'en> en::ToStream<'en> for List<T> {
    fn to_stream<E: en::Encoder<'en>>(&'en self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_seq(self)
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

#[async_trait]
impl<K, V> de::Visitor for OrdHashMapVisitor<K, V>
where
    K: Ord + Hash + Eq + de::FromStream<Context = ()>,
    V: de::FromStream<Context = ()>,
    OrdHashMap<K, V>: Send,
{
    type Value = OrdHashMap<K, V>;

    fn expecting() -> &'static str {
        "an ordered HashMap"
    }

    async fn visit_seq<A: de::SeqAccess>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut map = if let Some(size_hint) = seq.size_hint() {
            OrdHashMap::with_capacity(size_hint)
        } else {
            OrdHashMap::new()
        };

        while let Some((key, value)) = seq.next_element(()).await? {
            map.insert(key, value);
        }

        Ok(map)
    }
}

#[async_trait]
impl<K, V> de::FromStream for OrdHashMap<K, V>
where
    K: Ord + Hash + Eq + de::FromStream<Context = ()> + Send + Sync,
    V: de::FromStream<Context = ()>,
{
    type Context = ();

    async fn from_stream<D: de::Decoder>(_: (), decoder: &mut D) -> Result<Self, D::Error> {
        decoder.decode_seq(OrdHashMapVisitor::default()).await
    }
}

impl<'en, K, V> en::IntoStream<'en> for OrdHashMap<K, V>
where
    K: Ord + Hash + Eq + en::IntoStream<'en> + fmt::Debug + 'en,
    V: en::IntoStream<'en> + 'en,
{
    fn into_stream<E: en::Encoder<'en>>(self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_map(self)
    }
}

impl<'en, K, V> en::ToStream<'en> for OrdHashMap<K, V>
where
    K: Ord + Hash + Eq + en::ToStream<'en> + fmt::Debug + 'en,
    V: en::ToStream<'en> + 'en,
{
    fn to_stream<E: en::Encoder<'en>>(&'en self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_map(self)
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

#[async_trait]
impl<T> de::Visitor for SetVisitor<T>
where
    T: de::FromStream<Context = ()> + Ord + Hash + Eq,
    OrdHashSet<T>: Send + Sync,
{
    type Value = OrdHashSet<T>;

    fn expecting() -> &'static str {
        "an ordered HashSet"
    }

    async fn visit_seq<A: de::SeqAccess>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut set = if let Some(size_hint) = seq.size_hint() {
            OrdHashSet::with_capacity(size_hint)
        } else {
            OrdHashSet::new()
        };

        while let Some(item) = seq.next_element(()).await? {
            set.insert(item);
        }

        Ok(set)
    }
}

#[async_trait]
impl<T> de::FromStream for OrdHashSet<T>
where
    T: de::FromStream<Context = ()> + Ord + Hash + Eq + Send + Sync,
{
    type Context = ();

    async fn from_stream<D: de::Decoder>(_: (), decoder: &mut D) -> Result<Self, D::Error> {
        decoder.decode_seq(SetVisitor::default()).await
    }
}

impl<'en, T> en::IntoStream<'en> for OrdHashSet<T>
where
    T: 'en,
    Arc<T>: en::IntoStream<'en>,
{
    fn into_stream<E: en::Encoder<'en>>(self, encoder: E) -> Result<E::Ok, E::Error> {
        encoder.collect_seq(self)
    }
}
