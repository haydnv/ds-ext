use std::borrow::Borrow;
/// A hash map ordered by key using a linked list
use std::collections::HashMap as Inner;
use std::hash::Hash;
use std::sync::Arc;

use super::List;

/// An iterator over the contents of a [`LinkedHashMap`]
pub struct IntoIter {}

/// An iterator over the entries in a [`LinkedHashMap`]
pub struct Iter<'a, K, V> {
    inner: &'a Inner<K, V>,
}

/// A mutable iterator over the entries in a [`LinkedHashMap`]
pub struct IterMut<'a, K, V> {
    inner: &'a mut Inner<K, V>,
}

/// An iterator over the keys in a [`LinkedHashMap`]
pub struct Keys<'a, K> {
    keys: super::list::Iter<'a, K>,
}

/// An iterator over the values in a [`LinkedHashMap`]
pub struct Values<'a, K, V> {
    inner: &'a Inner<K, V>,
}

/// A vacant entry in a [`LinkedHashMap`]
pub struct VacantEntry<'a, K, V> {
    map: &'a mut LinkedHashMap<K, V>,
}

/// A filled entry in a [`LinkedHashMap`]
pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut LinkedHashMap<K, V>,
}

/// An entry in a [`LinkedHashMap`]
pub enum Entry<'a, K, V> {
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

/// A [`std::collections::HashMap`] ordered by key using a [`List`]
pub struct LinkedHashMap<K, V> {
    inner: Inner<Arc<K>, V>,
    order: List<Arc<K>>,
}

impl<K: Hash, V> LinkedHashMap<K, V> {
    /// Construct a new [`LinkedHashMap`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
            order: List::new(),
        }
    }

    /// Construct a new [`LinkedHashMap`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
            order: List::with_capacity(capacity),
        }
    }

    /// Remove all entries from this [`LinkedHashMap`].
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Construct an [`Entry`] for the given key for in-place manipulation
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        todo!()
    }

    /// Borrow the value at the given `key`, if present.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Borrow the key and value at the given `key`, if present.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&Arc<K>, &V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Borrow the value at the given `key` mutably, if present.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Construct an iterator over the entries in this [`LinkedHashMap`].
    pub fn iter(&self) -> Iter<K, V> {
        todo!()
    }

    /// Construct a mutable iterator over the entries in this [`LinkedHashMap`].
    pub fn iter_mut(&self) -> IterMut<K, V> {
        todo!()
    }

    /// Construct an iterator over the keys in this [`LinkedHashMap`].
    pub fn keys(&self) -> Keys<K> {
        todo!()
    }

    /// Check the size of this [`LinkedHashMap`].
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Borrow the last key in this [`LinkedHashMap`].
    pub fn peek_back(&mut self) -> Option<&K> {
        todo!()
    }

    /// Borrow the first key in this [`LinkedHashMap`].
    pub fn peek_front(&mut self) -> Option<&K> {
        todo!()
    }

    /// Remove and return the last value in this [`LinkedHashMap`].
    pub fn pop_back(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return the last entry in this [`LinkedHashMap`].
    pub fn pop_back_entry(&mut self) -> Option<(K, V)> {
        todo!()
    }

    /// Remove and return the first value in this [`LinkedHashMap`].
    pub fn pop_front(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return the first entry in this [`LinkedHashMap`].
    pub fn pop_front_entry(&mut self) -> Option<(K, V)> {
        todo!()
    }

    /// Remove an entry from this [`LinkedHashMap`] and return its value, if present.
    pub fn remove(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return an entry from this [`LinkedHashMap`], if present.
    pub fn remove_entry(&mut self) -> Option<(K, V)> {
        todo!()
    }

    /// Construct an iterator over the values in this [`LinkedHashMap`].
    pub fn values(&self) -> Values<K, V> {
        todo!()
    }
}
