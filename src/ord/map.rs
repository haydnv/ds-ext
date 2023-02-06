/// A hash map ordered by key using a linked list

use std::borrow::Borrow;
use std::collections::HashMap as Inner;
use std::hash::Hash;
use std::sync::Arc;

use super::set::LinkedHashSet;

/// An iterator over the contents of a [`LinkedHashMap`]
pub struct IntoIter<K, V> {
    inner: Inner<Arc<K>, V>,
    order: super::set::IntoIter<Arc<K>>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An iterator over the entries in a [`LinkedHashMap`]
pub struct Iter<'a, K, V> {
    inner: &'a Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

/// A mutable iterator over the entries in a [`LinkedHashMap`]
pub struct IterMut<'a, K, V> {
    inner: &'a mut Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

/// An iterator over the keys in a [`LinkedHashMap`]
pub struct Keys<'a, K> {
    order: super::set::Iter<'a, Arc<K>>,
}

/// An iterator over the values in a [`LinkedHashMap`]
pub struct Values<'a, K, V> {
    inner: &'a Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
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
    order: LinkedHashSet<Arc<K>>,
}

impl<K: Hash, V> LinkedHashMap<K, V> {
    /// Construct a new [`LinkedHashMap`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
            order: LinkedHashSet::new(),
        }
    }

    /// Construct a new [`LinkedHashMap`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
            order: LinkedHashSet::with_capacity(capacity),
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

    /// Consume the `iter` and insert all its elements into this [`LinkedHashMap`].
    pub fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }

    /// Borrow the value at the given `key`, if present.
    pub fn get<Q>(&mut self, key: &Q) -> Option<&V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Borrow the entry at the given `key`, if present.
    pub fn get_entry<Q>(&mut self, key: &Q) -> Option<(&K, &V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Borrow the value at the given `key` mutably, if present.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        todo!()
    }

    /// Insert a new `value` at `key` and return the previous value, if any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
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

    /// Construct an iterator over keys of this [`LinkedHashMap`].
    pub fn keys(&self) -> Keys<K> {
        todo!()
    }

    /// Remove and return the first value in this [`LinkedHashMap`].
    pub fn pop_first(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return the first entry in this [`LinkedHashMap`].
    pub fn pop_first_entry(&mut self) -> Option<(K, V)> {
        todo!()
    }

    /// Remove and return the last value in this [`LinkedHashMap`].
    pub fn pop_last(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return the last entry in this [`LinkedHashMap`].
    pub fn pop_last_entry(&mut self) -> Option<(K, V)> {
        todo!()
    }

    /// Remove an entry from this [`LinkedHashMap`] and return its value, if present.
    pub fn remove(&mut self) -> Option<V> {
        todo!()
    }

    /// Remove and return an entry from this [`LinkedHashMap`], if present.
    pub fn remove_entry(&mut self) -> Option<(Arc<K>, V)> {
        todo!()
    }

    /// Construct an iterator over the values in this [`LinkedHashMap`].
    pub fn values(&self) -> Values<K, V> {
        todo!()
    }
}

impl<K: Hash, V> FromIterator<(K, V)> for LinkedHashMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map = match iter.size_hint() {
            (_, Some(max)) => Self::with_capacity(max),
            (min, None) if min > 0 => Self::with_capacity(min),
            _ => Self::new(),
        };

        map.extend(iter);
        map
    }
}

impl<K, V> IntoIterator for LinkedHashMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}
