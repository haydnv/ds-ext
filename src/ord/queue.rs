//! A hash map ordered by insertion which can be reordered with a `swap` function,
//! suitable for use as a cache or priority queue (e.g. an LFU or LRU cache).
//!
//! Note: [`Queue`] is indexed by keys and uses a [`List`] for ordering internally.
//! For use cases which require cardinal indexing, use a [`List`] instead.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use super::List;

/// An iterator over the contents of a [`Queue`]
pub struct IntoIter<K, V> {
    inner: HashMap<Arc<K>, V>,
    order: super::list::IntoIter<Arc<K>>,
}

impl<K: Eq + Hash + fmt::Debug, V> IntoIter<K, V> {
    fn next_entry(&mut self, key: Arc<K>) -> Option<(K, V)> {
        let value = self.inner.remove(&*key).expect("value");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }
}

impl<K: Eq + Hash + fmt::Debug, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        self.next_entry(key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        self.next_entry(key)
    }
}

/// An iterator over the entries in a [`Queue`]
pub struct Iter<'a, K, V> {
    inner: &'a HashMap<Arc<K>, V>,
    order: super::list::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let key = &**self.order.next()?;
        let (key, value) = self.inner.get_key_value(key).expect("entry");
        Some((&**key, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        let (key, value) = self.inner.get_key_value(&**key).expect("entry");
        Some((&**key, value))
    }
}

/// An iterator over the keys in a [`Queue`]
pub struct Keys<'a, K, V> {
    inner: &'a HashMap<Arc<K>, V>,
    order: super::list::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        let (key, _) = self.inner.get_key_value(&**key).expect("entry");
        Some(&**key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        let (key, _) = self.inner.get_key_value(&**key).expect("entry");
        Some(&**key)
    }
}

/// An iterator over the values in a [`Queue`]
pub struct Values<'a, K, V> {
    inner: &'a HashMap<Arc<K>, V>,
    order: super::list::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        self.inner.get(&**key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        self.inner.get(&**key)
    }
}

/// A hash map in insertion order which can be reordered using [`Queue::swap`].
pub struct Queue<K, V> {
    inner: HashMap<Arc<K>, V>,
    order: List<Arc<K>>,
}

impl<K: Clone + Eq + Hash, V: Clone> Clone for Queue<K, V> {
    fn clone(&self) -> Self {
        let order: List<Arc<K>> = self.keys().cloned().map(Arc::new).collect();
        let mut inner = HashMap::with_capacity(self.inner.capacity());

        for key in &order {
            let value = self.get::<K>(&**key).expect("value");
            inner.insert(key.clone(), V::clone(value));
        }

        Self { inner, order }
    }
}

impl<K: Eq + Hash, V> Queue<K, V> {
    /// Construct a new [`Queue`].
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
            order: List::new(),
        }
    }

    /// Construct a new [`Queue`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: HashMap::with_capacity(capacity),
            order: List::with_capacity(capacity),
        }
    }

    /// Remove all entries from this [`Queue`].
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Return `true` if there is an entry for the given `key` in this [`Queue`].
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.contains_key(key)
    }

    /// Consume the `iter` and insert all its elements into this [`Queue`].
    pub fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }

    /// Borrow the value at the given `key`, if present.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.get(key)
    }

    /// Borrow the entry at the given `key`, if present.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner
            .get_key_value(key)
            .map(|(key, value)| (&**key, value))
    }

    /// Borrow the value at the given `key` mutably, if present.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.get_mut(key)
    }

    /// Insert a new `value` at `key` and return the previous value, if any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let key = Arc::new(key);
        if let Some(prev) = self.inner.insert(key.clone(), value) {
            todo!();
        } else {
            self.order.push_back(key);
            None
        }
    }

    /// Construct an iterator over the entries in this [`Queue`].
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }

    /// Return `true` if this [`Queue`] is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Construct an iterator over keys of this [`Queue`].
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }

    /// Remove and return the first value in this [`Queue`].
    pub fn pop_first(&mut self) -> Option<V> {
        let key = self.order.pop_front()?;
        self.inner.remove(&*key)
    }

    /// Remove and return the first entry in this [`Queue`].
    pub fn pop_first_entry(&mut self) -> Option<(K, V)>
    where
        K: fmt::Debug,
    {
        let key = self.order.pop_front()?;
        let (key, value) = self.inner.remove_entry(&*key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove and return the last value in this [`Queue`].
    pub fn pop_last(&mut self) -> Option<V> {
        let key = self.order.pop_back()?;
        self.inner.remove(&*key)
    }

    /// Remove and return the last entry in this [`Queue`].
    pub fn pop_last_entry(&mut self) -> Option<(K, V)>
    where
        K: fmt::Debug,
    {
        let key = self.order.pop_back()?;
        let (key, value) = self.inner.remove_entry(&*key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove an entry from this [`Queue`] and return its value, if present.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, value) = self.inner.remove_entry(key)?;
        todo!()
    }

    /// Remove and return an entry from this [`Queue`], if present.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, value) = self.inner.remove_entry(key)?;
        todo!();
    }

    /// Construct an iterator over the values in this [`Queue`].
    pub fn values(&self) -> Values<K, V> {
        Values {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for Queue<K, V> {
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

impl<K: Eq + Hash + fmt::Debug, V> IntoIterator for Queue<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner,
            order: self.order.into_iter(),
        }
    }
}

impl<K: Eq + Hash + fmt::Debug, V: fmt::Debug> fmt::Debug for Queue<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("{")?;

        for (key, value) in self.iter() {
            write!(f, "{:?}: {:?}, ", key, value)?;
        }

        f.write_str("}")
    }
}
