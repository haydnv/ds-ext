//! A hash map ordered by key using a linked hash set

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{HashMap as Inner, HashMap};
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use super::set::OrdHashSet;

/// An iterator over the contents of a [`OrdHashMap`]
pub struct IntoIter<K, V> {
    inner: Inner<Arc<K>, V>,
    order: super::set::IntoIter<Arc<K>>,
}

impl<K: Eq + Hash + fmt::Debug, V> IntoIter<K, V> {
    fn next_entry(&mut self, key: Arc<Arc<K>>) -> Option<(K, V)> {
        let value = self.inner.remove(&**key).expect("value");
        let key = Arc::try_unwrap(key).expect("key");
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

/// An iterator over the entries in a [`OrdHashMap`]
pub struct Iter<'a, K, V> {
    inner: &'a Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Iterator for Iter<'a, K, V> {
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

impl<'a, K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        let (key, value) = self.inner.get_key_value(&**key).expect("entry");
        Some((&**key, value))
    }
}

/// An iterator over the keys in a [`OrdHashMap`]
pub struct Keys<'a, K, V> {
    inner: &'a HashMap<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        let (key, _) = self.inner.get_key_value(&***key).expect("entry");
        Some(&**key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        let (key, _) = self.inner.get_key_value(&***key).expect("entry");
        Some(&**key)
    }
}

/// An iterator over the values in a [`OrdHashMap`]
pub struct Values<'a, K, V> {
    inner: &'a Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        self.inner.get(&**key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        self.inner.get(&**key)
    }
}

/// A [`HashMap`] ordered by key using a [`OrdHashSet`]
pub struct OrdHashMap<K, V> {
    inner: Inner<Arc<K>, V>,
    order: OrdHashSet<Arc<K>>,
}

impl<K: Clone + Eq + Hash + Ord + fmt::Debug, V: Clone> Clone for OrdHashMap<K, V> {
    fn clone(&self) -> Self {
        let mut inner = Inner::with_capacity(self.inner.capacity());
        let mut order = OrdHashSet::<Arc<K>>::with_capacity(inner.capacity());

        for key in &self.order {
            let key = Arc::new(K::clone(&**key));
            let value = self.inner.get(&key).cloned().expect("value");
            inner.insert(key.clone(), value);
            order.insert(key);
        }

        Self { inner, order }
    }
}

impl<K: Eq + Hash + Ord + fmt::Debug, V> OrdHashMap<K, V> {
    /// Construct a new [`OrdHashMap`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
            order: OrdHashSet::new(),
        }
    }

    /// Construct a new [`OrdHashMap`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
            order: OrdHashSet::with_capacity(capacity),
        }
    }

    fn bisect_hi<Cmp>(&self, cmp: Cmp) -> usize
    where
        Cmp: Fn(&K) -> Option<Ordering>,
    {
        let mut lo = 0;
        let mut hi = 1;

        while lo < hi {
            let mid = (lo + hi) >> 1;
            let key = self.order.nth(mid).expect("key");

            if cmp(&**key).is_some() {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        hi
    }

    fn bisect_lo<Cmp>(&self, cmp: Cmp) -> usize
    where
        Cmp: Fn(&K) -> Option<Ordering>,
    {
        let mut lo = 0;
        let mut hi = 1;

        while lo < hi {
            let mid = (lo + hi) >> 1;
            let key = self.order.nth(mid).expect("key");

            if cmp(&***key).is_some() {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        hi
    }

    fn bisect_inner<Cmp>(&self, cmp: Cmp, mut lo: usize, mut hi: usize) -> Option<Arc<Arc<K>>>
    where
        Cmp: Fn(&K) -> Option<Ordering>,
    {
        while lo < hi {
            let mid = (lo + hi) >> 1;
            let key = self.order.nth(mid).expect("key");

            if let Some(order) = cmp(&**key) {
                match order {
                    Ordering::Less => hi = mid,
                    Ordering::Equal => return Some(key.clone()),
                    Ordering::Greater => lo = mid + 1,
                }
            } else {
                panic!("comparison does not match key distribution")
            }
        }

        None
    }

    /// Bisect this map to match a key using the provided comparison, and return its value (if any).
    ///
    /// The first key for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered keys (where `cmp(key).is_none()`) lie at the
    /// beginning and/or end of the distribution.
    pub fn bisect<Cmp>(&self, cmp: Cmp) -> Option<&V>
    where
        Cmp: Fn(&K) -> Option<Ordering> + Copy,
    {
        let lo = self.bisect_lo(cmp);
        let hi = self.bisect_hi(cmp);
        let key = self.bisect_inner(cmp, lo, hi);
        key.map(|key| self.get(&**key).expect("value"))
    }

    /// Remove all entries from this [`OrdHashMap`].
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Return `true` if there is an entry for the given `key` in this [`OrdHashMap`].
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.inner.contains_key(key)
    }

    /// Consume the `iter` and insert all its elements into this [`OrdHashMap`].
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
        self.order.insert(key.clone());
        self.inner.insert(key, value)
    }

    /// Construct an iterator over the entries in this [`OrdHashMap`].
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }

    /// Return `true` if this [`OrdHashMap`] is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Construct an iterator over keys of this [`OrdHashMap`].
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }

    /// Return the size of this [`OrdHashMap`].
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Remove and return the first value in this [`OrdHashMap`].
    pub fn pop_first(&mut self) -> Option<V> {
        let key = self.order.pop_first()?;
        self.inner.remove(&**key)
    }

    /// Remove and return the first entry in this [`OrdHashMap`].
    pub fn pop_first_entry(&mut self) -> Option<(K, V)> {
        let key = self.order.pop_first()?;
        let (key, value) = self.inner.remove_entry(&**key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove and return the last value in this [`OrdHashMap`].
    pub fn pop_last(&mut self) -> Option<V> {
        let key = self.order.pop_last()?;
        self.inner.remove(&**key)
    }

    /// Remove and return the last entry in this [`OrdHashMap`].
    pub fn pop_last_entry(&mut self) -> Option<(K, V)> {
        let key = self.order.pop_last()?;
        let (key, value) = self.inner.remove_entry(&**key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove an entry from this [`OrdHashMap`] and return its value, if present.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, value) = self.inner.remove_entry(key)?;
        assert!(self.order.remove(&key));
        Some(value)
    }

    /// Remove and return an entry from this [`OrdHashMap`], if present.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, value) = self.inner.remove_entry(key)?;
        assert!(self.order.remove(&key));
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Construct an iterator over the values in this [`OrdHashMap`].
    pub fn values(&self) -> Values<K, V> {
        Values {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }
}

impl<K: Eq + Hash + Ord + fmt::Debug, V> FromIterator<(K, V)> for OrdHashMap<K, V> {
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

impl<K: Eq + Hash + fmt::Debug, V> IntoIterator for OrdHashMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner,
            order: self.order.into_iter(),
        }
    }
}

impl<K: Eq + Hash + Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for OrdHashMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("{")?;

        for (key, value) in self.iter() {
            write!(f, "{:?}: {:?}, ", key, value)?;
        }

        f.write_str("}")
    }
}
