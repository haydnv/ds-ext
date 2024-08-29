//! A hash map ordered by key using a linked hash set

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{hash_map, HashMap as Inner};
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use get_size::GetSize;
use get_size_derive::*;

use super::set::OrdHashSet;

/// An iterator to drain the contents of an [`OrdHashMap`]
pub struct Drain<'a, K, V> {
    inner: &'a mut Inner<Arc<K>, V>,
    order: super::set::Drain<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Drain<'a, K, V> {
    fn next_entry(&mut self, key: Arc<K>) -> Option<(K, V)> {
        let value = self.inner.remove(&*key).expect("value");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        self.next_entry(key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for Drain<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        self.next_entry(key)
    }
}

/// An iterator to drain the contents of an [`OrdHashMap`] conditionally
pub struct DrainWhile<'a, K, V, Cond> {
    inner: &'a mut Inner<Arc<K>, V>,
    order: &'a mut OrdHashSet<Arc<K>>,
    cond: Cond,
}

impl<'a, K, V, Cond> Iterator for DrainWhile<'a, K, V, Cond>
where
    K: Eq + Hash + Ord + fmt::Debug,
    Cond: Fn((&K, &V)) -> bool,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if {
            let key = self.order.first()?;
            let value = self.inner.get(&**key).expect("value");
            (self.cond)((&**key, value))
        } {
            let key = self.order.pop_first().expect("key");
            let value = self.inner.remove(&*key).expect("value");
            let key = Arc::try_unwrap(key).expect("key");
            Some((key, value))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

/// An iterator over the contents of an [`OrdHashMap`]
pub struct IntoIter<K, V> {
    inner: Inner<Arc<K>, V>,
    order: super::set::IntoIter<Arc<K>>,
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

/// An iterator over the entries in an [`OrdHashMap`]
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

/// An iterator over the keys in an [`OrdHashMap`]
pub struct Keys<'a, K, V> {
    inner: &'a Inner<Arc<K>, V>,
    order: super::set::Iter<'a, Arc<K>>,
}

impl<'a, K: Eq + Hash + fmt::Debug, V> Iterator for Keys<'a, K, V> {
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

impl<'a, K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        let (key, _) = self.inner.get_key_value(&**key).expect("entry");
        Some(&**key)
    }
}

/// An owned iterator over the values in an [`OrdHashMap`]
pub struct IntoValues<K, V> {
    inner: Inner<Arc<K>, V>,
    order: super::set::IntoIter<Arc<K>>,
}

impl<K: Eq + Hash + fmt::Debug, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        let key = self.order.next()?;
        self.inner.remove(&*key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for IntoValues<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let key = self.order.next_back()?;
        self.inner.remove(&*key)
    }
}

/// An iterator over the values in an [`OrdHashMap`]
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

/// An occupied entry in an [`OrdHashMap`]
pub type OccupiedEntry<'a, K, V> = hash_map::OccupiedEntry<'a, Arc<K>, V>;

/// A vacant entry in an [`OrdHashMap`]
pub struct VacantEntry<'a, K, V> {
    order: &'a mut OrdHashSet<Arc<K>>,
    entry: hash_map::VacantEntry<'a, Arc<K>, V>,
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Eq + Hash + Ord,
{
    /// Create a new entry with the given `value`
    pub fn insert(self, value: V) -> &'a mut V {
        self.order.insert(self.entry.key().clone());
        self.entry.insert(value)
    }
}

/// An entry in an [`OrdHashMap`]
pub enum Entry<'a, K, V> {
    Occupied(hash_map::OccupiedEntry<'a, Arc<K>, V>),
    Vacant(VacantEntry<'a, K, V>),
}

/// A `HashMap` ordered by key using a [`OrdHashSet`]
#[derive(GetSize)]
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
impl<K, V> OrdHashMap<K, V> {
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

    /// Return the size of this [`OrdHashMap`].
    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K: Eq + Hash + Ord, V> OrdHashMap<K, V> {
    /// Bisect this map to match a key using the provided comparison, and return its value (if any).
    ///
    /// The first key for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered keys (where `cmp(key).is_none()`) lie at the
    /// beginning and/or end of the distribution.
    pub fn bisect<Cmp>(&self, cmp: Cmp) -> Option<&V>
    where
        Cmp: Fn(&K) -> Option<Ordering> + Copy,
    {
        self.order
            .bisect(|key| cmp(&*key))
            .map(|key| self.get(&**key).expect("value"))
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

    /// Drain all entries from this [`OrdHashMap`].
    pub fn drain(&mut self) -> Drain<K, V> {
        Drain {
            inner: &mut self.inner,
            order: self.order.drain(),
        }
    }

    /// Drain all entries from this [`OrdHashMap`].
    pub fn drain_while<Cond>(&mut self, cond: Cond) -> DrainWhile<K, V, Cond>
    where
        Cond: Fn((&K, &V)) -> bool,
    {
        DrainWhile {
            inner: &mut self.inner,
            order: &mut self.order,
            cond,
        }
    }

    /// Return a mutable [`Entry`] in this [`OrdHashMap`].
    pub fn entry<Q: Into<Arc<K>>>(&mut self, key: Q) -> Entry<K, V> {
        match self.inner.entry(key.into()) {
            hash_map::Entry::Occupied(entry) => Entry::Occupied(entry),
            hash_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry {
                entry,
                order: &mut self.order,
            }),
        }
    }

    /// Consume `iter` and insert all its elements into this [`OrdHashMap`].
    pub fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }

    /// Borrow the first value in this [`OrdHashMap`].
    pub fn first(&self) -> Option<&V> {
        let key = self.order.first()?;
        self.inner.get(&**key)
    }

    /// Borrow the first value in this [`OrdHashMap`] mutably.
    pub fn first_mut(&mut self) -> Option<&mut V> {
        let key = self.order.first()?;
        self.inner.get_mut(&**key)
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

    /// Borrow the last value in this [`OrdHashMap`].
    pub fn last(&self) -> Option<&V> {
        let key = self.order.last()?;
        self.inner.get(&**key)
    }

    /// Borrow the last value in this [`OrdHashMap`] mutably.
    pub fn last_mut(&mut self) -> Option<&mut V> {
        let key = self.order.last()?;
        self.inner.get_mut(&**key)
    }

    /// Remove and return the first value in this [`OrdHashMap`].
    pub fn pop_first(&mut self) -> Option<V>
    where
        K: fmt::Debug,
    {
        let key = self.order.pop_first()?;
        self.inner.remove(&*key)
    }

    /// Remove and return the last value in this [`OrdHashMap`].
    pub fn pop_last(&mut self) -> Option<V>
    where
        K: fmt::Debug,
    {
        let key = self.order.pop_last()?;
        self.inner.remove(&*key)
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

    /// Return `true` if the first elements in this [`OrdHashMap`] equal those in the given `iter`.
    pub fn starts_with<'a, I: IntoIterator<Item = (&'a K, &'a V)>>(&self, other: I) -> bool
    where
        K: fmt::Debug + 'a,
        V: PartialEq + 'a,
    {
        let mut this = self.iter();
        let mut that = other.into_iter();

        while let Some(item) = that.next() {
            if this.next() != Some(item) {
                return false;
            }
        }

        true
    }

    /// Construct an owned iterator over the values in this [`OrdHashMap`].
    pub fn into_values(self) -> IntoValues<K, V>
    where
        K: fmt::Debug,
    {
        IntoValues {
            inner: self.inner,
            order: self.order.into_iter(),
        }
    }

    /// Construct an iterator over the values in this [`OrdHashMap`].
    pub fn values(&self) -> Values<K, V> {
        Values {
            inner: &self.inner,
            order: self.order.iter(),
        }
    }
}

impl<K: Eq + Hash + Ord + fmt::Debug, V> OrdHashMap<K, V> {
    /// Bisect this map to match and remove an entry using the provided comparison.
    ///
    /// The first key for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered keys (where `cmp(key).is_none()`) lie at the
    /// beginning and/or end of the distribution.
    pub fn bisect_and_remove<Cmp>(&mut self, cmp: Cmp) -> Option<(K, V)>
    where
        Cmp: Fn(&K) -> Option<Ordering> + Copy,
    {
        let key = self.order.bisect_and_remove(|key| cmp(&*key))?;
        let value = self.inner.remove(&*key).expect("value");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove and return the first entry in this [`OrdHashMap`].
    pub fn pop_first_entry(&mut self) -> Option<(K, V)> {
        let key = self.order.pop_first()?;
        let (key, value) = self.inner.remove_entry(&*key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove and return the last entry in this [`OrdHashMap`].
    pub fn pop_last_entry(&mut self) -> Option<(K, V)> {
        let key = self.order.pop_last()?;
        let (key, value) = self.inner.remove_entry(&*key).expect("entry");
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
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
}

impl<K: Eq + Hash + Ord + fmt::Debug, V: PartialEq> PartialEq<Self> for OrdHashMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .zip(other)
            .all(|((lk, lv), (rk, rv))| lk == rk && lv == rv)
    }
}

impl<K: Eq + Hash + Ord + fmt::Debug, V: Eq> Eq for OrdHashMap<K, V> {}

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

impl<'a, K: Ord + Eq + Hash + fmt::Debug, V> IntoIterator for &'a OrdHashMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find() {
        let mut map = OrdHashMap::<&str, u32>::new();
        map.insert(".tmp", 0);
        map.insert("1", 1);
        map.insert("2", 2);
        map.insert("3", 3);
        map.insert("five", 5);
        map.insert("six", 6);

        assert_eq!(
            map.bisect(|key| key.parse().ok().map(|key: u32| 1.cmp(&key))),
            Some(&1)
        );

        assert_eq!(
            map.bisect(|key| key.parse().ok().map(|key: u32| 2.cmp(&key))),
            Some(&2)
        );

        assert_eq!(
            map.bisect(|key| key.parse().ok().map(|key: u32| 3.cmp(&key))),
            Some(&3)
        );
    }

    #[test]
    fn test_drain() {
        let mut map: OrdHashMap<u32, String> =
            (0..10).into_iter().map(|i| (i, i.to_string())).collect();

        assert_eq!(
            map.drain().collect::<Vec<_>>(),
            (0..10)
                .into_iter()
                .map(|i| (i, i.to_string()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_drain_partial() {
        let mut map: OrdHashMap<u32, String> =
            (0..10).into_iter().map(|i| (i, i.to_string())).collect();

        assert_eq!(
            map.drain().take_while(|(k, _v)| *k < 5).collect::<Vec<_>>(),
            (0..5)
                .into_iter()
                .map(|i| (i, i.to_string()))
                .collect::<Vec<_>>()
        );

        assert_eq!(
            map,
            (6..10).into_iter().map(|i| (i, i.to_string())).collect()
        );
    }

    #[test]
    fn test_drain_while() {
        let mut map: OrdHashMap<u32, String> =
            (0..10).into_iter().map(|i| (i, i.to_string())).collect();

        assert_eq!(
            map.drain_while(|(k, _v)| *k < 5).collect::<Vec<_>>(),
            (0..5)
                .into_iter()
                .map(|i| (i, i.to_string()))
                .collect::<Vec<_>>()
        );

        assert_eq!(
            map,
            (5..10).into_iter().map(|i| (i, i.to_string())).collect()
        );
    }
}
