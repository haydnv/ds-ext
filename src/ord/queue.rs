//! A linked hash map ordered by insertion which can be reordered by swapping,
//! useful as a simple priority queue (e.g. an LFU or LRU cache).
//!
//! Note: [`Queue`] is indexed by keys. For indexing by cardinal order, use a [`List`] instead.

use std::borrow::Borrow;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;
use std::{fmt, mem};

struct ItemState<K> {
    prev: Option<Arc<K>>,
    next: Option<Arc<K>>,
}

struct Item<K, V> {
    key: Arc<K>,
    value: V,
    state: RefCell<ItemState<K>>,
}

impl<K, V> Item<K, V> {
    #[inline]
    fn state(&self) -> RefMut<ItemState<K>> {
        self.state.borrow_mut()
    }
}

type Inner<K, V> = HashMap<Arc<K>, Item<K, V>>;

/// An iterator over the contents of a [`Queue`]
pub struct IntoIter<K, V> {
    queue: Queue<K, V>,
}

impl<K: Eq + Hash + fmt::Debug, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop_first_entry()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.queue.len(), Some(self.queue.len()))
    }
}

impl<K: Eq + Hash + fmt::Debug, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.queue.pop_last_entry()
    }
}

/// An iterator over the entries in a [`Queue`]
pub struct Iter<'a, K, V> {
    list: &'a Inner<K, V>,
    next: Option<Arc<K>>,
    last: Option<Arc<K>>,
    size: usize,
}

impl<'a, K: Eq + Hash, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next.take()?;
        let (key, item) = self.list.get_key_value(&*next).expect("next");

        if self.last == Some(next) {
            self.next = None;
            self.last = None;
        } else {
            self.next = item.state().next.clone();
        }

        self.size -= 1;

        Some((key, &item.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, K: Eq + Hash, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let last = self.last.take()?;
        let (key, item) = self.list.get_key_value(&*last).expect("next");

        if self.next == Some(last) {
            self.next = None;
            self.last = None;
        } else {
            self.last = item.state().prev.clone();
        }

        self.size -= 1;

        Some((key, &item.value))
    }
}

/// An iterator over the keys in a [`Queue`]
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Hash + Eq, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(key, _value)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Hash + Eq, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(key, _value)| key)
    }
}

/// An iterator over the values in a [`Queue`]
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Eq + Hash, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_key, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K: Eq + Hash, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(_key, value)| value)
    }
}

/// A hash map in insertion order which can be reordered using [`Queue::swap`].
pub struct Queue<K, V> {
    list: Inner<K, V>,
    head: Option<Arc<K>>,
    tail: Option<Arc<K>>,
}

impl<K: Clone + Eq + Hash, V: Clone> Clone for Queue<K, V> {
    fn clone(&self) -> Self {
        let mut other = Self::with_capacity(self.list.capacity());

        for (key, item) in &self.list {
            let key = K::clone(&**key);
            let value = V::clone(&item.value);
            other.insert(key, value);
        }

        other
    }
}

impl<K: Eq + Hash, V> Queue<K, V> {
    /// Construct a new [`Queue`].
    pub fn new() -> Self {
        Self {
            list: HashMap::new(),
            head: None,
            tail: None,
        }
    }

    /// Construct a new [`Queue`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            list: HashMap::with_capacity(capacity),
            head: None,
            tail: None,
        }
    }

    /// If `key` is present, increase its priority by one and return `true`.
    pub fn bump(&mut self, key: &K) -> bool {
        let item = if let Some(item) = self.list.get(key) {
            item
        } else {
            return false;
        };

        let mut item_state = item.state();

        let last = if item_state.prev.is_none() {
            // can't bump the first item
            return true;
        } else if item_state.next.is_none() && item_state.prev.is_some() {
            // bump the last item

            let prev_key = item_state.prev.as_ref().expect("prev");
            let mut prev = self.list.get::<K>(prev_key).expect("prev").state();

            mem::swap(&mut prev.next, &mut item_state.next); // set prev.next
            mem::swap(&mut item_state.prev, &mut prev.prev); // set item.prev
            mem::swap(&mut item_state.next, &mut prev.prev); // set item.next & prev.prev

            item_state.next.clone()
        } else {
            // bump an item in the middle

            let next_key = item_state.next.as_ref().expect("next");
            let mut next = self.list.get::<K>(next_key).expect("next").state();

            let prev_key = item_state.prev.as_ref().expect("prev").clone();
            let mut prev = self.list.get::<K>(&prev_key).expect("prev").state();

            mem::swap(&mut next.prev, &mut item_state.prev); // set next.prev
            mem::swap(&mut item_state.prev, &mut prev.prev); // set item.prev
            mem::swap(&mut prev.next, &mut item_state.next); // set prev.next

            item_state.prev = Some(prev_key); // set item.prev

            None
        };

        let first = if let Some(prev_key) = &item_state.prev {
            let mut skip = self.list.get::<K>(prev_key).expect("skip").state();
            skip.next = Some(item.key.clone());
            None
        } else {
            Some(item.key.clone())
        };

        if let Some(first) = first {
            self.head = Some(first);
        }

        if let Some(last) = last {
            self.tail = Some(last);
        }

        true
    }

    /// Remove all entries from this [`Queue`].
    pub fn clear(&mut self) {
        self.list.clear();
        self.head = None;
        self.tail = None;
    }

    /// Return `true` if there is an entry for the given `key` in this [`Queue`].
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.list.contains_key(key)
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
        self.list.get(key).map(|item| &item.value)
    }

    /// Borrow the entry at the given `key`, if present.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.list
            .get_key_value(key)
            .map(|(key, item)| (&**key, &item.value))
    }

    /// Borrow the value at the given `key` mutably, if present.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Arc<K>: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.list.get_mut(key).map(|item| &mut item.value)
    }

    /// Insert a new `value` at `key` and return the previous value, if any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let old_value = self.remove(&key);

        let key = Arc::new(key);
        let next = None;
        let mut prev = Some(key.clone());
        mem::swap(&mut self.tail, &mut prev);

        if let Some(prev_key) = &prev {
            let mut prev = self.list.get::<K>(prev_key).expect("prev").state();
            prev.next = Some(key.clone());
        }

        if self.head.is_none() {
            self.head = Some(key.clone());
        }

        let item = Item {
            key: key.clone(),
            value,
            state: RefCell::new(ItemState { prev, next }),
        };

        assert!(self.list.insert(key, item).is_none());

        old_value
    }

    /// Construct an iterator over the entries in this [`Queue`].
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            list: &self.list,
            next: self.head.clone(),
            last: self.tail.clone(),
            size: self.len(),
        }
    }

    /// Return `true` if this [`Queue`] is empty.
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Construct an iterator over keys of this [`Queue`].
    pub fn keys(&self) -> Keys<K, V> {
        Keys { inner: self.iter() }
    }

    /// Return the size of this [`Queue`].
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Remove and return the first value in this [`Queue`].
    pub fn pop_first(&mut self) -> Option<V> {
        if self.head.is_none() {
            return None;
        }

        let item = self
            .list
            .remove(self.head.as_ref().expect("head"))
            .expect("head");

        Some(self.remove_inner(item))
    }

    /// Remove and return the first entry in this [`Queue`].
    pub fn pop_first_entry(&mut self) -> Option<(K, V)>
    where
        K: fmt::Debug,
    {
        if self.head.is_none() {
            return None;
        }

        let (key, item) = self
            .list
            .remove_entry(self.head.as_ref().expect("head"))
            .expect("head");

        let value = self.remove_inner(item);
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    /// Remove and return the last value in this [`Queue`].
    pub fn pop_last(&mut self) -> Option<V> {
        if self.tail.is_none() {
            return None;
        }

        let item = self
            .list
            .remove(self.tail.as_ref().expect("tail"))
            .expect("tail");

        Some(self.remove_inner(item))
    }

    /// Remove and return the last entry in this [`Queue`].
    pub fn pop_last_entry(&mut self) -> Option<(K, V)>
    where
        K: fmt::Debug,
    {
        if self.tail.is_none() {
            return None;
        }

        let (key, item) = self
            .list
            .remove_entry(self.tail.as_ref().expect("tail"))
            .expect("tail");

        let value = self.remove_inner(item);
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, value))
    }

    fn remove_inner(&mut self, item: Item<K, V>) -> V {
        let mut item_state = item.state();

        if item_state.prev.is_none() && item_state.next.is_none() {
            // there was only one item and now the map is empty
            self.head = None;
            self.tail = None;
        } else if item_state.prev.is_none() {
            // the last item has been removed
            self.tail = item_state.next.clone();

            let next_key = item_state.next.as_ref().expect("next key");
            let mut next = self.list.get::<K>(next_key).expect("next").state();

            mem::swap(&mut next.prev, &mut item_state.prev);
        } else if item_state.next.is_none() {
            // the first item has been removed
            self.head = item_state.prev.clone();

            let prev_key = item_state.prev.as_ref().expect("previous key");
            let mut prev = self.list.get::<K>(prev_key).expect("prev").state();

            mem::swap(&mut prev.next, &mut item_state.next);
        } else {
            // an item in the middle has been removed
            let prev_key = item_state.prev.as_ref().expect("previous key");
            let mut prev = self.list.get::<K>(prev_key).expect("prev").state();

            let next_key = item_state.next.as_ref().expect("next key");
            let mut next = self.list.get::<K>(next_key).expect("next item").state();

            mem::swap(&mut next.prev, &mut item_state.prev);
            mem::swap(&mut prev.next, &mut item_state.next);
        }

        std::mem::drop(item_state);
        item.value
    }

    /// Remove an entry from this [`Queue`] and return its value, if present.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let item = self.list.remove(key)?;
        Some(self.remove_inner(item))
    }

    /// Remove and return an entry from this [`Queue`], if present.
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: fmt::Debug,
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, item) = self.list.remove_entry(key)?;
        let key = Arc::try_unwrap(key).expect("key");
        Some((key, self.remove_inner(item)))
    }

    /// Swap the position of two keys in this [`Queue`].
    /// Returns `true` if both keys are present in the [`Queue`].
    pub fn swap<Q>(&mut self, l: &Q, r: &Q) -> bool
    where
        Arc<K>: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if l == r {
            return self.contains_key(l) && self.contains_key(r);
        }

        let (l_key, l_item) = if let Some(entry) = self.list.get_key_value(l) {
            entry
        } else {
            return false;
        };

        let (r_key, r_item) = if let Some(entry) = self.list.get_key_value(r) {
            entry
        } else {
            return false;
        };

        let mut l_state = l_item.state();
        let mut r_state = r_item.state();
        mem::swap(&mut l_state, &mut r_state);

        if self.head.as_ref() == Some(l_key) {
            self.head = Some(r_key.clone());
        } else if self.head.as_ref() == Some(r_key) {
            self.head = Some(l_key.clone());
        }

        if self.tail.as_ref() == Some(l_key) {
            self.tail = Some(r_key.clone());
        } else if self.tail.as_ref() == Some(r_key) {
            self.tail = Some(l_key.clone());
        }

        true
    }

    /// Construct an iterator over the values in this [`Queue`].
    pub fn values(&self) -> Values<K, V> {
        Values { inner: self.iter() }
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
        IntoIter { queue: self }
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

#[cfg(test)]
mod tests {
    use std::fmt;

    use rand::{thread_rng, Rng};

    use super::*;

    #[allow(dead_code)]
    fn print_debug<K: fmt::Display + Eq + Hash, V>(queue: &Queue<K, V>) {
        let mut next = queue.head.clone();
        while let Some(next_key) = next {
            let item = queue.list.get::<K>(&next_key).expect("item").state();

            if let Some(prev_key) = item.prev.as_ref() {
                print!("{}-", prev_key);
            }

            next = item.next.clone();
            if let Some(next_key) = &next {
                print!("-{}", next_key);
            }

            print!(" ");
        }

        println!();
    }

    fn validate<K: fmt::Debug + Eq + Hash, V>(queue: &Queue<K, V>) {
        if queue.list.is_empty() {
            assert!(queue.head.is_none(), "head is {:?}", queue.head);
            assert!(queue.tail.is_none(), "tail is {:?}", queue.tail);
        } else {
            let first_key = queue.head.as_ref().expect("first key");
            let first = queue.list.get::<K>(first_key).expect("first item");

            assert!(first.state.borrow().prev.is_none());

            let last_key = queue.tail.as_ref().expect("last key");
            let last = queue.list.get::<K>(last_key).expect("last item");
            assert!(last.state.borrow().next.is_none());
        }

        let mut last = None;
        let mut next = queue.head.clone();
        while let Some(key) = next {
            let item = queue.list.get::<K>(&key).expect("item");

            if let Some(last_key) = &last {
                let item_state = item.state.borrow();
                let prev_key = item_state.prev.as_ref().expect("previous key");
                assert_eq!(last_key, prev_key);
            }

            last = Some(key);
            next = item.state.borrow().next.clone();
        }
    }

    #[test]
    fn test_order() {
        let mut queue = Queue::new();
        let expected: Vec<i32> = (0..10).collect();

        for i in expected.iter() {
            queue.insert(*i, i.to_string());
            validate(&queue);
        }

        let mut actual = Vec::with_capacity(expected.len());
        for (i, s) in queue.iter() {
            assert_eq!(&i.to_string(), s);
            actual.push(i);
        }

        assert_eq!(actual.len(), expected.len());
        assert!(actual.iter().zip(expected).all(|(l, r)| **l == r))
    }

    #[test]
    fn test_access() {
        let mut queue = Queue::new();
        validate(&queue);

        let mut rng = thread_rng();
        for _ in 1..100_000 {
            let i: i32 = rng.gen_range(0..1000);
            queue.insert(i, i.to_string());
            validate(&queue);

            let mut size = 0;
            for _ in queue.iter() {
                size += 1;
            }

            assert_eq!(queue.len(), size);
            assert!(!queue.is_empty());

            let i: i32 = rng.gen_range(0..1000);
            queue.remove(&i);
            validate(&queue);

            let mut size = 0;
            for _ in queue.iter() {
                size += 1;
            }

            while !queue.is_empty() {
                queue.pop_last();
                validate(&queue);
                size -= 1;
                assert_eq!(queue.len(), size);
            }

            assert_eq!(queue.len(), 0);
        }
    }
}
