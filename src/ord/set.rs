/// A hash set ordered by key using a linked list
use std::collections::HashSet as Inner;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

use super::list::List;

/// An iterator over the contents of a [`LinkedHashSet`]
pub struct IntoIter<T> {
    inner: super::list::IntoIter<Arc<T>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An iterator over the values in a [`LinkedHashSet`]
pub struct Iter<'a, T> {
    inner: super::list::Iter<'a, Arc<T>>,
}

/// A [`std::collections::HashSet`] ordered by key using a [`List`]
pub struct LinkedHashSet<T> {
    inner: Inner<Arc<T>>,
    order: List<Arc<T>>,
}

impl<T> Deref for LinkedHashSet<T> {
    type Target = Inner<Arc<T>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Hash> LinkedHashSet<T> {
    /// Construct a new [`LinkedHashSet`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
            order: List::new(),
        }
    }

    /// Construct a new [`LinkedHashSet`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
            order: List::with_capacity(capacity),
        }
    }

    /// Remove all values from this [`LinkedHashSet`]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Consume the given `iter` and insert all its values into this [`LinkedHashSet`]
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.insert(item);
        }
    }

    /// Insert a `value` into this [`LinkedHashSet`] and return `false` if it was already present.
    pub fn insert(&mut self, value: T) -> bool {
        todo!()
    }

    /// Construct an iterator over the values in this [`LinkedHashSet`].
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: self.order.iter(),
        }
    }

    /// Remove and return the first value in this [`LinkedHashSet`].
    pub fn pop_first(&self) -> T {
        todo!()
    }

    /// Remove and return the last value in this [`LinkedHashSet`].
    pub fn pop_last(&self) -> T {
        todo!()
    }
}

impl<T: Hash> FromIterator<T> for LinkedHashSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut set = match iter.size_hint() {
            (_, Some(max)) => Self::with_capacity(max),
            (min, None) if min > 0 => Self::with_capacity(min),
            _ => Self::new(),
        };

        set.extend(iter);
        set
    }
}

impl<T> IntoIterator for LinkedHashSet<T> {
    type Item = Arc<T>;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.order.into_iter(),
        }
    }
}
