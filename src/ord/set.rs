//! A hash set ordered by key using a linked list.
//!
//! Example:
//! ```
//! use std::sync::Arc;
//!
//! use ds_ext::ord::LinkedHashSet;
//!
//! let mut set1 = LinkedHashSet::new();
//! assert!(set1.insert("d"));
//! assert!(set1.insert("a"));
//! assert!(set1.insert("c"));
//! assert!(set1.insert("b"));
//! assert!(!set1.insert("a"));
//! assert_eq!(set1.len(), 4);
//!
//! let mut set2 = set1.clone();
//! assert!(set2.remove(&"d"));
//! assert_eq!(set2.len(), 3);
//!
//! assert_eq!(**set1.difference(&set2).next().expect("diff"), "d");
//! assert_eq!(
//!     set1.intersection(&set2).map(|s| **s).collect::<LinkedHashSet<&str>>(),
//!     set2
//! );
//!
//! assert_eq!(
//!     set1.into_iter().map(|s| &**s).collect::<Vec<&str>>(),
//!     ["a", "b", "c", "d"]
//! );
//!
//! assert_eq!(
//!     set2.into_iter().map(|s| &**s).collect::<Vec<&str>>(),
//!     ["a", "b", "c"]
//! );
//! ```

use core::fmt;
use std::borrow::Borrow;
use std::cmp::Ordering;
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

/// An iterator over the values in a [`LinkedHashSet`]
pub struct Iter<'a, T> {
    inner: super::list::Iter<'a, Arc<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

/// A [`std::collections::HashSet`] ordered by key using a [`List`].
///
/// This implements `Deref` so that the standard comparison methods are still available.
pub struct LinkedHashSet<T> {
    inner: Inner<Arc<T>>,
    order: List<Arc<T>>,
}

impl<T> Clone for LinkedHashSet<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            order: self.order.clone(),
        }
    }
}

impl<T: PartialEq> PartialEq for LinkedHashSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order
    }
}

impl<T: Eq> Eq for LinkedHashSet<T> {}

impl<T> Deref for LinkedHashSet<T> {
    type Target = Inner<Arc<T>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> LinkedHashSet<T> {
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
        debug_assert!(self.is_valid());

        let new = if self.inner.contains(&value) {
            false
        } else {
            let value = Arc::new(value);

            let index = bisect(&self.order, &value);
            if index == self.len() {
                self.order.insert(index, value.clone());
            } else {
                let prior = self.order.get(index).expect("value");
                if prior < &value {
                    self.order.insert(index + 1, value.clone());
                } else {
                    self.order.insert(index, value.clone());
                }
            }

            self.inner.insert(value)
        };

        debug_assert!(self.is_valid());

        new
    }

    /// Construct an iterator over the values in this [`LinkedHashSet`].
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: self.order.iter(),
        }
    }

    /// Remove and return the first value in this [`LinkedHashSet`].
    pub fn pop_first(&mut self) -> Option<Arc<T>> {
        debug_assert!(self.is_valid());

        if let Some(value) = self.order.pop_front() {
            self.inner.remove(&value);
            debug_assert!(self.is_valid());
            Some(value)
        } else {
            None
        }
    }

    /// Remove and return the last value in this [`LinkedHashSet`].
    pub fn pop_last(&mut self) -> Option<Arc<T>> {
        if let Some(value) = self.order.pop_back() {
            self.inner.remove(&value);
            Some(value)
        } else {
            None
        }
    }

    /// Remove the given `value` from this [`LinkedHashSet`] and return `true` if it was present.
    ///
    /// The value may be any borrowed form of `T`,
    /// but the ordering on the borrowed form **must** match the ordering of `T`.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        Arc<T>: Borrow<Q>,
        Q: Eq + Hash + Ord,
    {
        debug_assert!(self.is_valid());

        if self.inner.remove(value) {
            let index = bisect(&self.order, value);
            assert!(self.order.remove(index).expect("removed").borrow() == value);
            debug_assert!(self.is_valid());
            true
        } else {
            false
        }
    }

    fn is_valid(&self) -> bool {
        assert_eq!(self.inner.len(), self.order.len());

        if self.is_empty() {
            return true;
        }

        let mut value = self.order.get(0).expect("value");
        for i in 1..self.len() {
            let next = self.order.get(i).expect("next");
            assert!(value <= next, "set out of order: {:?}", self);
            assert!(next >= value);
            value = next;
        }

        true
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> fmt::Debug for LinkedHashSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[ ")?;

        for value in self {
            write!(f, "{:?} ", value)?;
        }

        f.write_str("]")
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> FromIterator<T> for LinkedHashSet<T> {
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

impl<'a, T: Hash + Ord + fmt::Debug> IntoIterator for &'a LinkedHashSet<T> {
    type Item = &'a Arc<T>;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        LinkedHashSet::iter(self)
    }
}

#[inline]
fn bisect<T, Q>(list: &List<T>, target: &Q) -> usize
where
    T: Borrow<Q> + Ord,
    Q: Ord,
{
    let mut lo = 0;
    let mut hi = list.len();

    while lo < hi {
        let mid = (lo + hi) >> 1;
        let value = list.get(mid).expect("value").borrow();

        match value.cmp(target) {
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid,
            Ordering::Equal => return mid,
        }
    }

    lo
}
