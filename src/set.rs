//! A hash set ordered by key using a linked list.
//!
//! Example:
//! ```
//! use std::sync::Arc;
//!
//! use ds_ext::OrdHashSet;
//!
//! let mut set1 = OrdHashSet::new();
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
//!     set1.intersection(&set2).map(|s| **s).collect::<OrdHashSet<&str>>(),
//!     set2
//! );
//!
//! assert_eq!(
//!     set1.into_iter().map(|s| &**s).collect::<Vec<&str>>(),
//!     ["a", "b", "c", "d"]
//! );
//!
//! assert_eq!(
//!     set2.into_iter().rev().map(|s| &**s).collect::<Vec<&str>>(),
//!     ["c", "b", "a"]
//! );
//! ```

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::HashSet as Inner;
use std::fmt;
use std::hash::Hash;
use std::ops::Deref;
use std::sync::Arc;

use get_size::GetSize;
use get_size_derive::*;

use super::list::List;

/// An iterator to drain the contents of a [`OrdHashSet`]
pub struct Drain<'a, T> {
    inner: super::list::Drain<'a, Arc<T>>,
}

impl<'a, T: fmt::Debug> Iterator for Drain<'a, T> {
    type Item = Arc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T: fmt::Debug> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

/// An iterator over the contents of a [`OrdHashSet`]
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

/// An iterator over the values in a [`OrdHashSet`]
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
#[derive(GetSize)]
pub struct OrdHashSet<T> {
    inner: Inner<Arc<T>>,
    order: List<Arc<T>>,
}

impl<T> Clone for OrdHashSet<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            order: self.order.clone(),
        }
    }
}

impl<T: PartialEq + fmt::Debug> PartialEq for OrdHashSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order
    }
}

impl<T: Eq + fmt::Debug> Eq for OrdHashSet<T> {}

impl<T> Deref for OrdHashSet<T> {
    type Target = Inner<Arc<T>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> OrdHashSet<T> {
    /// Construct a new [`OrdHashSet`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
            order: List::new(),
        }
    }

    /// Construct a new [`OrdHashSet`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
            order: List::with_capacity(capacity),
        }
    }

    /// Construct an iterator over the values in this [`OrdHashSet`].
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: self.order.iter(),
        }
    }
}

impl<T: Eq + Hash + Ord> OrdHashSet<T> {
    fn bisect_hi<Cmp>(&self, cmp: Cmp) -> usize
    where
        Cmp: Fn(&T) -> Option<Ordering>,
    {
        if self.is_empty() {
            return 0;
        } else if cmp(self.order.back().expect("tail")).is_some() {
            return self.len();
        }

        let mut lo = 0;
        let mut hi = self.len();

        while lo < hi {
            let mid = (lo + hi) >> 1;
            let value = self.order.get(mid).expect("value");

            if cmp(&**value).is_some() {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        hi
    }

    fn bisect_lo<Cmp>(&self, cmp: Cmp) -> usize
    where
        Cmp: Fn(&T) -> Option<Ordering>,
    {
        if self.is_empty() {
            return 0;
        } else if cmp(self.order.front().expect("head")).is_some() {
            return 0;
        }

        let mut lo = 0;
        let mut hi = 1;

        while lo < hi {
            let mid = (lo + hi) >> 1;
            let value = self.order.get(mid).expect("value");

            if cmp(&**value).is_some() {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        hi
    }

    fn bisect_inner<Cmp>(&self, cmp: Cmp, mut lo: usize, mut hi: usize) -> Option<&T>
    where
        Cmp: Fn(&T) -> Option<Ordering>,
    {
        while lo < hi {
            let mid = (lo + hi) >> 1;
            let key = self.order.get(mid).expect("key");

            if let Some(order) = cmp(&**key) {
                match order {
                    Ordering::Less => hi = mid,
                    Ordering::Equal => return Some(key),
                    Ordering::Greater => lo = mid + 1,
                }
            } else {
                panic!("comparison does not match key distribution")
            }
        }

        None
    }

    /// Bisect this set to match a key using the provided comparison, and return its value (if any).
    ///
    /// The first key for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered keys (where `cmp(key).is_none()`) lie at the
    /// beginning and/or end of the distribution.
    pub fn bisect<Cmp>(&self, cmp: Cmp) -> Option<&T>
    where
        Cmp: Fn(&T) -> Option<Ordering> + Copy,
    {
        let lo = self.bisect_lo(cmp);
        let hi = self.bisect_hi(cmp);
        self.bisect_inner(cmp, lo, hi)
    }

    /// Bisect this set to match and remove a key using the provided comparison.
    ///
    /// The first key for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered keys (where `cmp(key).is_none()`) lie at the
    /// beginning and/or end of the distribution.
    pub fn bisect_and_remove<Cmp>(&mut self, cmp: Cmp) -> Option<Arc<T>>
    where
        Cmp: Fn(&T) -> Option<Ordering> + Copy,
    {
        let mut lo = self.bisect_lo(cmp);
        let mut hi = self.bisect_hi(cmp);

        let key = loop {
            if lo >= hi {
                break None;
            }

            let mid = (lo + hi) >> 1;
            let key = self.order.get(mid).expect("key");

            if let Some(order) = cmp(&**key) {
                match order {
                    Ordering::Less => hi = mid,
                    Ordering::Equal => {
                        lo = mid;
                        break Some(key.clone());
                    }
                    Ordering::Greater => lo = mid + 1,
                }
            } else {
                panic!("comparison does not match key distribution")
            }
        }?;

        self.order.remove(lo);
        self.inner.remove(&key);
        Some(key)
    }

    /// Remove all values from this [`OrdHashSet`].
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Drain all values from this [`OrdHashSet`].
    pub fn drain(&mut self) -> Drain<T> {
        self.inner.clear();

        Drain {
            inner: self.order.drain(),
        }
    }

    /// Consume the given `iter` and insert all its values into this [`OrdHashSet`]
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.insert(item);
        }
    }

    /// Borrow the first value in this [`OrdHashSet`].
    pub fn first(&self) -> Option<&Arc<T>> {
        self.order.front()
    }

    /// Insert a `value` into this [`OrdHashSet`] and return `false` if it was already present.
    pub fn insert(&mut self, value: T) -> bool {
        let new = if self.inner.contains(&value) {
            false
        } else {
            let value = Arc::new(value);

            let index = bisect(&self.order, &value);
            if index == self.len() {
                self.order.insert(index, value.clone());
            } else {
                let prior = self.order.get(index).expect("value").clone();
                if &prior < &value {
                    self.order.insert(index + 1, value.clone());
                } else {
                    self.order.insert(index, value.clone());
                }
            }

            self.inner.insert(value)
        };

        new
    }

    /// Borrow the last value in this [`OrdHashSet`].
    pub fn last(&self) -> Option<&Arc<T>> {
        self.order.back()
    }

    /// Remove and return the first value in this [`OrdHashSet`].
    pub fn pop_first(&mut self) -> Option<Arc<T>> {
        if let Some(value) = self.order.pop_front() {
            self.inner.remove(&value);
            Some(value)
        } else {
            None
        }
    }

    /// Remove and return the last value in this [`OrdHashSet`].
    pub fn pop_last(&mut self) -> Option<Arc<T>> {
        if let Some(value) = self.order.pop_back() {
            self.inner.remove(&value);
            Some(value)
        } else {
            None
        }
    }

    /// Remove the given `value` from this [`OrdHashSet`] and return `true` if it was present.
    ///
    /// The value may be any borrowed form of `T`,
    /// but the ordering on the borrowed form **must** match the ordering of `T`.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        Arc<T>: Borrow<Q>,
        Q: Eq + Hash + Ord,
    {
        if self.inner.remove(value) {
            let index = bisect(&self.order, value);
            assert!(self.order.remove(index).expect("removed").borrow() == value);
            true
        } else {
            false
        }
    }

    /// Return `true` if the first elements in this set are equal to those in the given `iter`.
    pub fn starts_with<'a, I: IntoIterator<Item = &'a T>>(&'a self, other: I) -> bool
    where
        T: PartialEq,
    {
        let mut this = self.iter();
        let mut that = other.into_iter();

        while let Some(item) = that.next() {
            if this.next().map(|arc| &**arc) != Some(item) {
                return false;
            }
        }

        true
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> OrdHashSet<T> {
    #[allow(unused)]
    fn is_valid(&self) -> bool {
        assert_eq!(self.inner.len(), self.order.len());

        if self.is_empty() {
            return true;
        }

        let mut value = self.order.get(0).expect("value");
        for i in 1..self.len() {
            let next = self.order.get(i).expect("next");
            assert!(*value <= *next, "set out of order: {:?}", self);
            assert!(*next >= *value);
            value = next;
        }

        true
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> fmt::Debug for OrdHashSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[ ")?;

        for value in self {
            write!(f, "{:?} ", value)?;
        }

        f.write_str("]")
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> FromIterator<T> for OrdHashSet<T> {
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

impl<T> IntoIterator for OrdHashSet<T> {
    type Item = Arc<T>;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.order.into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a OrdHashSet<T> {
    type Item = &'a Arc<T>;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        OrdHashSet::iter(self)
    }
}

#[inline]
fn bisect<T, Q>(list: &List<T>, target: &Q) -> usize
where
    T: Borrow<Q> + Ord,
    Q: Ord,
{
    if let Some(front) = list.front() {
        if target < (*front).borrow() {
            return 0;
        }
    }

    if let Some(last) = list.back() {
        if target > (*last).borrow() {
            return list.len();
        }
    }

    let mut lo = 0;
    let mut hi = list.len();

    while lo < hi {
        let mid = (lo + hi) >> 1;
        let value = &*list.get(mid).expect("value");

        match value.borrow().cmp(target) {
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid,
            Ordering::Equal => return mid,
        }
    }

    lo
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bisect_and_remove() {
        let mut set = OrdHashSet::<u8>::new();

        assert!(set.bisect_and_remove(|key| key.partial_cmp(&8)).is_none());

        set.insert(8);
        assert!(set.bisect_and_remove(|key| key.partial_cmp(&8)).is_some());
        assert!(set.bisect_and_remove(|key| key.partial_cmp(&8)).is_none());

        set.insert(9);
        assert!(set.bisect_and_remove(|key| key.partial_cmp(&8)).is_none());

        set.insert(7);
        assert!(set.bisect_and_remove(|key| key.partial_cmp(&8)).is_none());
    }

    #[test]
    fn test_drain() {
        let mut set = OrdHashSet::from_iter(0..10);
        let expected = (0..10).into_iter().collect::<Vec<_>>();
        let actual = set
            .drain()
            .map(|i| Arc::try_unwrap(i).expect("i"))
            .collect::<Vec<_>>();

        assert_eq!(expected, actual);
    }
}
