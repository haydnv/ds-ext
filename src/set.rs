//! A hash set ordered using a linked list.
//!
//! Example:
//! ```
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
//! assert_eq!(
//!     set1.into_iter().collect::<Vec<&str>>(),
//!     ["a", "b", "c", "d"]
//! );
//!
//! assert_eq!(
//!     set2.into_iter().rev().collect::<Vec<&str>>(),
//!     ["c", "b", "a"]
//! );
//! ```

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::HashSet as Inner;
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

use get_size::GetSize;
use get_size_derive::*;

use super::list::List;

/// An iterator to drain the contents of a [`OrdHashSet`]
pub struct Drain<'a, T> {
    inner: &'a mut Inner<Arc<T>>,
    order: super::list::Drain<'a, Arc<T>>,
}

impl<'a, T> Iterator for Drain<'a, T>
where
    T: Eq + Hash + fmt::Debug,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.order.next()?;
        self.inner.remove(&*item);
        Some(Arc::try_unwrap(item).expect("item"))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.order.size_hint()
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T>
where
    T: Eq + Hash + fmt::Debug,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let item = self.order.next_back()?;
        self.inner.remove(&*item);
        Some(Arc::try_unwrap(item).expect("item"))
    }
}

/// An iterator over the contents of a [`OrdHashSet`]
pub struct IntoIter<T> {
    inner: super::list::IntoIter<Arc<T>>,
}

impl<T: fmt::Debug> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|item| Arc::try_unwrap(item).expect("item"))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T: fmt::Debug> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_back()
            .map(|item| Arc::try_unwrap(item).expect("item"))
    }
}

/// An iterator over the items in a [`OrdHashSet`]
pub struct Iter<'a, T> {
    inner: super::list::Iter<'a, Arc<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|item| &**item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|item| &**item)
    }
}

/// A [`std::collections::HashSet`] ordered using a [`List`].
#[derive(GetSize)]
pub struct OrdHashSet<T> {
    inner: Inner<Arc<T>>,
    order: List<Arc<T>>,
}

impl<T: Clone + Eq + Hash + Ord + fmt::Debug> Clone for OrdHashSet<T> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T: PartialEq + fmt::Debug> PartialEq for OrdHashSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order
    }
}

impl<T: Eq + fmt::Debug> Eq for OrdHashSet<T> {}

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

    /// Construct an iterator over the items in this [`OrdHashSet`].
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: self.order.iter(),
        }
    }

    /// Return `true` if this [`OrdHashSet`] is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Return the number of items in this [`OrdHashSet`].
    pub fn len(&self) -> usize {
        self.inner.len()
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
            let item = self.order.get(mid).expect("item");

            if cmp(&**item).is_some() {
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
            let item = self.order.get(mid).expect("item");

            if cmp(&**item).is_some() {
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
            let item = self.order.get(mid).expect("item");

            if let Some(order) = cmp(&**item) {
                match order {
                    Ordering::Less => hi = mid,
                    Ordering::Equal => return Some(item),
                    Ordering::Greater => lo = mid + 1,
                }
            } else {
                panic!("comparison does not match distribution")
            }
        }

        None
    }

    /// Bisect this set to match an item using the provided comparison, and return it (if present).
    ///
    /// The first item for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered items (where `cmp(item).is_none()`)
    /// are ordered at the beginning or end of the set.
    pub fn bisect<Cmp>(&self, cmp: Cmp) -> Option<&T>
    where
        Cmp: Fn(&T) -> Option<Ordering> + Copy,
    {
        let lo = self.bisect_lo(cmp);
        let hi = self.bisect_hi(cmp);
        self.bisect_inner(cmp, lo, hi)
    }

    /// Bisect this set to match and remove an item using the provided comparison.
    ///
    /// The first item for which the comparison returns `Some(Ordering::Equal)` will be returned.
    /// This method assumes that any partially-ordered items (where `cmp(item).is_none()`)
    /// are ordered at the beginning and/or end of the set.
    pub fn bisect_and_remove<Cmp>(&mut self, cmp: Cmp) -> Option<T>
    where
        Cmp: Fn(&T) -> Option<Ordering> + Copy,
        T: fmt::Debug,
    {
        let mut lo = self.bisect_lo(cmp);
        let mut hi = self.bisect_hi(cmp);

        let item = loop {
            if lo >= hi {
                break None;
            }

            let mid = (lo + hi) >> 1;
            let item = self.order.get(mid).expect("item");

            if let Some(order) = cmp(&**item) {
                match order {
                    Ordering::Less => hi = mid,
                    Ordering::Equal => {
                        lo = mid;
                        break Some(item.clone());
                    }
                    Ordering::Greater => lo = mid + 1,
                }
            } else {
                panic!("comparison does not match distribution")
            }
        }?;

        self.order.remove(lo);
        self.inner.remove(&item);

        Some(Arc::try_unwrap(item).expect("item"))
    }

    /// Remove all items from this [`OrdHashSet`].
    pub fn clear(&mut self) {
        self.inner.clear();
        self.order.clear();
    }

    /// Drain all items from this [`OrdHashSet`].
    pub fn drain(&mut self) -> Drain<T> {
        Drain {
            inner: &mut self.inner,
            order: self.order.drain(),
        }
    }

    /// Consume the given `iter` and insert all its items into this [`OrdHashSet`]
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.insert(item);
        }
    }

    /// Borrow the first item in this [`OrdHashSet`].
    pub fn first(&self) -> Option<&T> {
        self.order.front().map(|item| &**item)
    }

    /// Insert an `item` into this [`OrdHashSet`] and return `false` if it was already present.
    pub fn insert(&mut self, item: T) -> bool {
        let new = if self.inner.contains(&item) {
            false
        } else {
            let item = Arc::new(item);

            let index = bisect(&self.order, &item);
            if index == self.len() {
                self.order.insert(index, item.clone());
            } else {
                let prior = self.order.get(index).expect("item").clone();

                if &prior < &item {
                    self.order.insert(index + 1, item.clone());
                } else {
                    self.order.insert(index, item.clone());
                }
            }

            self.inner.insert(item)
        };

        new
    }

    /// Borrow the last item in this [`OrdHashSet`].
    pub fn last(&self) -> Option<&T> {
        self.order.back().map(|item| &**item)
    }

    /// Remove and return the first item in this [`OrdHashSet`].
    pub fn pop_first(&mut self) -> Option<T>
    where
        T: fmt::Debug,
    {
        if let Some(item) = self.order.pop_front() {
            self.inner.remove(&item);
            Some(Arc::try_unwrap(item).expect("item"))
        } else {
            None
        }
    }

    /// Remove and return the last item in this [`OrdHashSet`].
    pub fn pop_last(&mut self) -> Option<T>
    where
        T: fmt::Debug,
    {
        if let Some(item) = self.order.pop_back() {
            self.inner.remove(&item);
            Some(Arc::try_unwrap(item).expect("item"))
        } else {
            None
        }
    }

    /// Remove the given `item` from this [`OrdHashSet`] and return `true` if it was present.
    ///
    /// The item may be any borrowed form of `T`,
    /// but the ordering on the borrowed form **must** match the ordering of `T`.
    pub fn remove<Q>(&mut self, item: &Q) -> bool
    where
        Arc<T>: Borrow<Q>,
        Q: Eq + Hash + Ord,
    {
        if self.inner.remove(item) {
            let index = bisect(&self.order, item);
            assert!(self.order.remove(index).expect("removed").borrow() == item);
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
            if this.next() != Some(item) {
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

        let mut item = self.order.get(0).expect("item");
        for i in 1..self.len() {
            let next = self.order.get(i).expect("next");
            assert!(*item <= *next, "set out of order: {:?}", self);
            assert!(*next >= *item);
            item = next;
        }

        true
    }
}

impl<T: Eq + Hash + Ord + fmt::Debug> fmt::Debug for OrdHashSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[ ")?;

        for item in self {
            write!(f, "{:?} ", item)?;
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

impl<T: fmt::Debug> IntoIterator for OrdHashSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.order.into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a OrdHashSet<T> {
    type Item = &'a T;
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
        let item = &*list.get(mid).expect("item");

        match item.borrow().cmp(target) {
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

        assert!(set.bisect_and_remove(|item| item.partial_cmp(&8)).is_none());

        set.insert(8);
        assert!(set.bisect_and_remove(|item| item.partial_cmp(&8)).is_some());
        assert!(set.bisect_and_remove(|item| item.partial_cmp(&8)).is_none());

        set.insert(9);
        assert!(set.bisect_and_remove(|item| item.partial_cmp(&8)).is_none());

        set.insert(7);
        assert!(set.bisect_and_remove(|item| item.partial_cmp(&8)).is_none());
    }

    #[test]
    fn test_into_iter() {
        let mut set = OrdHashSet::new();
        assert!(set.insert("d"));
        assert!(set.insert("a"));
        assert!(set.insert("c"));
        assert!(set.insert("b"));
        assert!(!set.insert("a"));
        assert_eq!(set.len(), 4);

        assert_eq!(set.into_iter().collect::<Vec<&str>>(), ["a", "b", "c", "d"]);
    }

    #[test]
    fn test_drain() {
        let mut set = OrdHashSet::from_iter(0..10);
        let expected = (0..10).into_iter().collect::<Vec<_>>();
        let actual = set.drain().collect::<Vec<_>>();
        assert_eq!(expected, actual);
    }
}
