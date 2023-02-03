//! A linked list with cardinal indexing and O(log n) get/insert/remove anywhere in the [`List`].
//!
//! The API of [`List`] is designed to resemble [`std::collections::VecDeque`] but [`List`] does
//! not use a `VecDeque`; instead each node in the list is assigned an ordinal value
//! in the range `[0, usize::MAX)`, which is stored in a
//! [`HashMap`](`std::collections::HashMap`) of ordinals to values.
//!
//! This design allows a cardinal index to be resolved to a value in O(log n) time.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::ops::{Bound, Deref, DerefMut, Index, IndexMut, RangeBounds};

macro_rules! assert_bounds {
    ($i:expr, $len:expr) => {
        assert!(
            $i < $len,
            "index {} is out of bounds for a list with length {}",
            $i,
            $len
        )
    };
}

struct Node<T> {
    value: T,
    prev: Option<usize>,
    next: Option<usize>,
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Node<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

/// An iterator over the elements of a [`List`]
pub struct IntoIter<T> {
    inner: HashMap<usize, Node<T>>,
    next: Option<usize>,
    last: Option<usize>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next?;
        let node = self.inner.remove(&next).expect("next");

        self.next = if self.last == Some(next) {
            None
        } else {
            node.next
        };

        if self.next.is_none() {
            self.last = None;
        }

        Some(node.value)
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let next = self.last?;
        let node = self.inner.remove(&next).expect("next");

        self.last = if self.next == Some(next) {
            None
        } else {
            node.prev
        };

        if self.last.is_none() {
            self.next = None;
        }

        Some(node.value)
    }
}

/// An iterator over the elements of a [`List`]
pub struct Iter<'a, T> {
    inner: &'a HashMap<usize, Node<T>>,
    next: Option<usize>,
    stop: Option<usize>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next?;
        let node = self.inner.get(&next).expect("next");

        self.next = if self.stop == Some(next) {
            None
        } else {
            node.next
        };

        if self.next.is_none() {
            self.stop = None;
        }

        Some(&node.value)
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let next = self.stop?;
        let node = self.inner.get(&next).expect("next");

        self.stop = if self.next == Some(next) {
            None
        } else {
            node.prev
        };

        if self.stop.is_none() {
            self.next = None;
        }

        Some(&node.value)
    }
}

/// A linked list with cardinal indexing and O(log n) get/insert/remove by index
pub struct List<T> {
    inner: HashMap<usize, Node<T>>,
}

impl<T> List<T> {
    const MAX_LEN: usize = usize::MAX;

    /// Create a new empty [`List`].
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back(&self) -> Option<&T> {
        let ordinal = if self.len() == 1 { 0 } else { Self::MAX_LEN };
        self.inner.get(&ordinal).map(Deref::deref)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let ordinal = if self.len() == 1 { 0 } else { Self::MAX_LEN };
        self.inner.get_mut(&ordinal).map(DerefMut::deref_mut)
    }

    /// Remove all elements from this [`List`].
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Borrow the first element in this [`List`], if any.
    pub fn front(&self) -> Option<&T> {
        self.inner.get(&0).map(Deref::deref)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut(&0).map(DerefMut::deref_mut)
    }

    /// Borrow the element at the given `index`, if any.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            self.front()
        } else if index == (self.len() - 1) {
            self.back()
        } else if index < self.len() {
            let ordinal = self.ordinal(index);
            self.inner.get(&ordinal).map(Deref::deref)
        } else {
            None
        }
    }

    /// Borrow the element at the given `index` mutably, if any.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index == 0 {
            self.front_mut()
        } else if index == (self.len() - 1) {
            self.back_mut()
        } else if index < self.len() {
            let ordinal = self.ordinal(index);
            self.inner.get_mut(&ordinal).map(DerefMut::deref_mut)
        } else {
            None
        }
    }

    fn insert_inner(&mut self, pos: (usize, usize, usize), value: T) {
        let (prev, ordinal, next) = pos;

        let node = Node {
            value,
            prev: Some(prev),
            next: Some(next),
        };

        {
            let prev = self.inner.get_mut(&prev).expect("prev");
            prev.next = Some(ordinal);
        }

        {
            let next = self.inner.get_mut(&next).expect("next");
            next.prev = Some(ordinal);
        }

        assert!(self.inner.insert(ordinal, node).is_none());
    }

    /// Insert a new `value` at the given `index`.
    pub fn insert(&mut self, index: usize, value: T) {
        match index {
            0 => self.push_front(value),
            i => match self.len().cmp(&i) {
                Ordering::Less => assert_bounds!(index, self.len()),
                Ordering::Equal => self.push_back(value),
                Ordering::Greater => {
                    let pos = bisect(&self.inner, self.len(), 0, Self::MAX_LEN, index);
                    self.insert_inner(pos, value)
                }
            },
        }
    }

    /// Iterate over all elements in this [`List`].
    pub fn iter(&self) -> Iter<T> {
        let next = if self.is_empty() { None } else { Some(0) };
        let stop = if self.len() == 1 {
            Some(0)
        } else {
            Some(Self::MAX_LEN)
        };

        Iter {
            inner: &self.inner,
            next,
            stop,
        }
    }

    /// Return `true` if this [`List`] is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Return the length of this [`List`].
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Iterate over the given `range` of elements in this [`List`].
    pub fn range<R: RangeBounds<usize>>(&self, range: R) -> Iter<T> {
        if self.is_empty() {
            return Iter {
                inner: &self.inner,
                next: None,
                stop: None,
            };
        }

        let next = match range.start_bound() {
            Bound::Unbounded => Some(0),
            Bound::Included(start) => Some(self.ordinal(*start)),
            Bound::Excluded(start) => {
                let ordinal = self.ordinal(*start);
                self.inner.get(&ordinal).expect("node").next
            }
        };

        let last_ordinal = if self.len() == 1 { 0 } else { Self::MAX_LEN };

        let stop = match range.end_bound() {
            Bound::Unbounded => Some(last_ordinal),
            Bound::Included(end) => Some(self.ordinal(*end)),
            Bound::Excluded(end) => {
                let ordinal = self.ordinal(*end);
                self.inner.get(&ordinal).expect("node").prev
            }
        };

        Iter {
            inner: &self.inner,
            next,
            stop,
        }
    }

    /// Remove and return the value at the given `index`, if any.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index == 0 {
            return self.pop_front();
        } else if index == self.len() - 1 {
            return self.pop_back();
        } else if index >= self.len() {
            return None;
        }

        let ordinal = self.ordinal(index);
        let node = self.inner.remove(&ordinal).expect("node");
        let prev = node.prev.expect("prev");
        let next = node.next.expect("next");

        {
            let prev = self.inner.get_mut(&prev).expect("prev");
            prev.next = Some(next);
        }

        {
            let next = self.inner.get_mut(&next).expect("next");
            next.prev = Some(prev);
        }

        Some(node.value)
    }

    /// Remove and return the last value in this [`List`].
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        } else if self.len() == 1 {
            return self.inner.remove(&0).map(|node| node.value);
        }

        let next = self.inner.remove(&Self::MAX_LEN)?;

        match next.prev.as_ref().expect("node") {
            0 => {}
            ordinal => {
                let mut node = self.inner.remove(ordinal).expect("node");
                debug_assert_eq!(node.next, Some(Self::MAX_LEN));
                node.next = None;

                {
                    let prev = node.prev.as_ref().expect("prev");
                    let prev = self.inner.get_mut(prev).expect("prev");
                    prev.next = Some(Self::MAX_LEN);
                }

                self.inner.insert(Self::MAX_LEN, node);
            }
        }

        Some(next.value)
    }

    /// Remove and return the first value in this [`List`].
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let prev = self.inner.remove(&0)?;
        let mut node = self
            .inner
            .remove(prev.next.as_ref().expect("node"))
            .expect("node");

        debug_assert_eq!(node.prev, Some(0));
        node.prev = None;

        self.inner.insert(0, node);

        Some(prev.value)
    }

    /// Append the given `value` to the back of this [`List`].
    pub fn push_back(&mut self, value: T) {
        match self.len() {
            0 => self.push_front(value),
            1 => {
                self.inner.get_mut(&0).expect("front").next = Some(Self::MAX_LEN);

                let node = Node {
                    value,
                    prev: Some(0),
                    next: None,
                };

                self.inner.insert(0, node);
            }
            _ => {
                let node = self.inner.remove(&Self::MAX_LEN).expect("back");
                let prev = node.prev.expect("prev");
                let ordinal = prev + ((Self::MAX_LEN - prev) >> 1);

                {
                    let prev = self.inner.get_mut(&prev).expect("prev");
                    prev.next = Some(ordinal);
                }

                self.inner.insert(ordinal, node);

                let next = Node {
                    value,
                    prev: Some(ordinal),
                    next: None,
                };

                self.inner.insert(Self::MAX_LEN, next);
            }
        }
    }

    /// Append the given `value` to the front of this [`List`].
    pub fn push_front(&mut self, value: T) {
        match self.len() {
            0 => {
                let node = Node {
                    value,
                    prev: None,
                    next: None,
                };

                self.inner.insert(0, node);
            }
            1 => {
                let mut back = self.inner.remove(&0).expect("back");
                back.prev = Some(0);

                let front = Node {
                    value,
                    prev: None,
                    next: Some(Self::MAX_LEN),
                };

                self.inner.insert(0, front);
                self.inner.insert(Self::MAX_LEN, back);
            }
            _ => {
                let mut next = self.inner.remove(&0).expect("next");
                let ordinal = next.next.expect("next") >> 1;
                next.prev = Some(0);

                let front = Node {
                    value,
                    prev: None,
                    next: Some(ordinal),
                };

                self.inner.insert(0, front);
                self.inner.insert(ordinal, next);
            }
        }
    }

    fn ordinal(&self, cardinal: usize) -> usize {
        assert_bounds!(cardinal, self.len());

        if cardinal == 0 {
            0
        } else if cardinal == self.len() - 1 {
            if self.len() == 1 {
                0
            } else {
                Self::MAX_LEN
            }
        } else {
            bisect_left(&self.inner, self.len(), 0, Self::MAX_LEN, cardinal)
        }
    }
}

impl<T> Extend<T> for List<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter.into_iter() {
            self.push_back(item);
        }
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let source = iter.into_iter();
        let mut list = List::new();

        for item in source {
            list.push_back(item);
        }

        list
    }
}

impl<T> Index<usize> for List<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        assert_bounds!(index, self.len());

        if index == 0 {
            self.front().expect("first element")
        } else if index == self.len() - 1 {
            self.back().expect("last element")
        } else {
            let ordinal = self.ordinal(index);
            self.inner.get(&ordinal).map(Deref::deref).expect("element")
        }
    }
}

impl<T> IndexMut<usize> for List<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert_bounds!(index, self.len());

        if index == 0 {
            self.front_mut().expect("first element")
        } else if index == self.len() - 1 {
            self.back_mut().expect("last element")
        } else {
            let ordinal = self.ordinal(index);

            self.inner
                .get_mut(&ordinal)
                .map(DerefMut::deref_mut)
                .expect("element")
        }
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let next = if self.is_empty() { None } else { Some(0) };
        let last = if self.len() == 1 {
            Some(0)
        } else {
            Some(Self::MAX_LEN)
        };

        IntoIter {
            inner: self.inner,
            next,
            last,
        }
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// it's ok to inline these recursive functions, just like it's ok to unroll an infinite loop

/// find the open position in the given ordinal range
/// such that there are `cardinal` number of elements to its left
#[inline]
fn bisect<T>(
    nodes: &HashMap<usize, Node<T>>,
    len: usize,
    lo: usize,
    hi: usize,
    cardinal: usize,
) -> (usize, usize, usize) {
    debug_assert!(
        cardinal < len,
        "cardinal {} is out of bounds for length {}",
        cardinal,
        len
    );

    let half = len >> 1;
    match cardinal.cmp(&half) {
        Ordering::Equal => partition(nodes, lo, hi),
        Ordering::Less => {
            let pivot = median(nodes, lo, hi);
            bisect(nodes, half, lo, pivot, cardinal)
        }
        Ordering::Greater => {
            let pivot = median(nodes, lo, hi);
            bisect(nodes, half, hi, pivot, cardinal - half)
        }
    }
}

/// find the ordinal of index `cardinal` within the given ordinal range
#[inline]
fn bisect_left<T>(
    nodes: &HashMap<usize, Node<T>>,
    len: usize,
    lo: usize,
    hi: usize,
    cardinal: usize,
) -> usize {
    debug_assert!(
        cardinal < len,
        "cardinal {} is out of bounds for length {}",
        cardinal,
        len
    );

    let half = len >> 1;
    match cardinal.cmp(&half) {
        Ordering::Equal => median(nodes, lo, hi),
        Ordering::Less => {
            let pivot = median(nodes, lo, hi);
            bisect_left(nodes, half, lo, pivot, cardinal)
        }
        Ordering::Greater => {
            let pivot = median(nodes, lo, hi);
            bisect_left(nodes, half, hi, pivot, cardinal - half)
        }
    }
}

/// find the unfilled position with half of the given ordinal range on each side
#[inline]
fn partition<T>(nodes: &HashMap<usize, Node<T>>, lo: usize, hi: usize) -> (usize, usize, usize) {
    debug_assert!(nodes.contains_key(&lo));
    debug_assert!(nodes.contains_key(&hi));

    let mid = lo + ((hi - lo) >> 1);

    if let Some(node) = nodes.get(&mid) {
        match (node.prev, node.next) {
            (Some(_), Some(_)) => {
                let lo = median(nodes, lo, mid);
                let hi = median(nodes, mid, hi);
                partition(nodes, lo, hi)
            }
            _ => unreachable!("inner node without two neighbors"),
        }
    } else {
        (lo, mid, hi)
    }
}

/// find the filled ordinal at the median of the given ordinal range
#[inline]
fn median<T>(nodes: &HashMap<usize, Node<T>>, lo: usize, hi: usize) -> usize {
    debug_assert!(nodes.contains_key(&lo));
    debug_assert!(nodes.contains_key(&hi));

    let mid = lo + ((hi - lo) >> 1);

    if let Some(node) = nodes.get(&mid) {
        match (node.prev, node.next) {
            (Some(_), Some(_)) => {
                let lo = median(nodes, lo, mid);
                let hi = median(nodes, mid, hi);
                median(nodes, lo, hi)
            }
            _ => unreachable!("inner node without two neighbors"),
        }
    } else {
        lo
    }
}
