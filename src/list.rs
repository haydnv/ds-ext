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
use std::ops::{Deref, DerefMut, Index, IndexMut, RangeBounds};

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
    next: Option<&'a usize>,
    stop: Option<&'a usize>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next?;
        let node = self.inner.get(next).expect("next");

        self.next = if self.stop == Some(next) {
            None
        } else {
            node.next.as_ref()
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
        let node = self.inner.get(next).expect("next");

        self.stop = if self.next == Some(next) {
            None
        } else {
            node.prev.as_ref()
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
    /// Create a new empty [`List`].
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back(&self) -> Option<&T> {
        self.inner.get(&usize::MAX).map(Deref::deref)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut(&usize::MAX).map(DerefMut::deref_mut)
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
            let ordinal = bisect_left(&self.inner, self.len(), 0, usize::MAX, index);
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
            let ordinal = bisect_left(&self.inner, self.len(), 0, usize::MAX, index);
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
                    let ordinal = bisect(&self.inner, self.len(), 0, usize::MAX, index);
                    self.insert_inner(ordinal, value)
                }
            },
        }
    }

    /// Iterate over all elements in this [`List`].
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: &self.inner,
            next: self.inner.keys().next(),
            stop: self.inner.keys().last(),
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
        todo!()
    }

    /// Remove and return the value at the given `index`, if any.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        todo!()
    }

    /// Remove and return the last value in this [`List`].
    pub fn pop_back(&mut self) -> Option<T> {
        todo!()
    }

    /// Remove and return the first value in this [`List`].
    pub fn pop_front(&mut self) -> Option<T> {
        todo!()
    }

    /// Append the given `value` to the back of this [`List`].
    pub fn push_back(&mut self, value: T) {
        todo!()
    }

    /// Append the given `value` to the front of this [`List`].
    pub fn push_front(&mut self, value: T) {
        todo!()
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
            let ordinal = bisect_left(&self.inner, self.len(), 0, usize::MAX, index);

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
            let ordinal = bisect_left(&self.inner, self.len(), 0, usize::MAX, index);

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
        let next = self.inner.keys().next().copied();
        let last = self.inner.keys().last().copied();

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

/// determine an open position such that there are `cardinal` number of elements to its left
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
            let pivot = partition_inner(nodes, lo, hi);
            bisect(nodes, half, lo, pivot, cardinal)
        }
        Ordering::Greater => {
            let pivot = partition_inner(nodes, lo, hi);
            bisect(nodes, half, hi, pivot, cardinal - half)
        }
    }
}

/// determine the ordinal at index `cardinal`
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
        Ordering::Equal => partition(nodes, lo, hi).0,
        Ordering::Less => {
            let pivot = partition_inner(nodes, lo, hi);
            bisect_left(nodes, half, lo, pivot, cardinal)
        }
        Ordering::Greater => {
            let pivot = partition_inner(nodes, lo, hi);
            bisect_left(nodes, half, hi, pivot, cardinal - half)
        }
    }
}

/// find an unfilled position with half of the given range on each side
#[inline]
fn partition<T>(nodes: &HashMap<usize, Node<T>>, lo: usize, hi: usize) -> (usize, usize, usize) {
    let mid = (lo + hi) >> 1;

    if let Some(node) = nodes.get(&mid) {
        match (node.prev, node.next) {
            (Some(_), Some(_)) => {
                let lo = partition_inner(nodes, lo, mid);
                let hi = partition_inner(nodes, mid, hi);
                partition(nodes, lo, hi)
            }
            _ => unreachable!("inner node without two neighbors"),
        }
    } else {
        (lo, mid, hi)
    }
}

/// determine an ordinal to partition the given range such that half its elements lie on each side
#[inline]
fn partition_inner<T>(nodes: &HashMap<usize, Node<T>>, lo: usize, hi: usize) -> usize {
    let mid = (lo + hi) >> 1;

    if let Some(node) = nodes.get(&mid) {
        match (node.prev, node.next) {
            (Some(_), Some(_)) => {
                let lo = partition_inner(nodes, lo, mid);
                let hi = partition_inner(nodes, mid, hi);
                partition_inner(nodes, lo, hi)
            }
            _ => unreachable!("inner node without two neighbors"),
        }
    } else {
        mid
    }
}
