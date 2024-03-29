//! A linked ord with cardinal indexing and O(log n) get/insert/remove anywhere in the [`List`].
//!
//! The API of [`List`] is designed to resemble [`std::collections::VecDeque`] but [`List`] does
//! not use a `VecDeque`; instead each node in the ord is assigned an ordinal value
//! in the range `[0, usize::MAX >> 1)`, which is stored in a
//! [`HashMap`](`std::collections::HashMap`) of ordinals to values.
//!
//! This design allows a cardinal index to be resolved to a value in O(log n) time.
//!
//! [`List`] is optimized to handle a random insertion order. A `Vec` or `VecDeque` offers better
//! performance in situations where inserts are append-only or append- and prepend- only.
//!
//! Example:
//! ```
//! use ds_ext::List;
//!
//! let mut list = List::new();
//!
//! list.push_front("zero");
//! assert_eq!(list.len(), 1);
//!
//! assert_eq!(list.pop_front(), Some("zero"));
//! assert_eq!(list.len(), 0);
//! assert!(list.get(0).is_none());
//!
//! list.push_back("zero");
//! assert_eq!(list.len(), 1);
//! assert_eq!(*list.get(0).expect("0"), "zero");
//!
//! assert_eq!(list.pop_back(), Some("zero"));
//! assert_eq!(list.len(), 0);
//! assert!(list.get(0).is_none());
//!
//! list.push_front("zero");
//! list.push_back("three");
//! list.insert(1, "two point five");
//! list.insert(1, "one");
//! list.insert(2, "two");
//!
//! assert_eq!(list.remove(3), Some("two point five"));
//! assert_eq!(list.len(), 4);
//! assert_eq!(list.iter().size_hint(), (4, Some(4)));
//! assert_eq!(list.range(1..3).size_hint(), (2, Some(2)));
//! assert_eq!(list.range(1..3).map(|s| *s).collect::<Vec<_>>(), ["one", "two"]);
//! assert_eq!(list.into_iter().collect::<Vec<_>>(), ["zero", "one", "two", "three"]);
//! ```

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::ops::{Bound, RangeBounds};

use get_size::GetSize;
use get_size_derive::*;

use super::tree::Tree;

const MAX_LEN: usize = 2 << 31;

macro_rules! assert_bounds {
    ($i:expr, $len:expr) => {
        assert!(
            $i < $len,
            "index {} is out of bounds for a ord with length {}",
            $i,
            $len
        )
    };
}

#[derive(Clone, Debug, GetSize)]
struct Node<T> {
    value: T,
    prev: Option<usize>,
    next: Option<usize>,
}

impl<T> Node<T> {
    fn new(value: T, prev: Option<usize>, next: Option<usize>) -> Self {
        Self { value, prev, next }
    }
}

impl<T> Node<T> {
    fn into_value(self) -> T {
        self.value
    }
}

#[derive(Clone, Debug, GetSize)]
struct Inner<T> {
    list: HashMap<usize, Node<T>>,
    tree: Tree,
}

impl<T> Inner<T> {
    fn new() -> Self {
        Self {
            list: HashMap::new(),
            tree: Tree::new(),
        }
    }

    fn with_capacity(capacity: usize) -> Self {
        Self {
            list: HashMap::with_capacity(capacity),
            tree: Tree::with_capacity(capacity),
        }
    }

    fn clear(&mut self) {
        self.list.clear();
        self.tree.clear();

        debug_assert!(self.is_valid());
    }

    fn get(&self, ordinal: &usize) -> &Node<T> {
        self.list.get(ordinal).expect("node")
    }

    fn get_value(&self, ordinal: &usize) -> Option<&T> {
        self.list.get(ordinal).map(|node| &node.value)
    }

    fn get_value_mut(&mut self, ordinal: &usize) -> Option<&mut T> {
        self.list.get_mut(ordinal).map(|node| &mut node.value)
    }

    fn insert(&mut self, ordinal: usize, node: Node<T>) {
        debug_assert!(self.is_valid());

        debug_assert!(
            !self.list.contains_key(&ordinal),
            "there is already an entry at {}",
            ordinal
        );

        debug_assert!(
            ordinal % 2 == 0,
            "ordinal {} should be divisible by 2",
            ordinal
        );

        debug_assert!(self.is_valid());

        if let Some(prev) = node.prev.as_ref() {
            debug_assert!(prev < &ordinal);
            let prev = self.list.get_mut(prev).expect("prev");
            prev.next = Some(ordinal);
        }

        if let Some(next) = node.next.as_ref() {
            debug_assert!(next > &ordinal);
            let next = self.list.get_mut(next).expect("next");
            next.prev = Some(ordinal);
        }

        if self.list.insert(ordinal, node).is_none() {
            self.tree.insert(ordinal);
        }

        debug_assert!(self.is_valid());
    }

    fn is_empty(&self) -> bool {
        debug_assert_eq!(self.list.is_empty(), self.tree.is_empty());
        self.list.is_empty()
    }

    fn len(&self) -> usize {
        debug_assert_eq!(self.list.len(), self.tree.size());
        self.list.len()
    }

    fn ordinal(&self, cardinal: usize) -> usize {
        self.tree.ordinal(cardinal)
    }

    fn pop_back(&mut self) -> Option<T> {
        let node = if self.is_empty() {
            None
        } else if self.len() == 1 {
            Some(self.remove(0))
        } else {
            let back = self.remove(MAX_LEN);
            let new_back = self.remove(back.prev.expect("prev"));

            if self.is_empty() {
                self.insert(0, new_back);
            } else {
                self.insert(MAX_LEN, new_back);
            }

            debug_assert!(self.list.contains_key(&0));
            Some(back)
        };

        node.map(|node| node.into_value())
    }

    fn pop_front(&mut self) -> Option<T> {
        let node = if self.is_empty() {
            None
        } else if self.len() == 1 {
            Some(self.remove(0))
        } else {
            let front = self.remove(0);
            let new_front = self.remove(front.next.expect("next"));
            self.insert(0, new_front);
            Some(front)
        };

        node.map(|node| node.into_value())
    }

    fn remove(&mut self, ordinal: usize) -> Node<T> {
        debug_assert!(self.is_valid());

        let node = self.list.remove(&ordinal).expect("node");
        self.tree.remove(ordinal);

        if let Some(prev) = node.prev.as_ref() {
            let prev = self.list.get_mut(prev).expect("prev");
            prev.next = node.next;
        }

        if let Some(next) = node.next.as_ref() {
            let next = self.list.get_mut(next).expect("next");
            next.prev = node.prev;
        }

        debug_assert!(self.is_valid());

        node
    }

    fn swap(&mut self, from: usize, to: usize) {
        debug_assert!(self.is_valid());

        match from.cmp(&to) {
            Ordering::Less => {
                let mut ordinal = Some(from);

                // swap the value at this ordinal with the value at the next ordinal,
                // until the target is reached
                while let Some(this) = ordinal {
                    let mut node = self.list.remove(&this).expect("node");
                    ordinal = node.next;

                    if let Some(next_ordinal) = node.next {
                        let mut next_node = self.list.remove(&next_ordinal).expect("next");

                        mem::swap(&mut node.value, &mut next_node.value);

                        self.list.insert(this, node);
                        self.list.insert(next_ordinal, next_node);

                        if next_ordinal == to {
                            break;
                        }
                    } else {
                        self.list.insert(this, node);
                    }
                }
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                let mut ordinal = Some(from);

                // swap the value at this ordinal with the value at the previous ordinal,
                // until the target is reached
                while let Some(this) = ordinal {
                    let mut node = self.list.remove(&this).expect("node");
                    ordinal = node.prev;

                    if let Some(prev_ordinal) = node.prev {
                        let mut prev_node = self.list.remove(&prev_ordinal).expect("prev");

                        mem::swap(&mut node.value, &mut prev_node.value);

                        self.list.insert(this, node);
                        self.list.insert(prev_ordinal, prev_node);

                        if prev_ordinal == to {
                            break;
                        }
                    } else {
                        self.list.insert(this, node);
                    }
                }
            }
        }

        debug_assert!(self.is_valid());
    }

    fn is_valid(&self) -> bool {
        assert_eq!(self.list.len(), self.tree.size());

        if self.list.is_empty() {
            assert!(self.tree.is_empty());
            return true;
        }

        let mut prev = None;
        for cardinal in 0..self.len() {
            let ordinal = self.tree.ordinal(cardinal);

            let node = self.list.get(&ordinal).expect("node");
            assert_eq!(node.prev, prev);
            prev = Some(ordinal);

            if let Some(next) = node.next {
                assert_eq!(self.tree.ordinal(cardinal + 1), next);
            } else {
                assert_eq!(node.next, None);
            }
        }

        true
    }
}

/// An iterator to drain the contents of a [`List`]
pub struct Drain<'a, T> {
    inner: &'a mut Inner<T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.inner.len();
        (size, Some(size))
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_back()
    }
}

/// An iterator to drain the contents of a [`List`] conditionally
pub struct DrainWhile<'a, T, Cond> {
    inner: &'a mut Inner<T>,
    cond: Cond,
}

impl<'a, T, Cond> Iterator for DrainWhile<'a, T, Cond>
where
    Cond: Fn(&T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if (self.cond)(self.inner.get_value(&0)?) {
            self.inner.pop_front()
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

/// An iterator over the contents of a [`List`]
pub struct IntoIter<T> {
    inner: Inner<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.inner.len();
        (size, Some(size))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_back()
    }
}

/// An iterator over the elements of a [`List`]
pub struct Iter<'a, T> {
    inner: &'a HashMap<usize, Node<T>>,
    size: usize,
    next: Option<usize>,
    stop: Option<usize>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let ordinal = self.next?;
        let node = self.inner.get(&ordinal).expect("next");

        self.next = if self.stop == Some(ordinal) {
            None
        } else {
            node.next
        };

        if self.next.is_none() {
            self.stop = None;
        } else {
            self.size -= 1;
        }

        Some(&node.value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let ordinal = self.stop?;
        let node = self.inner.get(&ordinal).expect("next");

        self.size -= 1;

        self.stop = if self.next == Some(ordinal) {
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
#[derive(Clone, GetSize)]
pub struct List<T> {
    inner: Inner<T>,
}

impl<T> List<T> {
    /// Create a new empty [`List`].
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
        }
    }

    /// Create a new empty [`List`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Inner::with_capacity(capacity),
        }
    }
}

impl<T> List<T> {
    /// Borrow the last element in this [`List`], if any.
    pub fn back(&self) -> Option<&T> {
        let ordinal = if self.len() <= 1 { 0 } else { MAX_LEN };
        self.inner.get_value(&ordinal)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let ordinal = if self.len() <= 1 { 0 } else { MAX_LEN };
        self.inner.get_value_mut(&ordinal)
    }

    /// Remove all elements from this [`List`].
    pub fn clear(&mut self) {
        self.inner.clear();
        debug_assert!(self.inner.is_valid());
    }

    /// Drain all elements from this [`List`].
    pub fn drain(&mut self) -> Drain<T> {
        Drain {
            inner: &mut self.inner,
        }
    }

    /// Drain the first elements from this [`List`] which match the given `cond`ition.
    pub fn drain_while<Cond>(&mut self, cond: Cond) -> DrainWhile<T, Cond>
    where
        Cond: Fn(&T) -> bool,
    {
        DrainWhile {
            inner: &mut self.inner,
            cond,
        }
    }

    /// Borrow the first element in this [`List`], if any.
    pub fn front(&self) -> Option<&T> {
        self.inner.get_value(&0)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.inner.get_value_mut(&0)
    }

    /// Borrow the element at the given `index`, if any.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            self.front()
        } else if index == (self.len() - 1) {
            self.back()
        } else if index < self.len() {
            let ordinal = self.ordinal(index);
            self.inner.get_value(&ordinal)
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
            self.inner.get_value_mut(&ordinal)
        } else {
            None
        }
    }

    /// Insert a new `value` at the given `index`.
    pub fn insert(&mut self, index: usize, value: T) {
        match self.len() {
            0 => {
                assert_eq!(
                    index, 0,
                    "cannot insert at index {} in an empty list",
                    index
                );

                self.push_front(value)
            }
            1 => match index {
                0 => self.push_front(value),
                1 => self.push_back(value),
                i => panic!("cannot insert at index {} in a single-item list", i),
            },
            2 => match index {
                0 => self.push_front(value),
                1 => {
                    let node = Node::new(value, Some(0), Some(MAX_LEN));
                    self.inner.insert(MAX_LEN >> 1, node);
                }
                2 => self.push_back(value),
                i => panic!("cannot insert at index {} in a list of length {}", i, 2),
            },
            _ if index == 0 => self.push_front(value),
            len if index == len => self.push_back(value),
            len => {
                assert_bounds!(index, len);
                let ordinal = self.ordinal(index);

                if ordinal < (MAX_LEN >> 1) {
                    let insert_ordinal = self.insert_after(value, ordinal);
                    debug_assert!(insert_ordinal > ordinal);
                    self.inner.swap(insert_ordinal, ordinal);
                } else {
                    let node = self.inner.get(&ordinal);
                    let prev = node.prev.expect("prev");

                    let insert_ordinal = self.insert_before(value, ordinal);
                    debug_assert!(
                        insert_ordinal < ordinal,
                        "unable to insert before {ordinal}: {insert_ordinal}"
                    );

                    if insert_ordinal < prev {
                        self.inner.swap(insert_ordinal, prev)
                    } else {
                        // no-op (in this case the order is already correct)
                    }
                }
            }
        }
    }

    /// Iterate over all elements in this [`List`].
    pub fn iter(&self) -> Iter<T> {
        let (next, stop) = match self.len() {
            0 => (None, None),
            1 => (Some(0), Some(0)),
            _ => (Some(0), Some(MAX_LEN)),
        };

        Iter {
            inner: &self.inner.list,
            size: self.len(),
            next,
            stop,
        }
    }

    /// Iterate over all element in this [`List`] mutably. Does NOT preserve order!
    pub fn iter_mut_unordered(&mut self) -> impl Iterator<Item = &mut T> {
        self.inner.list.values_mut().map(|node| &mut node.value)
    }

    /// Return `true` if this [`List`] is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Return the length of this [`List`].
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Remove and return the last value in this [`List`].
    pub fn pop_back(&mut self) -> Option<T> {
        self.inner.pop_back()
    }

    /// Remove and return the first value in this [`List`].
    pub fn pop_front(&mut self) -> Option<T> {
        self.inner.pop_front()
    }

    /// Append the given `value` to the back of this [`List`].
    pub fn push_back(&mut self, value: T) {
        match self.len() {
            0 => self.push_front(value),
            1 => {
                let node = Node::new(value, Some(0), None);
                self.inner.insert(MAX_LEN, node)
            }
            2 => {
                let new_ordinal = MAX_LEN >> 1;
                let new_node = Node::new(value, Some(0), Some(MAX_LEN));

                self.inner.insert(new_ordinal, new_node);
                self.inner.swap(new_ordinal, MAX_LEN);
            }
            _ => {
                let ordinal = self.insert_before(value, MAX_LEN);
                self.inner.swap(ordinal, MAX_LEN);
            }
        }
    }

    #[inline]
    fn insert_before(&mut self, value: T, before: usize) -> usize {
        // identify the previous node
        let node = self.inner.get(&before);
        let prev_ordinal = node.prev.expect("prev");

        // traverse back to find the lowest-density insertion point
        let (prev, ordinal, next) = {
            let mut ordinal = prev_ordinal;
            let insert_after = loop {
                let node = self.inner.get(&ordinal);

                if let Some(prev) = node.prev {
                    if let Some(next) = node.next {
                        if ordinal - prev < next - ordinal {
                            break node;
                        }
                    }

                    ordinal = prev;
                } else {
                    break node;
                }
            };

            let next = insert_after.next.expect("next");

            (ordinal, ordinal + ((next - ordinal) >> 1), next)
        };

        // then insert the new value
        let node = Node::new(value, Some(prev), Some(next));

        self.inner.insert(ordinal, node);

        ordinal
    }

    /// Append the given `value` to the front of this [`List`].
    pub fn push_front(&mut self, value: T) {
        match self.len() {
            0 => {
                let node = Node::new(value, None, None);
                self.inner.insert(0, node);
            }
            1 => {
                let node = Node::new(value, Some(0), None);
                self.inner.insert(MAX_LEN, node);
                self.inner.swap(0, MAX_LEN);
            }
            2 => {
                let new_ordinal = MAX_LEN >> 1;
                let new_node = Node::new(value, Some(0), Some(MAX_LEN));
                self.inner.insert(new_ordinal, new_node);
                self.inner.swap(new_ordinal, 0);
            }
            _ => {
                let new_ordinal = self.insert_after(value, 0);
                self.inner.swap(new_ordinal, 0);
            }
        }
    }

    #[inline]
    fn insert_after(&mut self, value: T, after: usize) -> usize {
        debug_assert!(self.inner.is_valid());

        // traverse forward to find the lowest-density insertion point
        let mut ordinal = after;
        let mut gap = 0;

        loop {
            let node = self.inner.get(&ordinal);

            if let Some(next) = node.next {
                let next_gap = next - ordinal;

                debug_assert!(next_gap > 2);
                debug_assert_eq!(ordinal + next_gap, next);
                debug_assert!(self.inner.list.contains_key(&(ordinal + next_gap)));

                if next_gap < gap {
                    break;
                } else {
                    gap = next_gap;
                    ordinal = next;
                }
            } else {
                break;
            }
        }

        debug_assert!(gap > 0);
        debug_assert!(self.inner.list.contains_key(&ordinal));
        debug_assert!(self.inner.list.contains_key(&(ordinal - gap)));

        // then insert the new value
        let new_ordinal = ordinal - (gap >> 1);
        let new_node = Node::new(value, Some(ordinal - gap), Some(ordinal));

        self.inner.insert(new_ordinal, new_node);

        new_ordinal
    }

    /// Iterate over the given `range` of elements in this [`List`].
    pub fn range<R: RangeBounds<usize>>(&self, range: R) -> Iter<T> {
        #[inline]
        fn empty<T>(list: &HashMap<usize, Node<T>>) -> Iter<T> {
            Iter {
                inner: list,
                size: 0,
                next: None,
                stop: None,
            }
        }

        if self.is_empty() {
            return empty(&self.inner.list);
        }

        let start = match range.start_bound() {
            Bound::Included(start) => match self.len().cmp(start) {
                Ordering::Less | Ordering::Equal => return empty(&self.inner.list),
                Ordering::Greater => *start,
            },
            Bound::Excluded(start) => match self.len().cmp(start) {
                Ordering::Less | Ordering::Equal => return empty(&self.inner.list),
                Ordering::Greater => {
                    if *start == self.len() - 1 {
                        return empty(&self.inner.list);
                    } else {
                        start + 1
                    }
                }
            },
            _ => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(end) if end < &self.len() => *end,
            Bound::Excluded(end) if end <= &self.len() => *end - 1,
            _ => MAX_LEN,
        };

        Iter {
            inner: &self.inner.list,
            size: (end - start) + 1,
            next: Some(self.ordinal(start)),
            stop: Some(self.ordinal(end)),
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
        let node = self.inner.remove(ordinal);

        Some(node.into_value())
    }

    /// Return `true` if the first elements in this [`List`] are equal to those in the given `iter`.
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

    /// Swap the value at `from` with the value at `to`.
    pub fn swap(&mut self, from: usize, to: usize) {
        assert_bounds!(from, self.len());
        assert_bounds!(to, self.len());

        let from = self.ordinal(from);
        let mut from_node = self.inner.list.remove(&from).expect("from");

        let to = self.ordinal(to);
        let mut to_node = self.inner.list.remove(&to).expect("to");

        mem::swap(&mut from_node.value, &mut to_node.value);

        self.inner.list.insert(from, from_node);
        self.inner.list.insert(to, to_node);

        debug_assert!(self.inner.is_valid());
    }

    fn ordinal(&self, cardinal: usize) -> usize {
        assert_bounds!(cardinal, self.len());

        if cardinal == 0 {
            0
        } else if cardinal == self.len() - 1 {
            if self.len() == 1 {
                0
            } else {
                MAX_LEN
            }
        } else {
            self.inner.ordinal(cardinal)
        }
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().zip(other).all(|(l, r)| *l == *r)
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T: PartialEq> PartialEq<Vec<T>> for List<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().zip(other).all(|(l, r)| l == r)
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
        let mut list = match source.size_hint() {
            (_, Some(max)) => Self::with_capacity(max),
            (min, None) if min > 0 => Self::with_capacity(min),
            _ => Self::new(),
        };

        for item in source {
            list.push_back(item);
        }

        list
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { inner: self.inner }
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[")?;

        let mut iter = self.iter();
        let last = iter.next_back();

        for item in iter {
            write!(f, "{item:?}, ")?;
        }

        if let Some(last) = last {
            write!(f, "{last:?}")?;
        }

        f.write_str("]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_drain_partial() {
        let mut list = List::from_iter(0..10);
        let drained = list.drain().take_while(|i| *i < 5).collect::<Vec<_>>();

        assert_eq!(drained, vec![0, 1, 2, 3, 4]);
        assert_eq!(list, vec![6, 7, 8, 9]);
    }

    #[test]
    fn test_drain_while() {
        let mut list = List::from_iter(0..10);
        let drained = list.drain_while(|i| *i < 5).collect::<Vec<_>>();

        assert_eq!(drained, vec![0, 1, 2, 3, 4]);
        assert_eq!(list, vec![5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_list() {
        let mut rng = rand::thread_rng();

        for i in (0..8).into_iter().map(|i| 2usize.pow(i)) {
            let mut list = List::new();
            let mut vector = Vec::new();

            list.push_front("0".to_string());
            vector.insert(0, "0".to_string());

            let max = Ord::min(i, MAX_LEN);
            for _ in 0..max {
                let r = rng.gen_range(0..list.len());
                list.insert(r, r.to_string());
                vector.insert(r, r.to_string());
                assert_eq!(list.len(), vector.len());
                assert_eq!(
                    list.iter().collect::<Vec<_>>(),
                    vector.iter().collect::<Vec<_>>()
                );
            }

            for _ in 0..(max >> 1) {
                let i = rng.gen_range(0..list.len());
                list.remove(i);
                vector.remove(i);
            }

            for i in 0..vector.len() {
                assert_eq!(vector[i], *list.get(i).expect("item"));
            }
        }
    }

    #[test]
    fn test_ordered_list() {
        let expected = Vec::from_iter(0..100);
        let actual = List::from_iter(0..100);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reversed_list() {
        let expected = Vec::from_iter((0..100).rev());
        let mut actual = List::with_capacity(100);
        for i in 0..100 {
            actual.push_front(i);
        }

        assert_eq!(actual, expected);
    }
}
