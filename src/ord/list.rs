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
//! use ds_ext::ord::List;
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

use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::mem;
use std::ops::{Bound, DerefMut, RangeBounds};

use super::tree::Tree;

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

#[derive(Clone, Debug)]
struct Node<T> {
    value: RefCell<T>,
    prev: Option<usize>,
    next: Option<usize>,
}

#[derive(Clone, Debug)]
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
    }

    fn get(&self, ordinal: &usize) -> &Node<T> {
        self.list.get(ordinal).expect("node")
    }

    // TODO: delete
    fn get_mut(&mut self, ordinal: &usize) -> &mut Node<T> {
        self.list.get_mut(ordinal).expect("node")
    }

    fn get_value(&self, ordinal: &usize) -> Option<Ref<T>> {
        self.list.get(ordinal).map(|node| node.value.borrow())
    }

    fn get_value_mut(&mut self, ordinal: &usize) -> Option<RefMut<T>> {
        self.list.get(ordinal).map(|node| node.value.borrow_mut())
    }

    fn insert(&mut self, ordinal: usize, node: Node<T>) {
        debug_assert!(self.is_valid());

        if let Some(prev) = node.prev.as_ref() {
            let prev = self.list.get_mut(prev).expect("prev");
            prev.next = Some(ordinal);
        }

        if let Some(next) = node.next.as_ref() {
            let next = self.list.get_mut(next).expect("next");
            next.prev = Some(ordinal);
        }

        if self.list.insert(ordinal, node).is_none() {
            self.tree.insert(ordinal);
        }

        debug_assert!(self.is_valid());
    }

    // TODO: delete
    fn insert_unchecked(&mut self, ordinal: usize, node: Node<T>) {
        if self.list.insert(ordinal, node).is_none() {
            self.tree.insert(ordinal);
        }
    }

    fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn len(&self) -> usize {
        self.list.len()
    }

    fn ordinal(&self, cardinal: usize) -> usize {
        self.tree.ordinal(cardinal)
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

    fn swap(&self, from: &usize, to: &usize) {
        debug_assert!(self.is_valid());

        match from.cmp(to) {
            Ordering::Less => {
                let mut node = self.get(from);
                while let Some(next) = node.next.as_ref() {
                    let next_node = self.get(next);

                    mem::swap(
                        node.value.borrow_mut().deref_mut(),
                        next_node.value.borrow_mut().deref_mut(),
                    );

                    if next == to {
                        break;
                    } else {
                        node = next_node;
                    }
                }
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                let mut node = self.get(from);
                while let Some(prev) = node.prev.as_ref() {
                    let prev_node = self.get(prev);

                    mem::swap(
                        node.value.borrow_mut().deref_mut(),
                        prev_node.value.borrow_mut().deref_mut(),
                    );

                    if prev == to {
                        break;
                    } else {
                        node = prev_node;
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

/// An iterator over the elements of a [`List`]
pub struct IntoIter<T> {
    inner: HashMap<usize, Node<T>>,
    size: usize,
    next: Option<usize>,
    last: Option<usize>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let ordinal = self.next?;
        let node = self.inner.remove(&ordinal).expect("node");

        self.size -= 1;

        self.next = if self.last == Some(ordinal) {
            None
        } else {
            node.next
        };

        if self.next.is_none() {
            self.last = None;
        }

        Some(node.value.into_inner())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let ordinal = self.last?;
        let node = self.inner.remove(&ordinal).expect("node");

        self.size -= 1;

        self.last = if self.next == Some(ordinal) {
            None
        } else {
            node.prev
        };

        if self.last.is_none() {
            self.next = None;
        }

        Some(node.value.into_inner())
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
    type Item = Ref<'a, T>;

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

        Some(node.value.borrow())
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

        Some(node.value.borrow())
    }
}

/// A linked list with cardinal indexing and O(log n) get/insert/remove by index
#[derive(Clone, Debug)]
pub struct List<T> {
    inner: Inner<T>,
}

impl<T> List<T> {
    const MAX_LEN: usize = usize::MAX;

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

    /// Borrow the last element in this [`List`], if any.
    pub fn back(&self) -> Option<Ref<T>> {
        let ordinal = if self.len() <= 1 { 0 } else { Self::MAX_LEN };
        self.inner.get_value(&ordinal)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn back_mut(&mut self) -> Option<RefMut<T>> {
        let ordinal = if self.len() <= 1 { 0 } else { Self::MAX_LEN };
        self.inner.get_value_mut(&ordinal)
    }

    /// Remove all elements from this [`List`].
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Borrow the first element in this [`List`], if any.
    pub fn front(&self) -> Option<Ref<T>> {
        self.inner.get_value(&0)
    }

    /// Borrow the last element in this [`List`], if any.
    pub fn front_mut(&mut self) -> Option<RefMut<T>> {
        self.inner.get_value_mut(&0)
    }

    /// Borrow the element at the given `index`, if any.
    pub fn get(&self, index: usize) -> Option<Ref<T>> {
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
    pub fn get_mut(&mut self, index: usize) -> Option<RefMut<T>> {
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
        match index {
            0 => self.push_front(value),
            i if self.is_empty() => assert_bounds!(i, self.len()),
            i => match self.len().cmp(&i) {
                Ordering::Less => assert_bounds!(i, self.len()),
                Ordering::Equal => self.push_back(value),
                Ordering::Greater => {
                    // TODO: create the new node on whichever side of this node has more room
                    // then swap the values if needed

                    let next_ordinal = self.ordinal(i);
                    let next = self.inner.get(&next_ordinal);
                    let prev_ordinal = next.prev.expect("prev");
                    let ordinal = prev_ordinal + ((next_ordinal - prev_ordinal) >> 1);

                    let node = Node {
                        value: RefCell::new(value),
                        prev: Some(prev_ordinal),
                        next: Some(next_ordinal),
                    };

                    self.inner.insert(ordinal, node);
                }
            },
        }
    }

    /// Iterate over all elements in this [`List`].
    pub fn iter(&self) -> Iter<T> {
        let next = if self.is_empty() { None } else { Some(0) };

        Iter {
            inner: &self.inner.list,
            size: self.len(),
            next,
            stop: None,
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
                Ordering::Greater => Some(*start),
            },
            Bound::Excluded(start) => match self.len().cmp(start) {
                Ordering::Less | Ordering::Equal => return empty(&self.inner.list),
                Ordering::Greater => {
                    if *start == self.len() - 1 {
                        return empty(&self.inner.list);
                    } else {
                        Some(start + 1)
                    }
                }
            },
            _ => None,
        };

        let end = match range.end_bound() {
            Bound::Included(end) if end < &self.len() => Some(*end),
            Bound::Excluded(end) if end <= &self.len() => Some(*end - 1),
            _ => None,
        };

        let size = match (start, end) {
            (Some(start), Some(end)) => (end - start) + 1,
            (None, Some(end)) => end + 1,
            (Some(start), None) => self.len() - start,
            (None, None) => self.len(),
        };

        let next = start.map(|i| self.ordinal(i));
        let stop = end.map(|i| self.ordinal(i));

        Iter {
            inner: &self.inner.list,
            size,
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
        let node = self.inner.remove(ordinal);

        Some(node.value.into_inner())
    }

    /// Remove and return the last value in this [`List`].
    pub fn pop_back(&mut self) -> Option<T> {
        let node = if self.is_empty() {
            None
        } else if self.len() == 1 {
            Some(self.inner.remove(0))
        } else {
            let back = self.inner.remove(Self::MAX_LEN);
            let new_back = self.inner.remove(back.prev.expect("prev"));
            self.inner.insert(Self::MAX_LEN, new_back);
            Some(back)
        };

        node.map(|node| node.value.into_inner())
    }

    /// Remove and return the first value in this [`List`].
    pub fn pop_front(&mut self) -> Option<T> {
        let node = if self.is_empty() {
            None
        } else if self.len() == 1 {
            Some(self.inner.remove(0))
        } else {
            let front = self.inner.remove(0);
            let new_front = self.inner.remove(front.next.expect("next"));
            self.inner.insert(0, new_front);
            Some(front)
        };

        node.map(|node| node.value.into_inner())
    }

    /// Append the given `value` to the back of this [`List`].
    pub fn push_back(&mut self, value: T) {
        match self.len() {
            0 => self.push_front(value),
            1 => {
                let node = Node {
                    value: RefCell::new(value),
                    prev: Some(0),
                    next: None,
                };

                self.inner.insert(Self::MAX_LEN, node)
            }
            _ => {
                // traverse back to find the lowest-density insertion point
                let mut ordinal = Self::MAX_LEN;
                let mut gap = 0;

                loop {
                    let node = self.inner.get(&ordinal);

                    if let Some(prev) = node.prev {
                        let prev_gap = ordinal - prev;
                        debug_assert!(prev_gap > 2);

                        if prev_gap <= gap {
                            break;
                        } else {
                            gap = prev_gap;
                            ordinal = prev;
                        }
                    } else {
                        break;
                    }
                }

                debug_assert!(gap > 0);
                debug_assert!(ordinal > gap);

                // then insert the new value
                let new_ordinal = ordinal - (gap >> 1);
                let new_node = Node {
                    value: RefCell::new(value),
                    prev: Some(ordinal - gap),
                    next: Some(ordinal),
                };

                self.inner.insert(new_ordinal, new_node);

                // and swap it forward
                self.inner.swap(&new_ordinal, &Self::MAX_LEN);
            }
        }
    }

    /// Append the given `value` to the front of this [`List`].
    pub fn push_front(&mut self, value: T) {
        match self.len() {
            0 => {
                let node = Node {
                    value: RefCell::new(value),
                    prev: None,
                    next: None,
                };

                self.inner.insert(0, node);
            }
            1 => {
                let mut back = self.inner.remove(0);
                debug_assert!(back.next.is_none());
                back.prev = Some(0);

                let front = Node {
                    value: RefCell::new(value),
                    prev: None,
                    next: Some(Self::MAX_LEN),
                };

                self.inner.insert_unchecked(0, front);
                self.inner.insert_unchecked(Self::MAX_LEN, back);
                debug_assert!(self.inner.is_valid());
            }
            _ => {
                // TODO: traverse forward to insert the new value at the largest empty range
                // then traverse backward swapping the values

                let mut node = self.inner.remove(0);
                assert_eq!(node.prev, None);
                node.prev = Some(0);

                let next_ordinal = node.next.expect("next");
                let ordinal = next_ordinal >> 1;

                let front = Node {
                    value: RefCell::new(value),
                    prev: None,
                    next: Some(ordinal),
                };

                self.inner.insert_unchecked(0, front);
                self.inner.insert_unchecked(ordinal, node);

                let next = self.inner.get_mut(&next_ordinal);
                next.prev = Some(ordinal);

                debug_assert!(self.inner.is_valid());
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
            self.inner.ordinal(cardinal)
        }
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().zip(other.iter()).all(|(l, r)| *l == *r)
    }
}

impl<T: Eq> Eq for List<T> {}

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
        let next = if self.is_empty() { None } else { Some(0) };
        let size = self.len();
        let last = if self.len() == 1 {
            Some(0)
        } else {
            Some(Self::MAX_LEN)
        };

        IntoIter {
            inner: self.inner.list,
            size,
            next,
            last,
        }
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = Ref<'a, T>;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

mod tests {
    #[test]
    fn test_list() {
        use super::*;
        use rand::Rng;

        let mut rng = rand::thread_rng();

        for i in 0..64 {
            let mut list = List::new();
            let mut vector = Vec::new();

            list.push_front("0".to_string());
            vector.insert(0, "0".to_string());

            let max = Ord::min(i, List::<String>::MAX_LEN);
            for _ in 0..max {
                let r = rng.gen_range(0..list.len());
                list.insert(r, r.to_string());
                vector.insert(r, r.to_string());
            }

            for _ in 0..(max >> 1) {
                let i = rng.gen_range(0..list.len());
                list.remove(i);
                vector.remove(i);
            }

            assert_eq!(list.len(), vector.len());
            for i in 0..vector.len() {
                assert_eq!(vector[i], *list.get(i).expect("item"));
            }
        }
    }
}
