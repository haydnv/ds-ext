//! A linked list with cardinal indexing and O(log n) insert/remove anywhere in the [`List`].
//!
//! The API of [`List`] is designed to resemble [`std::collections::VecDeque`] but [`List`] does
//! not use a `VecDeque`; instead each node in the list is assigned an ordinal value
//! in the range `[0, usize::MAX)`, which is also stored in a
//! [`HashMap`](`std::collections::HashMap`) of ordinal values to nodes.
//!
//! This design allows a cardinal index to be resolved to a node in O(log n) time.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::{Index, IndexMut, RangeBounds};
use std::sync::Arc;

struct Node<T> {
    ordinal: usize,
    next: Option<Arc<Value<T>>>,
    prev: Option<Arc<Value<T>>>,
}

impl<T> Node<T> {
    fn new(ordinal: usize) -> Self {
        Self {
            ordinal,
            next: None,
            prev: None,
        }
    }
}

struct Value<T> {
    value: T,
    state: RefCell<Node<T>>,
}

impl<T> Value<T> {
    fn new(ordinal: usize, value: T) -> Self {
        Self {
            value,
            state: RefCell::new(Node::new(ordinal)),
        }
    }
}

/// A draining iterator over the elements of a [`List`]
pub struct Drain<'a, T> {
    #[allow(unused)]
    list: &'a mut List<T>,
    next: Option<Arc<Node<T>>>,
    stop: Option<usize>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An iterator over the elements of a [`List`]
pub struct IntoIter<T> {
    next: Option<Arc<Node<T>>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An iterator over the elements of a [`List`]
pub struct Iter<'a, T> {
    #[allow(unused)]
    list: &'a List<T>,
    next: Option<Arc<Node<T>>>,
    stop: Option<usize>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An iterator over the elements of a [`List`]
pub struct IterMut<'a, T> {
    #[allow(unused)]
    list: &'a mut List<T>,
    next: Option<Arc<Node<T>>>,
    stop: Option<usize>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// A linked list with cardinal indexing and O(log n) insert/remove by index anywhere in the list
pub struct List<T> {
    head: Option<Arc<Node<T>>>,
    tail: Option<Arc<Node<T>>>,
    order: HashMap<usize, Arc<Node<T>>>,
}

impl<T> List<T> {
    /// Create a new empty [`List`].
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            order: HashMap::new(),
        }
    }

    /// Create a new empty [`List`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            head: None,
            tail: None,
            order: HashMap::with_capacity(capacity),
        }
    }

    /// Remove all elements from this [`List`].
    pub fn clear(&mut self) {
        todo!()
    }

    /// Remove and return all elements from thie [`List`].
    pub fn drain(&mut self) -> Drain<T> {
        todo!()
    }

    /// Borrow the element at the given `index`, if any.
    pub fn get(&self, index: usize) -> Option<&T> {
        todo!()
    }

    /// Borrow the element at the given `index` mutably, if any.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        todo!()
    }

    /// Insert a new `value` at the given `index`.
    pub fn insert(&mut self, index: usize, value: T) {
        todo!()
    }

    /// Iterate over all elements in this [`List`].
    pub fn iter(&self) -> Iter<T> {
        todo!()
    }

    /// Iterate mutably over all elements in this [`List`].
    pub fn iter_mut(&self) -> IterMut<T> {
        todo!()
    }

    /// Return `true` if this [`List`] is empty.
    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    /// Return the length of this [`List`].
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Iterate over the given `range` of elements in this [`List`].
    pub fn range<R: RangeBounds<usize>>(&self, range: R) -> IntoIter<T> {
        todo!()
    }

    /// Iterate mutably over the given `range` of elements in this [`List`].
    pub fn range_mut<R: RangeBounds<usize>>(&self, range: R) -> IntoIter<T> {
        todo!()
    }

    /// Remove and return the value at the given `index`, if any.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        todo!()
    }

    /// Remove and return the last value in this [`List`].
    pub fn pop_back(&mut self, value: T) {
        todo!()
    }

    /// Remove and return the first value in this [`List`].
    pub fn pop_front(&mut self, value: T) {
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

    /// Split this list into two at the given index.
    pub fn split_off(&mut self, at: usize) -> (Self, Self) {
        todo!()
    }

    /// Drop all elements after the given index from this [`List`].
    pub fn truncate(&mut self, at: usize) {
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
        let mut list = match source.size_hint() {
            (0, None) => List::new(),
            (min, None) => List::with_capacity(min),
            (_min, Some(max)) => List::with_capacity(max),
        };

        for item in source {
            list.push_back(item);
        }

        list
    }
}

impl<T> Index<usize> for List<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        todo!()
    }
}

impl<T> IndexMut<usize> for List<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        todo!()
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut List<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
