//! A binary search tree of ordinal values

use std::collections::HashSet;
use std::hash::{Hash, Hasher};

macro_rules! assert_bounds {
    ($i:expr, $max:expr) => {
        assert!(
            $i < $max,
            "ordinal {} is out of bounds for tree with max size {}",
            $i,
            $max
        );
    };
}

#[derive(Eq)]
struct Node {
    value: usize,
    left: Option<usize>,
    right: Option<usize>,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Hash for Node {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

/// A binary tree of ordinal values
pub struct Tree {
    nodes: HashSet<Node>,
    root: Option<usize>,
    max_size: usize,
}

impl Tree {
    /// Construct a new [`Tree`].
    pub fn new(max_size: usize) -> Self {
        Self {
            nodes: HashSet::new(),
            root: None,
            max_size,
        }
    }

    /// Check the maximum allowed size of this [`Tree`].
    pub fn max_size(&self) -> usize {
        self.max_size
    }

    /// Insert a new `ordinal` into this [`Tree`].
    ///
    /// Panics:
    ///  - `if ordinal >= self.max_size()`
    pub fn insert(&mut self, ordinal: usize) {
        assert_bounds!(ordinal, self.max_size);

        if let Some(root) = self.root {
            insert(&mut self.nodes, root, ordinal);
        } else {
            let root = Node {
                value: ordinal,
                left: None,
                right: None,
            };

            self.nodes.insert(root);
            self.root = Some(ordinal);
        }
    }

    /// Find the median ordinal between `lo` and `hi`.
    ///
    /// Panics:
    ///  - `if lo > hi`
    ///  - `if lo >= self.max_size()`
    ///  - `if hi >= self.max_size()`
    pub fn median(&self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi, "invalid range: [{}, {})", lo, hi);
        assert_bounds!(lo, self.max_size);
        assert_bounds!(hi, self.max_size);

        if let Some(root) = self.root {
            median(&self.nodes, root)
        } else {
            self.max_size >> 1
        }
    }

    /// Remove the given `ordinal` from this [`Tree`].
    ///
    /// Panics:
    ///  - `if ordinal >= self.max_size()`
    pub fn remove(&mut self, ordinal: usize) {
        assert_bounds!(ordinal, self.max_size);

        if let Some(root) = self.root {
            remove(&mut self.nodes, root, ordinal)
        }
    }
}

#[inline]
fn insert(nodes: &mut HashSet<Node>, node: usize, ordinal: usize) {
    todo!()
}

#[inline]
fn median(nodes: &HashSet<Node>, node: usize) -> usize {
    todo!()
}

#[inline]
fn remove(nodes: &mut HashSet<Node>, node: usize, ordinal: usize) {
    todo!()
}
