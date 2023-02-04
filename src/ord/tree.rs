//! A binary search tree of ordinal values
//!
//! Example usage:
//! ```
//! use ds_ext::ord::Tree;
//!
//! let mut tree = Tree::new(32);
//! tree.insert(1);
//! assert_eq!(tree.size(), 1);
//! 
//! ```

use std::cmp::Ordering;
use std::collections::HashMap;

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

struct Node {
    left: Option<usize>,
    right: Option<usize>,
}

/// A binary tree of ordinal values
pub struct Tree {
    nodes: HashMap<usize, Node>,
    root: Option<usize>,
    max_size: usize,
}

impl Tree {
    /// Construct a new [`Tree`].
    pub fn new(max_size: usize) -> Self {
        Self {
            nodes: HashMap::new(),
            root: None,
            max_size,
        }
    }

    /// Check the maximum allowed size of this [`Tree`].
    pub fn max_size(&self) -> usize {
        self.max_size
    }

    /// Check the size of this [`Tree`].
    pub fn size(&self) -> usize {
        self.nodes.len()
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
                left: None,
                right: None,
            };

            self.nodes.insert(ordinal, root);
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
fn insert(nodes: &mut HashMap<usize, Node>, node: usize, ordinal: usize) {
    let children = nodes.get_mut(&node).expect("node");

    match node.cmp(&ordinal) {
        Ordering::Greater => {
            if let Some(left) = children.left {
                insert(nodes, left, ordinal)
            } else {
                children.left = Some(ordinal)
            }
        }
        Ordering::Equal => {}
        Ordering::Less => {
            if let Some(right) = children.right {
                insert(nodes, right, ordinal)
            } else {
                children.right = Some(ordinal)
            }
        }
    }
}

#[inline]
fn median(nodes: &HashMap<usize, Node>, node: usize) -> usize {
    todo!()
}

#[inline]
fn remove(nodes: &mut HashMap<usize, Node>, node: usize, ordinal: usize) {
    todo!()
}
