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
//! tree.insert(2);
//! assert_eq!(tree.size(), 2);
//!
//! tree.insert(2);
//! assert_eq!(tree.size(), 2);
//!
//! tree.insert(3);
//! tree.remove(3);
//! assert_eq!(tree.size(), 2);
//!
//! tree.insert(3);
//! tree.remove(2);
//! assert_eq!(tree.size(), 2);
//!
//! tree.insert(16);
//! tree.insert(8);
//! tree.insert(24);
//! tree.remove(16);
//! assert_eq!(tree.size(), 4);
//!
//! tree.remove(1);
//! assert_eq!(tree.size(), 3);
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

#[derive(Copy, Clone)]
struct Node {
    left: Option<usize>,
    right: Option<usize>,
}

impl Node {
    fn new() -> Self {
        Self {
            left: None,
            right: None,
        }
    }
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
            self.nodes.insert(ordinal, Node::new());
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
            if root == ordinal {
                self.root = remove_inner(&mut self.nodes, root);
            } else {
                remove(&mut self.nodes, root, ordinal)
            }
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
                children.left = Some(ordinal);
                nodes.insert(ordinal, Node::new());
            }
        }
        Ordering::Equal => {}
        Ordering::Less => {
            if let Some(right) = children.right {
                insert(nodes, right, ordinal)
            } else {
                children.right = Some(ordinal);
                nodes.insert(ordinal, Node::new());
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
    let mut children = *nodes.get(&node).expect("node");

    match node.cmp(&ordinal) {
        Ordering::Greater => {
            if let Some(left) = children.left {
                if left == ordinal {
                    children.left = remove_inner(nodes, left);
                    nodes.insert(node, children);
                } else {
                    remove(nodes, left, ordinal)
                }
            } else {
                // nothing to remove
            }
        }
        Ordering::Less => {
            if let Some(right) = children.right {
                if right == ordinal {
                    children.right = remove_inner(nodes, right);
                    nodes.insert(node, children);
                } else {
                    remove(nodes, right, ordinal)
                }
            } else {
                // nothing to remove
            }
        }
        Ordering::Equal => unreachable!("a tree node cannot delete itself"),
    }
}

#[inline]
fn remove_inner(nodes: &mut HashMap<usize, Node>, node: usize) -> Option<usize> {
    let deleted = nodes.remove(&node).expect("node");

    let new_node = match (deleted.left, deleted.right) {
        (None, None) => None,
        (Some(left), None) => {
            // move the left child up
            Some(left)
        }
        (None, Some(right)) => {
            // move the right child up
            Some(right)
        }
        (Some(_left), Some(right)) => {
            let inorder_successor = remove_min(nodes, right);
            nodes.insert(inorder_successor, deleted);
            Some(inorder_successor)
        }
    };

    new_node
}

#[inline]
fn remove_min(nodes: &mut HashMap<usize, Node>, node: usize) -> usize {
    let mut children = nodes.get_mut(&node).expect("node");
    if let Some(left) = children.left {
        remove_min(nodes, left)
    } else {
        children.left = None;
        node
    }
}
