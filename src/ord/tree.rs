//! A binary search tree which maps cardinal values to ordinal values
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

type Nodes = HashMap<usize, Node>;

/// A binary search tree which maps cardinal values to ordinal values
pub struct Tree {
    nodes: Nodes,
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

    /// Check the cardinal size of this [`Tree`].
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    /// Insert an `ordinal` into this [`Tree`] and return `false` if it was already present.
    ///
    /// Panics:
    ///  - `if ordinal >= self.max_size()`
    pub fn insert(&mut self, ordinal: usize) -> bool {
        assert_bounds!(ordinal, self.max_size);

        if let Some(root) = self.root {
            insert(&mut self.nodes, root, ordinal)
        } else {
            self.nodes.insert(ordinal, Node::new());
            self.root = Some(ordinal);
            true
        }
    }

    /// Find the ordinal of the given `cardinal`.
    ///
    /// Panics:
    ///  - `if cardinal >= self.size()`
    pub fn ordinal(&self, cardinal: usize) -> usize {
        assert!(
            cardinal < self.size(),
            "cardinal {} is out of bounds for ordinal tree with size {}",
            cardinal,
            self.size()
        );

        todo!()
    }

    /// Remove the given `ordinal` from this [`Tree`] and return `true` if it was present.
    ///
    /// Panics:
    ///  - `if ordinal >= self.max_size()`
    pub fn remove(&mut self, ordinal: usize) -> bool {
        assert_bounds!(ordinal, self.max_size);

        if let Some(root) = self.root {
            if root == ordinal {
                self.root = remove_inner(&mut self.nodes, root);
                true
            } else {
                remove(&mut self.nodes, root, ordinal)
            }
        } else {
            false
        }
    }
}

#[inline]
fn insert(nodes: &mut Nodes, ordinal: usize, target: usize) -> bool {
    let node = nodes.get_mut(&ordinal).expect("node");

    match ordinal.cmp(&target) {
        Ordering::Greater => {
            if let Some(left) = node.left {
                insert(nodes, left, target)
            } else {
                node.left = Some(target);
                nodes.insert(target, Node::new());
                true
            }
        }
        Ordering::Equal => false,
        Ordering::Less => {
            if let Some(right) = node.right {
                insert(nodes, right, target)
            } else {
                node.right = Some(target);
                nodes.insert(target, Node::new());
                true
            }
        }
    }
}

#[inline]
fn remove(nodes: &mut Nodes, ordinal: usize, target: usize) -> bool {
    let mut node = *nodes.get(&ordinal).expect("node");

    match ordinal.cmp(&target) {
        Ordering::Greater => {
            if let Some(left) = node.left {
                if left == target {
                    node.left = remove_inner(nodes, left);
                    nodes.insert(ordinal, node);
                    true
                } else {
                    remove(nodes, left, target)
                }
            } else {
                false
            }
        }
        Ordering::Less => {
            if let Some(right) = node.right {
                if right == target {
                    node.right = remove_inner(nodes, right);
                    nodes.insert(ordinal, node);
                    true
                } else {
                    remove(nodes, right, target)
                }
            } else {
                false
            }
        }
        Ordering::Equal => unreachable!("a node cannot delete itself"),
    }
}

#[inline]
fn remove_inner(nodes: &mut Nodes, node: usize) -> Option<usize> {
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
fn remove_min(nodes: &mut Nodes, ordinal: usize) -> usize {
    let mut node = nodes.get_mut(&ordinal).expect("node");
    if let Some(left) = node.left {
        remove_min(nodes, left)
    } else {
        node.left = None;
        ordinal
    }
}
