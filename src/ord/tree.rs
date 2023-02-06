//! A binary search tree which maps cardinal values to ordinal values
//!
//! Example usage:
//! ```
//! use ds_ext::ord::Tree;
//!
//! let mut tree = Tree::new();
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
//!
//! assert_eq!(tree.size(), 4);
//!
//! tree.remove(1);
//! assert_eq!(tree.size(), 3);
//! ```

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

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

#[derive(Copy, Clone, Debug)]
struct Node {
    size: usize,
    left: Option<usize>,
    right: Option<usize>,
}

impl Node {
    fn new() -> Self {
        Self {
            size: 1,
            left: None,
            right: None,
        }
    }
}

type Nodes = HashMap<usize, Node>;

/// A binary search tree which maps cardinal values to ordinal values
#[derive(Clone)]
pub struct Tree {
    nodes: Nodes,
    root: Option<usize>,
}

impl Tree {
    /// Construct a new [`Tree`].
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            root: None,
        }
    }

    /// Construct a new [`Tree`] with the given `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            nodes: HashMap::with_capacity(capacity),
            root: None,
        }
    }

    /// Remove all nodes from this [`Tree`].
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.root = None;
    }

    /// Return `true` if this [`Tree`] has zero nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
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
        debug_assert!(self.is_valid());

        let new = if let Some(root) = self.root {
            insert(&mut self.nodes, root, ordinal)
        } else {
            self.nodes.insert(ordinal, Node::new());
            self.root = Some(ordinal);
            true
        };

        debug_assert!(self.is_valid());

        new
    }

    /// Find the ordinal of the given `cardinal`.
    ///
    /// Panics:
    ///  - `if cardinal >= self.size()`
    pub fn ordinal(&self, cardinal: usize) -> usize {
        assert_bounds!(cardinal, self.nodes.len());
        debug_assert!(self.is_valid());
        search(&self.nodes, self.root.as_ref().expect("root"), cardinal)
    }

    /// Remove the given `ordinal` from this [`Tree`] and return `true` if it was present.
    ///
    /// Panics:
    ///  - `if ordinal >= self.max_size()`
    pub fn remove(&mut self, ordinal: usize) -> bool {
        debug_assert!(self.is_valid());

        if let Some(root) = self.root {
            if root == ordinal {
                self.root = remove_inner(&mut self.nodes, root);

                debug_assert!(self.is_valid());

                true
            } else {
                let removed = remove(&mut self.nodes, root, ordinal);
                debug_assert!(self.is_valid());
                removed
            }
        } else {
            false
        }
    }

    fn is_valid(&self) -> bool {
        if let Some(root) = self.root.as_ref() {
            assert_eq!(self.nodes.get(root).expect("root").size, self.size());
            is_valid(&self.nodes, root)
        } else {
            assert!(self.is_empty());
            true
        }
    }
}

impl fmt::Debug for Tree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("[")?;

        if let Some(root) = self.root.as_ref() {
            fmt_node(&self.nodes, root, f)?;
        }

        f.write_str("]")
    }
}

fn fmt_node(nodes: &Nodes, ordinal: &usize, f: &mut fmt::Formatter) -> fmt::Result {
    let node = nodes.get(ordinal).expect("node");

    if let Some(left) = node.left.as_ref() {
        fmt_node(nodes, left, f)?;
        f.write_str(" ")?;
    }

    write!(f, "{}", ordinal)?;

    if let Some(right) = node.right.as_ref() {
        f.write_str(" ")?;
        fmt_node(nodes, right, f)?;
    }

    Ok(())
}

fn is_valid(nodes: &Nodes, ordinal: &usize) -> bool {
    fn count(nodes: &Nodes, ordinal: Option<&usize>) -> usize {
        if let Some(ordinal) = ordinal {
            let node = nodes.get(ordinal).expect("node");
            let size = count(nodes, node.left.as_ref()) + count(nodes, node.right.as_ref()) + 1;
            assert_eq!(
                node.size, size,
                "node {}: {:?} should have a size of {}",
                ordinal, node, size
            );
            size
        } else {
            0
        }
    }

    let expected = nodes.get(ordinal).expect("node").size;
    let actual = count(&nodes, Some(ordinal));

    assert_eq!(
        expected, actual,
        "node {} should have a size of {}, not {}",
        ordinal, expected, actual
    );

    true
}

#[inline]
fn search(nodes: &Nodes, ordinal: &usize, cardinal: usize) -> usize {
    let node = nodes.get(ordinal).expect("node");

    debug_assert!(
        cardinal < node.size,
        "node of size {} cannot contain cardinal {}",
        node.size,
        cardinal
    );

    match (node.left.as_ref(), node.right.as_ref()) {
        (None, None) => match cardinal {
            0 => *ordinal,
            _ => unreachable!(),
        },
        (Some(left), None) => {
            if cardinal == node.size - 1 {
                *ordinal
            } else {
                search(nodes, left, cardinal)
            }
        }
        (None, Some(right)) => {
            if cardinal == 0 {
                *ordinal
            } else {
                search(nodes, right, cardinal - 1)
            }
        }
        (Some(left_ordinal), Some(right_ordinal)) => {
            let left = nodes.get(left_ordinal).expect("left");
            if cardinal < left.size {
                search(nodes, left_ordinal, cardinal)
            } else if cardinal == left.size {
                *ordinal
            } else {
                search(nodes, right_ordinal, cardinal - (left.size + 1))
            }
        }
    }
}

#[inline]
fn insert(nodes: &mut Nodes, ordinal: usize, target: usize) -> bool {
    let mut node = *nodes.get(&ordinal).expect("node");

    let new = match ordinal.cmp(&target) {
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
    };

    if new {
        node.size += 1;
        nodes.insert(ordinal, node);
    }

    new
}

#[inline]
fn remove(nodes: &mut Nodes, ordinal: usize, target: usize) -> bool {
    let mut node = *nodes.get(&ordinal).expect("node");

    let removed = match ordinal.cmp(&target) {
        Ordering::Greater => {
            if let Some(left) = node.left {
                if left == target {
                    node.left = remove_inner(nodes, left);
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
                    true
                } else {
                    remove(nodes, right, target)
                }
            } else {
                false
            }
        }
        Ordering::Equal => unreachable!("a node cannot delete itself"),
    };

    if removed {
        node.size -= 1;
        nodes.insert(ordinal, node);
    }

    removed
}

#[inline]
fn remove_inner(nodes: &mut Nodes, node: usize) -> Option<usize> {
    debug_assert!(is_valid(nodes, &node));

    let mut deleted = nodes.remove(&node).expect("node");

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
            let inorder_successor = min(nodes, &right);

            if inorder_successor == right {
                deleted.right = remove_inner(nodes, right);
            } else {
                assert!(remove(nodes, right, inorder_successor));
                debug_assert!(is_valid(nodes, &right));
            }

            deleted.size -= 1;
            nodes.insert(inorder_successor, deleted);

            debug_assert!(is_valid(nodes, &inorder_successor));

            Some(inorder_successor)
        }
    };

    new_node
}

#[inline]
fn min(nodes: &Nodes, ordinal: &usize) -> usize {
    let node = nodes.get(&ordinal).expect("node");
    if let Some(left) = node.left.as_ref() {
        min(nodes, left)
    } else {
        *ordinal
    }
}

mod tests {
    #[test]
    fn test_tree() {
        use super::*;
        use rand::Rng;
        use std::collections::BTreeSet;

        let mut rng = rand::thread_rng();

        for size in 0..100 {
            let mut order = BTreeSet::new();
            let mut tree = Tree::new();

            for _ in 0..size {
                let ord = rng.gen();
                order.insert(ord);
                tree.insert(ord);
            }

            for _ in 0..(size >> 1) {
                let ord = tree.ordinal(rng.gen_range(0..tree.size()));

                order.remove(&ord);
                tree.remove(ord);

                assert_eq!(order.len(), tree.size());
            }

            let mut i = 0;
            for ord in order {
                assert_eq!(ord, tree.ordinal(i));
                i += 1;
            }
        }
    }
}
