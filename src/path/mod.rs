//! A segmented [`Path`] safe to use as a filesystem [`std::path::Path`] or in a URL.
//!
//! This module also provides an HTTP [`Link`](`crate::path::Link`) for use with [`Path`].

use std::ops::{Deref, DerefMut};

pub mod id;
pub mod link;

pub use id::Id;
pub use link::{Host, Link};

/// A segment of a [`Path`]
pub type PathSegment = Id;

/// A segmented path safe to use with a filesystem or via HTTP.
pub struct Path<'a> {
    segments: &'a [PathSegment],
}

impl<'a> Deref for Path<'a> {
    type Target = [PathSegment];

    fn deref(&self) -> &Self::Target {
        &self.segments
    }
}

/// A segmented path buffer safe to use with a filesystem or via HTTP.
pub struct PathBuf {
    segments: Vec<PathSegment>,
}

impl Deref for PathBuf {
    type Target = [PathSegment];

    fn deref(&self) -> &Self::Target {
        &self.segments
    }
}

impl DerefMut for PathBuf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.segments
    }
}
