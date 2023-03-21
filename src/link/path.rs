//! A segmented [`Path`] safe to use as a filesystem [`std::path::Path`] or in a [`super::Link`].

use std::ops::{Deref, DerefMut};
use std::str::FromStr;
use std::{fmt, iter};

use get_size::GetSize;
use get_size_derive::*;

use super::{label, Id, Label, ParseError};

/// A segment of a [`Path`]
pub type PathSegment = Id;

/// A constant representing a [`PathBuf`].
pub struct PathLabel {
    segments: &'static [&'static str],
}

impl<Idx: std::slice::SliceIndex<[&'static str]>> std::ops::Index<Idx> for PathLabel {
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.segments[index]
    }
}

/// Return a [`PathLabel`] with the given segments.
pub const fn path_label(segments: &'static [&'static str]) -> PathLabel {
    PathLabel { segments }
}

impl From<PathLabel> for Id {
    fn from(path: PathLabel) -> Self {
        Label::from(path).into()
    }
}

impl From<PathLabel> for Label {
    fn from(path: PathLabel) -> Self {
        match path.segments {
            [id] => label(id),
            _ => panic!("not an Id: {}", PathBuf::from(path)),
        }
    }
}

impl From<PathLabel> for PathBuf {
    fn from(path: PathLabel) -> Self {
        let segments = path
            .segments
            .into_iter()
            .map(|segment| label(*segment))
            .map(PathSegment::from)
            .collect();

        Self { segments }
    }
}

/// A segmented link safe to use with a filesystem or via HTTP.
pub struct Path<'a> {
    inner: &'a [PathSegment],
}

impl Default for Path<'static> {
    fn default() -> Self {
        Self { inner: &[] }
    }
}

impl<'a> Deref for Path<'a> {
    type Target = [PathSegment];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'a> From<&'a [PathSegment]> for Path<'a> {
    fn from(inner: &'a [PathSegment]) -> Path<'a> {
        Path { inner }
    }
}

impl<'a, Idx: std::slice::SliceIndex<[PathSegment]>> std::ops::Index<Idx> for Path<'a> {
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.inner[index]
    }
}

impl<'a> fmt::Debug for Path<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<'a> fmt::Display for Path<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("/")?;

        for i in 0..self.len() {
            write!(f, "{}", self[i])?;

            if i < self.len() - 1 {
                f.write_str("/")?;
            }
        }

        Ok(())
    }
}

/// A segmented link buffer safe to use with a filesystem or via HTTP.
#[derive(Clone, Default, Hash, Eq, PartialEq, GetSize)]
pub struct PathBuf {
    segments: Vec<PathSegment>,
}

impl PathBuf {
    /// Consumes `self` and returns its underlying vector.
    pub fn into_vec(self) -> Vec<PathSegment> {
        self.segments
    }

    /// Appends `suffix` to this `PathBuf`.
    pub fn append<S: Into<PathSegment>>(mut self, suffix: S) -> Self {
        self.segments.push(suffix.into());
        self
    }

    /// Remove and return the last segment in this path, if any.
    pub fn pop(&mut self) -> Option<PathSegment> {
        self.segments.pop()
    }

    /// If this path begins with the specified prefix, returns the suffix following the prefix.
    pub fn suffix<'a>(&self, path: &'a [PathSegment]) -> Option<&'a [PathSegment]> {
        if path.starts_with(&self.segments) {
            Some(&path[self.segments.len()..])
        } else {
            None
        }
    }
}

impl Extend<PathSegment> for PathBuf {
    fn extend<T: IntoIterator<Item = PathSegment>>(&mut self, iter: T) {
        self.segments.extend(iter)
    }
}

impl<Idx: std::slice::SliceIndex<[PathSegment]>> std::ops::Index<Idx> for PathBuf {
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.segments[index]
    }
}

#[cfg(feature = "hash")]
impl<D: async_hash::Digest> async_hash::Hash<D> for PathBuf {
    fn hash(self) -> async_hash::Output<D> {
        async_hash::Hash::<D>::hash(&self)
    }
}

#[cfg(feature = "hash")]
impl<'a, D: async_hash::Digest> async_hash::Hash<D> for &'a PathBuf {
    fn hash(self) -> async_hash::Output<D> {
        if self == &PathBuf::default() {
            return async_hash::default_hash::<D>();
        } else {
            async_hash::Hash::<D>::hash(self.to_string())
        }
    }
}

impl PartialEq<String> for PathBuf {
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<str> for PathBuf {
    fn eq(&self, other: &str) -> bool {
        if other.is_empty() {
            return false;
        } else if self.segments.is_empty() {
            return other == "/";
        }

        let mut i = 0;
        for segment in other.split('/') {
            if i >= self.segments.len() {
                return false;
            } else if segment == self.segments[i] {
                i += 1;
            } else {
                return false;
            }
        }

        self.segments.len() == i
    }
}

impl IntoIterator for PathBuf {
    type Item = PathSegment;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.segments.into_iter()
    }
}

impl std::borrow::Borrow<[PathSegment]> for PathBuf {
    fn borrow(&self) -> &[PathSegment] {
        &self.segments[..]
    }
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

impl PartialEq<[PathSegment]> for PathBuf {
    fn eq(&self, other: &[PathSegment]) -> bool {
        &self.segments == other
    }
}

impl From<PathSegment> for PathBuf {
    fn from(segment: PathSegment) -> PathBuf {
        PathBuf {
            segments: iter::once(segment).collect(),
        }
    }
}

impl From<Label> for PathBuf {
    fn from(segment: Label) -> PathBuf {
        PathBuf {
            segments: iter::once(segment.into()).collect(),
        }
    }
}

impl FromStr for PathBuf {
    type Err = ParseError;

    #[inline]
    fn from_str(to: &str) -> Result<Self, Self::Err> {
        if to == "/" {
            Ok(PathBuf { segments: vec![] })
        } else if to.ends_with('/') {
            Err(format!("Path {} cannot end with a slash", to).into())
        } else if to.starts_with('/') {
            let segments = to
                .split('/')
                .skip(1)
                .map(PathSegment::from_str)
                .collect::<Result<Vec<PathSegment>, ParseError>>()?;

            Ok(PathBuf { segments })
        } else {
            to.parse()
                .map(|id| PathBuf {
                    segments: iter::once(id).collect(),
                })
                .map_err(|cause| format!("invalid path: {}", cause).into())
        }
    }
}

impl From<Vec<PathSegment>> for PathBuf {
    fn from(segments: Vec<PathSegment>) -> Self {
        Self { segments }
    }
}

impl iter::FromIterator<PathSegment> for PathBuf {
    fn from_iter<T: IntoIterator<Item = PathSegment>>(iter: T) -> Self {
        PathBuf {
            segments: iter.into_iter().collect(),
        }
    }
}

impl fmt::Debug for PathBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Path::from(&self[..]))
    }
}

impl fmt::Display for PathBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Path::from(&self[..]))
    }
}
