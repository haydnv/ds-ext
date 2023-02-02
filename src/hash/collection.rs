//! A [`Collection`] with no trait boundaries, i.e. a [`HashMap`] which generates its own keys.

use uuid::Uuid;

use super::map::HashMap;

/// A generic collection with no trait boundaries, i.e. a [`HashMap`] which generates its own keys.
pub struct Collection<T> {
    inner: HashMap<Uuid, T>,
}
