//! A URI which supports IPv4, IPv6, domain names, and segmented [`Path`](`crate::path::Path`)s.

use crate::path::PathBuf;

/// The host component of a [`Link`]
pub enum Host {
    // TODO: IPv4
    // TODO: IPv6
    // TODO: international domain names with IDNA: https://docs.rs/idna/0.3.0/idna/
}

/// An HTTP Link with an optional [`Host`] and [`PathBuf`]
pub struct Link {
    host: Option<Host>,
    path: PathBuf,
}
