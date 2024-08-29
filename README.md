# ds-ext

[![Crates.io][crates-badge]][crates-url]
[![Docs.rs][docs-badge]][docs-url]

[crates-badge]: https://img.shields.io/crates/v/ds-ext.svg
[crates-url]: https://crates.io/crates/ds-ext
[docs-badge]: https://docs.rs/ds-ext/badge.svg
[docs-url]: https://docs.rs/ds-ext/

Extensions to standard Rust data structures which provide additional capabilities

Example usage:
```rust
use ds_ext::*;

let mut set = OrdHashSet::new();
set.insert(1);
assert!(set.contains(&1));

let mut map = OrdHashMap::from_iter(set.into_iter().map(|i| (i, i)));
assert_eq!(map.get(&1), map.bisect(|i| i.partial_cmp(&1)));
```
