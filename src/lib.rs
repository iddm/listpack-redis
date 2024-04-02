//! The listpack data structure is a compressed list of strings, and
//! numbers.
//!
//! The listpack data structure is used in the Redis database to store
//! lists of strings, and numbers. The listpack data structure is
//! implemented in the C programming language, and this crate provides
//! an idiomatic and safe Rust interface to the listpack data structure.
//!
//! For the description of the listpack data structure, refer to this
//! [document](https://github.com/antirez/listpack/blob/master/listpack.md).
//!
//! # Example
//!
//! ```
//! use listpack_redis::*;
//!
//! let mut listpack: Listpack = Listpack::default();
//! listpack.push("hello");
//! listpack.push("world");
//!
//! let entry = listpack.get(0).unwrap();
//! assert_eq!(entry.to_string(), "hello");
//!
//! let entry = &listpack[1];
//! assert_eq!(entry.to_string(), "world");
//!
//! listpack.replace(1, "rust");
//! let entry = &listpack[1];
//! assert_eq!(entry.to_string(), "rust");
//!
//! listpack.remove(0);
//! let entry = &listpack[0];
//! assert_eq!(entry.to_string(), "rust");
//!
//! listpack.clear();
//! assert_eq!(listpack.len(), 0);
//! assert!(listpack.is_empty());
//! ```
//!
//! The listpack data structure can be used as a replacement for the
//! standard library's `Vec` data structure, however, it cannot produce
//! slices to the underlying data and stores different types within
//! itself, contrary to the `Vec` data structure, which only stores
//! elements of the same type.
//!
//! The listpack data structure, as a result of storing different types
//! within itself, is not as flexible as the `Vec` data structure, for
//! example, it cannot be sorted and it cannot provide with mutable
//! iterators.
#![deny(missing_docs)]

#[allow(warnings)]
#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(unused)]
#[allow(missing_docs)]
/// The raw bindings to the listpack redis implementation.
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

pub mod allocator;
pub mod entry;
pub mod error;
pub mod listpack;
mod redis_helpers;

/// The prelude module contains all the types and traits that you need
/// to use the listpack library.
pub mod prelude {
    pub use crate::entry::*;
    pub use crate::listpack::*;
}

// Re-export the prelude contents.
pub use prelude::*;
