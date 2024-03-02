//! The listpack data structure is a compressed list of strings, and
//! numbers.
#![deny(missing_docs)]

#[allow(warnings)]
#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(unused)]
#[allow(missing_docs)]
/// The raw bindings to the listpack redis implementation.
pub mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

pub mod error;
pub mod listpack;
mod redis_helpers;

/// The prelude module contains all the types and traits that you need
/// to use the listpack library.
pub mod prelude {
    pub use crate::listpack::*;
}

// Re-export the prelude contents.
pub use prelude::*;
