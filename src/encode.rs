//! This module provides the `Encode` trait for encoding objects into
//! byte arrays. This is useful particularly for encoding objects into
//! byte arrays for storage in the listpack data structure.

/// The encoded presentation of the object as a byte array.
pub trait Encode {
    /// Return a byte representation of the object.
    fn encode(&self) -> Result<Vec<u8>>;
}
