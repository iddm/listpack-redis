//! The error module contains the error type and result type for the

use std::str::Utf8Error;
/// listpack.

#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// The subencoding of the listpack's entry is unknown.
    UnknownEncodingType {
        /// The encoding byte that caused the error.
        encoding_byte: u8,
    },
    /// Indicates an unsupported number data type. The bit width of the
    /// provided number which caused this error is provided in the
    /// [`bit_width`] field.
    UnsupportedNumberDataTypeBitWidth {
        /// The bit width of the number that caused the error.
        bit_width: u8,
    },
    /// An error indicating that the listpack's entry is missing a data
    /// block.
    MissingDataBlock,
    /// An error indicating that the listpack's entry contains an
    /// invalid string inside the data block.
    InvalidStringEncodingInsideDataBlock(Utf8Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::UnknownEncodingType { encoding_byte } => {
                write!(f, "Unknown encoding byte: {encoding_byte}")
            }
            Error::UnsupportedNumberDataTypeBitWidth { bit_width } => {
                write!(f, "Unsupported number data type bit width: {bit_width}")
            }
            Error::MissingDataBlock => write!(f, "Missing data block"),
            Error::InvalidStringEncodingInsideDataBlock(e) => {
                write!(f, "Invalid string inside data block: {e}")
            }
        }
    }
}

impl std::error::Error for Error {}

/// The result type for the listpack crate.
pub type Result<T = ()> = std::result::Result<T, Error>;
