//! The error module contains the error type and result type for the

use std::str::Utf8Error;

/// An error happening during the insertion into listpack.
#[derive(Debug, Copy, Clone)]
pub enum InsertionError {
    /// An empty string is provided to be inserted into the listpack.
    StringIsEmpty,
    /// The object which is too long to be inserted into the listpack.
    ListpackIsFull {
        /// The current byte length of the object causing the error
        /// during the insertion.
        current_length: usize,
        /// The available amount of bytes available in the listpack.
        available_listpack_length: usize,
    },
}

impl std::fmt::Display for InsertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            InsertionError::StringIsEmpty => write!(f, "Provided string is empty."),
            InsertionError::ListpackIsFull {
                current_length,
                available_listpack_length,
            } => write!(
                f,
                "Object is too long: {current_length} > {available_listpack_length}"
            ),
        }
    }
}

impl std::error::Error for InsertionError {}

/// The error type for the listpack crate.
#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// The subencoding of the listpack's entry is unknown.
    UnknownEncodingType {
        /// The encoding byte that caused the error.
        encoding_byte: u8,
    },
    /// Indicates an unsupported number data type. The bit width of the
    /// provided number which caused this error is provided in the
    /// [`Self::UnsupportedNumberDataTypeBitWidth::bit_width`] field.
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
    /// An error related to the insertion into the listpack.
    Insertion(InsertionError),
}

impl From<InsertionError> for Error {
    fn from(e: InsertionError) -> Self {
        Error::Insertion(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::UnknownEncodingType { encoding_byte } => {
                write!(f, "Unknown encoding byte: {encoding_byte:b}")
            }
            Error::UnsupportedNumberDataTypeBitWidth { bit_width } => {
                write!(f, "Unsupported number data type bit width: {bit_width}")
            }
            Error::MissingDataBlock => write!(f, "Missing data block"),
            Error::InvalidStringEncodingInsideDataBlock(e) => {
                write!(f, "Invalid string inside data block: {e}")
            }
            Error::Insertion(e) => write!(f, "Insertion error: {e}"),
        }
    }
}

impl std::error::Error for Error {}

/// The result type for the listpack crate.
pub type Result<T = ()> = std::result::Result<T, Error>;
