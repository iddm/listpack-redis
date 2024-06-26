//! The bloom filter facilities.

/// A trait for the bloom filters.
pub trait BloomFilter {
    /// Inserts a value into the bloom filter.
    fn insert(&mut self, key: &[u8]);

    /// Returns true if the value is in the bloom filter.
    fn contains(&self, key: &[u8]) -> bool;
}

impl BloomFilter for () {
    fn insert(&mut self, _key: &[u8]) {}

    fn contains(&self, _key: &[u8]) -> bool {
        false
    }
}

/// The provided bloom filter implementation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct FastBloomFilter(fastbloom::BloomFilter);

impl BloomFilter for FastBloomFilter {
    fn insert(&mut self, key: &[u8]) {
        self.0.insert(key);
    }

    fn contains(&self, key: &[u8]) -> bool {
        self.0.contains(key)
    }
}
