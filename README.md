[![CI](https://github.com/iddm/listpack-redis/actions/workflows/ci.yml/badge.svg)](https://github.com/iddm/listpack-redis/actions/workflows/ci.yml)
[![Crates](https://img.shields.io/crates/v/listpack-redis.svg)](https://crates.io/crates/listpack-redis)
[![Docs](https://docs.rs/listpack-redis/badge.svg)](https://docs.rs/listpack-redis)
[![License](https://img.shields.io/badge/license-RSALv2_or_SSPLv1-blue?style=flat&logo=license)](./LICENSE)

# Listpack (based on the Redis implementation)

This crate provides a Rust-idiomatic re-implementation of the "listpack"
data-structure implemented in Redis as a part of Redis.

This implementation is:

1. fully written in Rust.
2. Allows to specify a custom allocator.
3. Allows to store more types than in Redis: `f64`, `u64`, `bool`,
   `null` and objects of custom type.

# Description

Please follow the official [description](https://github.com/antirez/listpack/blob/master/listpack.md) of the data structure first.

In order to implement the additional types, the unused data subencodings
are used.

# MSRV (Minimally-Supported Rust Version)

The `MSRV` is `1.70`.

# Building

Simply build using `cargo`:

```sh
cargo build
```

# Examples

Please take a look at the [/examples](./examples) directory, where you
may find a few examples showing the use of the crate.

Additionally, you may check out the unit tests
[/src/listpack.rs](./src/listpack.rs) directory to get familiar with
some more specific use-cases.

# LICENSE

[License](./LICENSE)
