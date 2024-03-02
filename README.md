[![CI](https://github.com/iddm/listpack-redis/actions/workflows/ci.yml/badge.svg)](https://github.com/iddm/listpack-redis/actions/workflows/ci.yml)
[![Crates](https://img.shields.io/crates/v/listpack-redis.svg)](https://crates.io/crates/listpack-redis)
[![Docs](https://docs.rs/listpack-redis/badge.svg)](https://docs.rs/listpack-redis)
[![License](https://img.shields.io/badge/license-RSALv2_or_SSPLv1-blue?style=flat&logo=license)](./LICENSE)

# Listpack (Redis implementation)

This crate provides a Rust-idiomatic interface to the "listpack"
data-structure implemented in Redis as a part of Redis.

# Description

Please follow the official [description](https://github.com/antirez/listpack/blob/master/listpack.md) of the data structure first.

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

Additionally, you may check out the [/tests](./tests) directory to get
familiar with some more specific use-cases.

# LICENSE

[License](./LICENSE)
