
# i256

Optimized implementations of 256-bit signed and unsigned integers.

This contains a fixed-width, performant implementation for 256-bit signed and unsigned integers. This has significantly faster performance for basic math operations than comparable fixed-width integer types, since it can use optimizations from 128-bit integers on 64-bit architectures.

## Design

This contains variable-time, optimized algorithms for smaller big integers, primarily, 256-bit integers. It supports a no_std environment, requiring no allocation with all integers stored on the stack.

## Features

This crate is optimized for small variants of big integers, but a few additional types can be enabled via the following features:

- `i384`: Add the 384-bit I384 and U384 types.
- `i512`: Add the 512-bit I512 and U512 types.
- `i1024`: Add the 1024-bit I1024 and U1024 types.
- `stdint`: Support operations with fixed-width integer types. The `ULimb`, `UWide`, and other scalars defined may vary in size for optimal performance on the target architecture (64-bit multiplies, for example, are more expensive on 32-bit architectures): enabling this API adds in overloads for `u32`, `u64`, and `u128`, guaranteeing API stability across all platforms.

If you need larger integers, [`crypto-bigint`] has high-performance addition, subtraction, and multiplication. With integers with a large number of bits, it uses Karatsuba multiplication, which is significantly asymptotically faster.

## Use Case

[`i256`] is for a very specific purpose: relatively high-performance, fixed-sized 256-bit integers. This is dependent on support for native 64-bit integer multiplies on the architecture, and highly benefits from 64-bit to 128-bit widening multiplies (supported on `x86_64`). For example, on `x86_64`, we can get 256-bit multiplications in at worst 10 multiplies and 15 adds, and significantly faster in most cases. However, using 256-bit x 64-bit multiplication, we can get a worst case scenario in 5 `mul`, 3 `add`, and 6 `sub` instructions.

This will, for obvious reasons, not support significantly larger type sizes. It is optimized only for a smaller number of bits.

- [`bnum`]: Arbitrary-precision, fixed-width, big integer support.
- [`crypto-bigint`]: Constant-time, arbitrary-precision, fixed-width, big integer support suitable for cryptographically secure applications.
- [`num-bigint`], [`malachite`], or [`rug`]: Dynamic-width big integers with high-performance calculations with very large integers.

Specifically, [`i256`] has optimizations that would be considered anti-features for these libraries: better performance for smaller values (variable-time calculations) and operations with native, scalar values. This is particularly useful when doing incremental operations with [native integers][`u64`], with performance improvements greater than 2 fold in many cases,

## Versioning and Version Support

**Rustc Compatibility**

[`i256`] currently supports 1.60+, including stable, beta, and nightly. This aims to support at least the Rust included in the latest stable Debian release. Please report any errors compiling a supported [`i256`] version on a compatible Rustc version.

**Versioning**

[`i256`] uses [semantic versioning](https://semver.org/). Removing support for Rustc versions newer than the latest stable Debian or Ubuntu version is considered an incompatible API change, requiring a major (minor pre-1.0) version change.

## Changelog

All changes are documented in [CHANGELOG](https://github.com/Alexhuszagh/i256/blob/main/CHANGELOG).

## License

[`i256`] is dual licensed under the Apache 2.0 license as well as the MIT license.

Almost all of the accessory methods in [ints](/src/ints/), such as the `checked_*`, `unchecked_*`, `strict_*`, and others, including their documentation, are taken directly from the Rust implementation, specifically, [`uint_macros`] and [`int_macros`]. The core algorithms under [math](/src/math/) for numeric operations, both their wrapping and overflowing forms, are not.

[`uint_macros`]: https://github.com/rust-lang/rust/blob/master/library/core/src/num/uint_macros.rs
[`int_macros`]: https://github.com/rust-lang/rust/blob/master/library/core/src/num/int_macros.rs

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in i256 by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions. Contributing to the repository means abiding by the [code of conduct](https://github.com/Alexhuszagh/i256/blob/main/CODE_OF_CONDUCT.md).

[`crypto-bigint`]: https://crates.io/crates/crypto-bigint
[`bnum`]: https://crates.io/crates/bnum
[`num-bigint`]: https://crates.io/crates/num-bigint
[`malachite`]: https://crates.io/crates/malachite
[`rug`]: https://crates.io/crates/rug
[`u64`]: https://doc.rust-lang.org/std/primitive.u64.html
[`i256`]: https://crates.io/crates/i256
