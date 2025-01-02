//!  Type for a single limb of the big integer.
//!
//!  A limb is analogous to a digit in base10, except, it stores 32-bit
//!  or 64-bit numbers instead.
//!
//!  This should be all-known 64-bit [`platforms`] supported by Rust.
//!
//!  Platforms where native 128-bit multiplication is explicitly supported:
//!      - `x86_64` (Supported via `MUL`).
//!      - `mips64` (Supported via `DMULTU`, which `HI` and `LO` can be
//!        read-from).
//!
//!  Platforms where native 64-bit multiplication is supported and
//!  you can extract hi-lo for 64-bit multiplications.
//!      `aarch64` (Requires `UMULH` and `MUL` to capture high and low bits).
//!      `powerpc64` (Requires `MULHDU` and `MULLD` to capture high and low
//! bits).
//!
//!  Platforms where native 128-bit multiplication is not supported,
//!  requiring software emulation.
//!      `sparc64` (`UMUL` only supported double-word arguments).
//!
//! [`platforms`]: https://forge.rust-lang.org/platform-support.html

// NOTE: Since we're using 128-bits under the hood, we just assume every
// architecture can use 64-bit limbs, which is true of most modern systems.
// This might not be true in which case we can address this at that time.

#[rustfmt::skip]
macro_rules! limb_doc {
    () => {
// a blank line to avoid a large first paragraph in the generated docs
"

This is guaranteed to have optimal performance for big integer
to scalar operations, however, the type size may be 32 or
64 bits depending on the architecture and pointer size.

To guaranteed code is fully portable on 32 and 64-bit systems,
use the fixed-width overloads. However, this might have suboptimal
performance if the bits in the type used is larger than the limb.
"
    };
}

#[rustfmt::skip]
macro_rules! wide_doc {
    () => {
// a blank line to avoid a large first paragraph in the generated docs
"

The performance of wide (double the bits of the limb) can be highly
variable: for addition, multiplication, and subtraction it can be
as fast as operations with limbs, however, the worst case performance
is as slow as operations between big integers.

For division, the performance is comparable to operations between two
big integers. If iteratively processing data from 64-bit integers,
you should benchmark first to see if, say, `((x as u128) * (y as u128)) * z`,
where `z` is [`u256`][crate::u256], is faster than `(x * z) * y`.
"
    };
}

/// The unsigned type used as a native "limb".
#[doc = limb_doc!()]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type ULimb = u64;

/// The unsigned type used as a native "limb".
#[doc = limb_doc!()]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type ULimb = u32;

/// The same sized type of the limb as a signed integer.
#[doc = limb_doc!()]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type ILimb = i64;

/// The same sized type of the limb as a signed integer.
#[doc = limb_doc!()]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type ILimb = i32;

/// An unsigned type double the width of the limb.
#[doc = wide_doc!()]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type UWide = u128;

/// An unsigned type double the width of the limb.
#[doc = wide_doc!()]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type UWide = u64;

/// A signed type double the width of the limb.
#[doc = wide_doc!()]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type IWide = i128;

/// A signed type double the width of the limb.
#[doc = wide_doc!()]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type IWide = i64;
