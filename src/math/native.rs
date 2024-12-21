//! Arithmetic utilities from small, native integer components.
//!
//! This allows the construction of larger type sizes from native,
//! fast integers.

#![doc(hidden)]

// NOTE: We use the `wrapping`, etc. functions instead of the op
// traits because for non-primitive types, if we ever want to
// use this for wider types, then we don't have to rewrite this all.

// NOTE: Division and remainders aren't supported due to the difficulty in
// implementation. See `div.rs` for the implementation.

macro_rules! add_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_small =>
        $wrapping_small:ident,overflowing_small =>
        $overflowing_small:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add` and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add` and 4 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
            // NOTE: This is significantly slower than implementing with overflowing.
            let (v0, c0) = x0.overflowing_add(y0);
            let v1 = x1.wrapping_add(y1);
            let v1 = v1.wrapping_add(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value and if the add overflowed. In practice,
        /// the nightly (carrying) and the overflowing add variants
        /// have the same ASM generated, but this might not be the
        /// case in the future or for different architectures.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add`, 1 `adc`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, r8
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add`, 4 `adc`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, qword ptr [rsp + 24]
        ///     add     rax, rcx
        ///     mov     rax, qword ptr [rsp + 32]
        ///     adc     rax, r8
        ///     setb    r9b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     setb    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            let (v0, c0) = x0.overflowing_add(y0);
            let v1: $u;
            let c: bool;

            #[cfg(is_nightly)]
            {
                (v1, c) = x1.carrying_add(y1, c0);
            }

            #[cfg(not(is_nightly))]
            {
                let (r, c1) = x1.overflowing_add(y1);
                let (r, c2) = r.overflowing_add(c0 as $u);
                v1 = r;
                c = c1 | c2;
            }

            (v0, v1, c)
        }

        /// Const implementation of `wrapping_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add` and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///    mov     rax, rdi
        ///    add     rax, rdx
        ///    adc     rsi, 0
        ///    mov     rdx, rsi
        ///    ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///    add     rsi, qword ptr [rsp + 8]
        ///    adc     rdx, qword ptr [rsp + 16]
        ///    adc     rcx, 0
        ///    mov     rax, rdi
        ///    adc     r8, 0
        ///    mov     qword ptr [rdi], rsi
        ///    mov     qword ptr [rdi + 8], rdx
        ///    mov     qword ptr [rdi + 16], rcx
        ///    mov     qword ptr [rdi + 24], r8
        ///    ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_small(x0: $u, x1: $u, y: $u) -> ($u, $u) {
            // NOTE: This is significantly slower than implementing with overflowing.
            let (v0, c0) = x0.overflowing_add(y);
            let v1 = x1.wrapping_add(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow, and if the add overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add`, 1 `adc`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     setb    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_small(x0: $u, x1: $u, y: $u) -> ($u, $u, bool) {
            let (v0, c0) = x0.overflowing_add(y);
            let (v1, c1) = x1.overflowing_add(c0 as $u);
            (v0, v1, c1)
        }
    };
}

add_unsigned_impl!(
    u8,
    wrapping_full => wrapping_add_u8,
    overflowing_full => overflowing_add_u8,
    wrapping_small => wrapping_add_small_u8,
    overflowing_small => overflowing_add_small_u8
);
add_unsigned_impl!(
    u16,
    wrapping_full => wrapping_add_u16,
    overflowing_full => overflowing_add_u16,
    wrapping_small => wrapping_add_small_u16,
    overflowing_small => overflowing_add_small_u16
);
add_unsigned_impl!(
    u32,
    wrapping_full => wrapping_add_u32,
    overflowing_full => overflowing_add_u32,
    wrapping_small => wrapping_add_small_u32,
    overflowing_small => overflowing_add_small_u32
);
add_unsigned_impl!(
    u64,
    wrapping_full => wrapping_add_u64,
    overflowing_full => overflowing_add_u64,
    wrapping_small => wrapping_add_small_u64,
    overflowing_small => overflowing_add_small_u64
);
add_unsigned_impl!(
    u128,
    wrapping_full => wrapping_add_u128,
    overflowing_full => overflowing_add_u128,
    wrapping_small => wrapping_add_small_u128,
    overflowing_small => overflowing_add_small_u128
);
add_unsigned_impl!(
    usize,
    wrapping_full => wrapping_add_usize,
    overflowing_full => overflowing_add_usize,
    wrapping_small => wrapping_add_small_usize,
    overflowing_small => overflowing_add_small_usize
);

macro_rules! sub_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_small =>
        $wrapping_small:ident,overflowing_small =>
        $overflowing_small:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `sub` and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub` and 4 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1 = x1.wrapping_sub(y1);
            let v1 = v1.wrapping_sub(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit subtraction (2x u64 + 2x u64), it optimizes to 1
        /// `sub`, 1 `sbb`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, r8
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub`, 4 `sbb`, 2 `set`, and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     setb    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     setb    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1: $u;
            let c: bool;

            #[cfg(is_nightly)]
            {
                (v1, c) = x1.borrowing_sub(y1, c0);
            }

            #[cfg(not(is_nightly))]
            {
                let (r, c1) = x1.overflowing_sub(y1);
                let (r, c2) = r.overflowing_sub(c0 as $u);
                v1 = r;
                c = c1 | c2;
            }

            (v0, v1, c)
        }

        /// Const implementation of `wrapping_sub` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `sub` and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_small(x0: $u, x1: $u, y: $u) -> ($u, $u) {
            let (v0, c0) = x0.overflowing_sub(y);
            let v1 = x1.wrapping_sub(c0 as $u);
            (v0, v1)
        }

        /// Const implementation to subtract a small number from the wider type.
        ///
        /// Returns the value and if the sub overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit subtraction (2x u64 + 2x u64), it optimizes to 1
        /// `sub`, 1 `sbb`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     setb    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_small(x0: $u, x1: $u, y: $u) -> ($u, $u, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            // This is super efficient, it becomes an `add` and an `adc` (add carry).
            let (v0, c0) = x0.overflowing_sub(y);
            let (v1, c1) = x1.overflowing_sub(c0 as $u);
            (v0, v1, c1)
        }
    };
}

sub_unsigned_impl!(
    u8,
    wrapping_full => wrapping_sub_u8,
    overflowing_full => overflowing_sub_u8,
    wrapping_small => wrapping_sub_small_u8,
    overflowing_small => overflowing_sub_small_u8
);
sub_unsigned_impl!(
    u16,
    wrapping_full => wrapping_sub_u16,
    overflowing_full => overflowing_sub_u16,
    wrapping_small => wrapping_sub_small_u16,
    overflowing_small => overflowing_sub_small_u16
);
sub_unsigned_impl!(
    u32,
    wrapping_full => wrapping_sub_u32,
    overflowing_full => overflowing_sub_u32,
    wrapping_small => wrapping_sub_small_u32,
    overflowing_small => overflowing_sub_small_u32
);
sub_unsigned_impl!(
    u64,
    wrapping_full => wrapping_sub_u64,
    overflowing_full => overflowing_sub_u64,
    wrapping_small => wrapping_sub_small_u64,
    overflowing_small => overflowing_sub_small_u64
);
sub_unsigned_impl!(
    u128,
    wrapping_full => wrapping_sub_u128,
    overflowing_full => overflowing_sub_u128,
    wrapping_small => wrapping_sub_small_u128,
    overflowing_small => overflowing_sub_small_u128
);
sub_unsigned_impl!(
    usize,
    wrapping_full => wrapping_sub_usize,
    overflowing_full => overflowing_sub_usize,
    wrapping_small => wrapping_sub_small_usize,
    overflowing_small => overflowing_sub_small_usize
);

macro_rules! mul_unsigned_impl {
    (
        $u:ty,narrow =>
        $narrow:ident,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_small =>
        $wrapping_small:ident,overflowing_small =>
        $overflowing_small:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            // This optimizes down to ~6 muls and 6 adds, which really isn't bad.
            let (lo, hi) = $narrow(x0, y0);
            let x0_y1 = x0.wrapping_mul(y1);
            let x1_y0 = x1.wrapping_mul(y0);
            let hi = hi.wrapping_add(x0_y1);
            let hi = hi.wrapping_add(x1_y0);
            // NOTE: We can always skip the `x1 * y1` op since it always
            // overflows and will wrap to the same value.
            (lo, hi)
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value and the carry.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// It returns the lower and higher bits, and if it overflowed in
        /// 1 step. The results can then be used by the caller is desired.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            // This optimizes down to ~6 muls and 6 adds, which really isn't bad.
            let (lo, hi) = $narrow(x0, y0);
            let (x0_y1, c1) = x0.overflowing_mul(y1);
            let (x1_y0, c2) = x1.overflowing_mul(y0);
            let (hi, c3) = hi.overflowing_add(x0_y1);
            let (hi, c4) = hi.overflowing_add(x1_y0);
            // NOTE: We can always skip the `x1 * y1` op since it always
            // overflows and will wrap to the same value.
            (lo, hi, c1 | c2 | c3 | c4 | ((x1 != 0) & (y1 != 0)))
        }

        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// Returns the value and the carry.
        ///
        /// It returns the lower and higher bits. This is used when chaining
        /// together wider multiplications, so we can multiply large types
        /// without larger scalars (`u128`) and get the result in two scalars.
        /// This can never overflow.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $narrow(x: $u, y: $u) -> ($u, $u) {
            // This mimics multiplying 2 numbers from native limbs. It's not
            // that efficient but it emulates those faster instructions.

            const HALF: u32 = <$u>::BITS / 2;
            const LO: $u = <$u>::MAX >> HALF;

            let (x0, x1) = (x & LO, x.wrapping_shr(HALF));
            let (y0, y1) = (y & LO, y.wrapping_shr(HALF));

            let x0_y0 = x0 * y0;
            let x0_y1 = x0 * y1;
            let x1_y0 = x1 * y0;
            let x1_y1 = x1 * y1;
            let (mut lo, mut c) = (x0_y0 & LO, x0_y0.wrapping_shr(HALF));

            c += x1_y0;
            lo += c.wrapping_shl(HALF);
            let mut hi = c.wrapping_shr(HALF);

            c = lo.wrapping_shr(HALF);
            lo &= LO;
            c += x0_y1;

            lo += c.wrapping_shl(HALF);
            hi += c.wrapping_shr(HALF);
            hi += x1_y1;

            (lo, hi)
        }

        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $wrapping_small(x0: $u, x1: $u, n: $u) -> ($u, $u) {
            // NOTE: The compiler optimizes this down to 4 muls and 5 adds,
            // significantly better than the naive approach which is 6 muls
            // and 6 adds, which since some are fused mul/adds is good anyway.
            $wrapping_full(x0, x1, n, 0)
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value and the carry.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $overflowing_small(x0: $u, x1: $u, n: $u) -> ($u, $u, bool) {
            // NOTE: The compiler optimizes this down to 4 muls and 5 adds,
            // significantly better than the naive approach which is 6 muls
            // and 6 adds, which since some are fused mul/adds is good anyway.
            $overflowing_full(x0, x1, n, 0)
        }
    };
}

mul_unsigned_impl!(
    u8,
    narrow => mul_narrow_u8,
    wrapping_full => wrapping_mul_u8,
    overflowing_full => overflowing_mul_u8,
    wrapping_small => wrapping_mul_small_u8,
    overflowing_small => overflowing_mul_small_u8
);
mul_unsigned_impl!(
    u16,
    narrow => mul_narrow_u16,
    wrapping_full => wrapping_mul_u16,
    overflowing_full => overflowing_mul_u16,
    wrapping_small => wrapping_mul_small_u16,
    overflowing_small => overflowing_mul_small_u16
);
mul_unsigned_impl!(
    u32,
    narrow => mul_narrow_u32,
    wrapping_full => wrapping_mul_u32,
    overflowing_full => overflowing_mul_u32,
    wrapping_small => wrapping_mul_small_u32,
    overflowing_small => overflowing_mul_small_u32
);
mul_unsigned_impl!(
    u64,
    narrow => mul_narrow_u64,
    wrapping_full => wrapping_mul_u64,
    overflowing_full => overflowing_mul_u64,
    wrapping_small => wrapping_mul_small_u64,
    overflowing_small => overflowing_mul_small_u64
);
mul_unsigned_impl!(
    u128,
    narrow => mul_narrow_u128,
    wrapping_full => wrapping_mul_u128,
    overflowing_full => overflowing_mul_u128,
    wrapping_small => wrapping_mul_small_u128,
    overflowing_small => overflowing_mul_small_u128
);
mul_unsigned_impl!(
    usize,
    narrow => mul_narrow_usize,
    wrapping_full => wrapping_mul_usize,
    overflowing_full => overflowing_mul_usize,
    wrapping_small => wrapping_mul_small_usize,
    overflowing_small => overflowing_mul_small_usize
);

macro_rules! swap_unsigned_impl {
    ($($u:ty => $swap_bytes:ident, $reverse_bits:ident,)*) => ($(
        /// Reverses the byte order of the integer.
        ///
        /// # Assembly
        ///
        /// This optimizes very nicely, with efficient `bswap` or `rol`
        /// implementations for each.
        #[inline(always)]
        pub const fn $swap_bytes(x0: $u, x1: $u) -> ($u, $u) {
            (x1.swap_bytes(), x0.swap_bytes())
        }

        /// Reverses the order of bits in the integer.
        ///
        /// The least significant bit becomes the most significant bit, second
        /// least-significant bit becomes second most-significant bit, etc.
        /// Reversing bits is also quite inefficient, and for 128-bit and
        /// larger integers (2x `u64`), this is just as efficient as the
        /// native implementation. For smaller type sizes, the compiler can
        /// optimize the implementation, but we go beyond that realm.
        #[inline(always)]
        pub const fn $reverse_bits(x0: $u, x1: $u) -> ($u, $u) {
            (x1.reverse_bits(), x0.reverse_bits())
        }
    )*);
}

swap_unsigned_impl! {
    u8 => swap_bytes_u8, reverse_bits_u8,
    u16 => swap_bytes_u16, reverse_bits_u16,
    u32 => swap_bytes_u32, reverse_bits_u32,
    u64 => swap_bytes_u64, reverse_bits_u64,
    u128 => swap_bytes_u128, reverse_bits_u128,
    usize => swap_bytes_usize, reverse_bits_usize,
}

macro_rules! shift_unsigned_impl {
    ($($u:ty => $shl:ident, $shr:ident,)*) => ($(
        /// Const implementation of `Shl` for internal algorithm use.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
        // TODO: This optimizes poorly, fix this
        #[inline(always)]
        pub const fn $shl(x0: $u, x1: $u, shift: u32) -> ($u, $u) {
            const BITS: u32 = <$u>::BITS as u32;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shl(shift - BITS))
            } else if shift == 0 {
                (x0, x1)
            } else {
                // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                // so to `0xBCDE_FGH0`, or we need to carry the `D`. So,
                // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                // and then the value needs to be shifted left `<< (4 - 1)`.
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = x0.wrapping_shr(BITS - shift);
                (lo, hi | carry)
            }
        }

        /// Const implementation of `Shr` for internal algorithm use.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
        // TODO: This optimizes poorly, fix this
        #[inline(always)]
        pub const fn $shr(x0: $u, x1: $u, shift: u32) -> ($u, $u) {
            // This really isn't great and has a bit of branching,
            // but it works:
            //
            // ```asm
            // shr:
            //     mov     ecx, edx
            //     mov     edx, esi
            //     mov     esi, ecx
            //     and     esi, 63
            //     cmp     esi, 31
            //     jbe     .LBB2_1
            //     mov     eax, edx
            //     shr     eax, cl
            //     xor     edx, edx
            //     ret
            // .LBB2_1:
            //     mov     eax, edi
            //     test    esi, esi
            //     je      .LBB2_3
            //     mov     esi, edx
            //     shr     esi, cl
            //     shr     eax, cl
            //     neg     cl
            //     shl     edx, cl
            //     or      eax, edx
            //     mov     edx, esi
            // .LBB2_3:
            //     ret
            // ```
            const BITS: u32 = <$u>::BITS as u32;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (x1.wrapping_shr(shift - BITS), 0)
            } else if shift == 0 {
                (x0, x1)
            } else {
                // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                // so to `0x0ABC_DEFG`, or we need to carry the `D`. So,
                // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                // and then the value needs to be shifted left `<< (4 - 1)`.
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = x1.wrapping_shl(BITS - shift);
                (lo | carry, hi)
            }
        }
    )*);
}

shift_unsigned_impl! {
    u8 => shl_u8, shr_u8,
    u16 => shl_u16, shr_u16,
    u32 => shl_u32, shr_u32,
    u64 => shl_u64, shr_u64,
    u128 => shl_u128, shr_u128,
    usize => shl_usize, shr_usize,
}

macro_rules! rotate_unsigned_impl {
    ($($u:ty => $left:ident, $right:ident,)*) => ($(
        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// Please note this isn't the same operation as the `<<` shifting operator!
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $left(x0:$u, x1: $u, n: u32) -> ($u, $u) {
            // 0bXYFFFF -> 0bFFFFXY
            const BITS: u32 = <$u>::BITS;
            // First, 0 out all bits above as if we did a narrowing case.
            // Then, we want to get `n` as a narrow cast for `log2(BITS)`,
            // then see if we have any upper digits. This optimizes it
            // with these bit tricks over the regular approach on x86_64.
            // Say. we if `u16`, then we'd first 0 out above `001F`.
            // Then, if we have `0x10` set, then we have to swap `(lo, hi)`.
            // Then we can just shift on `0xF`.
            //
            // This isn't great but a better than some naive approaches.
            //
            // ```asm
            // rotate_left:
            //     mov     r8d, edi
            //     shr     r8d, 16
            //     test    sil, 16
            //     mov     eax, edi
            //     cmove   eax, r8d
            //     cmove   r8d, edi
            //     mov     edx, esi
            //     and     edx, 15
            //     je      .LBB
            //     mov     edi, eax
            //     mov     ecx, edx
            //     shl     edi, cl
            //     movzx   r9d, ax
            //     movzx   eax, r8w
            //     neg     sil
            //     and     sil, 15
            //     mov     ecx, esi
            //     shr     eax, cl
            //     mov     ecx, edx
            //     shl     r8d, cl
            //     mov     ecx, esi
            //     shr     r9d, cl
            //     or      eax, edi
            //     or      r9d, r8d
            //     mov     r8d, r9d
            // .LBB:
            //     movzx   ecx, r8w
            //     shl     eax, 16
            //     or      eax, ecx
            //     ret
            // ```
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1, x0)
            } else {
                (x0, x1)
            };
            if n == 0 {
                (x0, x1)
            } else {
                let hi = (x1.wrapping_shl(n)) | (x0.wrapping_shr(BITS - n));
                let lo = (x0.wrapping_shl(n)) | (x1.wrapping_shr(BITS - n));
                (lo, hi)
            }
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $right(x0:$u, x1: $u, n: u32) -> ($u, $u) {
            // See rotate_left for the description
            // 0bFFFFXY -> 0bXYFFFF
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1, x0)
            } else {
                (x0, x1)
            };
            if n == 0 {
                (x0, x1)
            } else {
                let hi = (x1.wrapping_shr(n)) | (x0.wrapping_shl(BITS - n));
                let lo = (x0.wrapping_shr(n)) | (x1.wrapping_shl(BITS - n));
                (lo, hi)
            }
        }
    )*);
}

rotate_unsigned_impl! {
    u8 => rotate_left_u8, rotate_right_u8,
    u16 => rotate_left_u16, rotate_right_u16,
    u32 => rotate_left_u32, rotate_right_u32,
    u64 => rotate_left_u64, rotate_right_u64,
    u128 => rotate_left_u128, rotate_right_u128,
    usize => rotate_left_usize, rotate_right_usize,
}

// Widening and narrowing conversions for primitive types.
macro_rules! unsigned_primitive_cast {
    (
        $u:ty,
        $s:ty,as_uwide =>
        $as_uwide:ident,as_unarrow =>
        $as_unarrow:ident,as_iwide =>
        $as_iwide:ident,as_inarrow =>
        $as_inarrow:ident,wide_cast =>
        $wide_cast:ident
    ) => {
        /// Convert an unsigned, narrow type to the wide type.
        #[inline(always)]
        pub const fn $as_uwide(x: $u) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x, 0)
        }

        /// Convert a signed, narrow type to the wide type.
        ///
        /// This is the same logic, and codegen as `is_wide`
        /// for signed types, just we keep it as an unsigned type
        /// for `hi`.
        #[inline(always)]
        pub const fn $as_iwide(x: $s) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let hi = <$u>::MIN.wrapping_sub(x.is_negative() as $u);
            (x as $u, hi)
        }

        /// Convert the wide value to a narrow, unsigned type.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $as_unarrow(x0: $u, x1: $u) -> $u {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let _ = x1;
            x0
        }

        /// Convert the wide value to a narrow, signed type.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $as_inarrow(x0: $u, x1: $u) -> $s {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let _ = x1;
            x0 as $s
        }

        /// Do a wide cast from unsigned to signed.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $wide_cast(x0: $u, x1: $u) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x0, x1 as $s)
        }
    };
}

unsigned_primitive_cast!(
    u8,
    i8,
    as_uwide => as_uwide_u8,
    as_unarrow => as_unarrow_u8,
    as_iwide => as_iwide_u8,
    as_inarrow => as_inarrow_u8,
    wide_cast => wide_cast_u8
);
unsigned_primitive_cast!(
    u16,
    i16,
    as_uwide => as_uwide_u16,
    as_unarrow => as_unarrow_u16,
    as_iwide => as_iwide_u16,
    as_inarrow => as_inarrow_u16,
    wide_cast => wide_cast_u16
);
unsigned_primitive_cast!(
    u32,
    i32,
    as_uwide => as_uwide_u32,
    as_unarrow => as_unarrow_u32,
    as_iwide => as_iwide_u32,
    as_inarrow => as_inarrow_u32,
    wide_cast => wide_cast_u32
);
unsigned_primitive_cast!(
    u64,
    i64,
    as_uwide => as_uwide_u64,
    as_unarrow => as_unarrow_u64,
    as_iwide => as_iwide_u64,
    as_inarrow => as_inarrow_u64,
    wide_cast => wide_cast_u64
);
unsigned_primitive_cast!(
    u128,
    i128,
    as_uwide => as_uwide_u128,
    as_unarrow => as_unarrow_u128,
    as_iwide => as_iwide_u128,
    as_inarrow => as_inarrow_u128,
    wide_cast => wide_cast_u128
);
unsigned_primitive_cast!(
    usize,
    isize,
    as_uwide => as_uwide_usize,
    as_unarrow => as_unarrow_usize,
    as_iwide => as_iwide_usize,
    as_inarrow => as_inarrow_usize,
    wide_cast => wide_cast_usize
);

macro_rules! add_signed_impl {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_usmall =>
        $wrapping_usmall:ident,overflowing_usmall =>
        $overflowing_usmall:ident,wrapping_ismall =>
        $wrapping_ismall:ident,overflowing_ismall =>
        $overflowing_ismall:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes very well, for example, on x86_64,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 2 `add` and 4 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_add(y0);
            let v1 = x1.wrapping_add(y1);
            let v1 = v1.wrapping_add(c0 as $s);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value and if the add overflowed. In practice,
        /// the nightly (carrying) and the overflowing add variants
        /// have the same ASM generated, but this might not be the
        /// case in the future or for different architectures.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit addition (1x u64, 1x i64 + 1x u64, 1x u64),
        /// it optimizes to 2
        /// `add`, 1 `adc`, 2 `set`, and 1 `or` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rdx, r8
        ///     seto    dil
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add`, 4 `adc`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     seto    r9b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_add(y0);
            let v1: $s;
            let c: bool;

            #[cfg(is_nightly)]
            {
                (v1, c) = x1.carrying_add(y1, c0);
            }

            #[cfg(not(is_nightly))]
            {
                let (r, c1) = x1.overflowing_add(y1);
                let (r, c2) = r.overflowing_add(c0 as $s);
                v1 = r;
                c = c1 | c2;
            }

            (v0, v1, c)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on x86_64,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_usmall(x0: $u, x1: $s, y: $u) -> ($u, $s) {
            let (v0, c0) = x0.overflowing_add(y);
            let v1 = x1.wrapping_add(c0 as $s);
            (v0, v1)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the add overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, 1 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     seto    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on x86_64,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_usmall(x0: $u, x1: $s, y: $u) -> ($u, $s, bool) {
            let (v0, c0) = x0.overflowing_add(y);
            let (v1, c1) = x1.overflowing_add(c0 as $s);
            (v0, v1, c1)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value, wrapping on overflow. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on x86_64,
        /// for a 128-bit addition (1x u64, 1x i64 + 1x i64), it
        /// optimizes to 1 `add`, 1 `adc`, and 1 `sar` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     sar     rcx, 63
        ///     add     rax, rdx
        ///     adc     rcx, rsi
        ///     mov     rdx, rcx
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on x86_64,
        /// for a 256-bit addition (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 2 `add`, 4 `adc`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, qword ptr [rsp + 16]
        ///     mov     r9, rax
        ///     sar     r9, 63
        ///     add     rcx, r9
        ///     adc     r9, r8
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, rax
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r9, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r9
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_ismall(x0: $u, x1: $s, y: $s) -> ($u, $s) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $wrapping_full(x0, x1, y0, y1)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value and if the add overflowed. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, signed value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on x86_64, for a 128-bit addition
        /// (1x u64, 1x i64 + 1x i64), it optimizes to 2 `add`, 1 `adc`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rdi, rcx
        ///     sar     rdi, 63
        ///     add     rdi, rdx
        ///     seto    dl
        ///     add     rsi, rcx
        ///     adc     rdi, 0
        ///     seto    cl
        ///     or      cl, dl
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on x86_64, for a 256-bit addition
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `add`, 4 `adc`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rdi, qword ptr [rsp + 16]
        ///     mov     r9, rdi
        ///     sar     r9, 63
        ///     add     rcx, r9
        ///     adc     r9, r8
        ///     seto    r8b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, rdi
        ///     adc     rcx, 0
        ///     adc     r9, 0
        ///     seto    dil
        ///     or      dil, r8b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r9
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_ismall(x0: $u, x1: $s, y: $s) -> ($u, $s, bool) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $overflowing_full(x0, x1, y0, y1)
        }
    };
}

add_signed_impl!(
    u8,
    i8,
    wrapping_full => wrapping_add_i8,
    overflowing_full => overflowing_add_i8,
    wrapping_usmall => wrapping_add_usmall_i8,
    overflowing_usmall => overflowing_add_usmall_i8,
    wrapping_ismall => wrapping_add_ismall_i8,
    overflowing_ismall => overflowing_add_ismall_i8
);
add_signed_impl!(
    u16,
    i16,
    wrapping_full => wrapping_add_i16,
    overflowing_full => overflowing_add_i16,
    wrapping_usmall => wrapping_add_usmall_i16,
    overflowing_usmall => overflowing_add_usmall_i16,
    wrapping_ismall => wrapping_add_ismall_i16,
    overflowing_ismall => overflowing_add_ismall_i16
);
add_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_add_i32,
    overflowing_full => overflowing_add_i32,
    wrapping_usmall => wrapping_add_usmall_i32,
    overflowing_usmall => overflowing_add_usmall_i32,
    wrapping_ismall => wrapping_add_ismall_i32,
    overflowing_ismall => overflowing_add_ismall_i32
);
add_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_add_i64,
    overflowing_full => overflowing_add_i64,
    wrapping_usmall => wrapping_add_usmall_i64,
    overflowing_usmall => overflowing_add_usmall_i64,
    wrapping_ismall => wrapping_add_ismall_i64,
    overflowing_ismall => overflowing_add_ismall_i64
);
add_signed_impl!(
    u128,
    i128,
    wrapping_full => wrapping_add_i128,
    overflowing_full => overflowing_add_i128,
    wrapping_usmall => wrapping_add_usmall_i128,
    overflowing_usmall => overflowing_add_usmall_i128,
    wrapping_ismall => wrapping_add_ismall_i128,
    overflowing_ismall => overflowing_add_ismall_i128
);
add_signed_impl!(
    usize,
    isize,
    wrapping_full => wrapping_add_isize,
    overflowing_full => overflowing_add_isize,
    wrapping_usmall => wrapping_add_usmall_isize,
    overflowing_usmall => overflowing_add_usmall_isize,
    wrapping_ismall => wrapping_add_ismall_isize,
    overflowing_ismall => overflowing_add_ismall_isize
);

macro_rules! sub_signed_impl {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_usmall =>
        $wrapping_usmall:ident,overflowing_usmall =>
        $overflowing_usmall:ident,wrapping_ismall =>
        $wrapping_ismall:ident,overflowing_ismall =>
        $overflowing_ismall:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes very well, for example, on x86_64,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 2 `sub` and 4 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1 = x1.wrapping_sub(y1);
            let v1 = v1.wrapping_sub(c0 as $s);
            (v0, v1)
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on x86_64,
        /// for a 128-bit subtraction (1x u64, 1x i64 + 1x u64, 1x u64),
        /// it optimizes to 2
        /// `sub`, 1 `sbb`, 2 `set`, and 1 `or` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rdx, r8
        ///     seto    dil
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on x86_64, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub`, 4 `sbb`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     seto    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1: $s;
            let c: bool;

            #[cfg(is_nightly)]
            {
                (v1, c) = x1.borrowing_sub(y1, c0);
            }

            #[cfg(not(is_nightly))]
            {
                let (mut r, c1) = x1.overflowing_sub(y1);
                let (r, c2) = r.overflowing_sub(c0 as $s);
                v1 = r;
                c = c1 | c2;
            }

            (v0, v1, c)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on x86_64,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_usmall(x0: $u, x1: $s, y: $u) -> ($u, $s) {
            let (v0, c0) = x0.overflowing_sub(y);
            let v1 = x1.wrapping_sub(c0 as $s);
            (v0, v1)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on x86_64, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, 1 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     seto    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on x86_64,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_usmall(x0: $u, x1: $s, y: $u) -> ($u, $s, bool) {
            let (v0, c0) = x0.overflowing_sub(y);
            let (v1, c1) = x1.overflowing_sub(c0 as $s);
            (v0, v1, c1)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on x86_64,
        /// for a 128-bit subtraction (1x u64, 1x i64 + 1x i64), it
        /// optimizes to 1 `add`, 1 `sub`, 1 `sbb`, and 1 `shr`
        /// instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     shr     rcx, 63
        ///     add     rcx, rsi
        ///     sub     rax, rdx
        ///     sbb     rcx, 0
        ///     mov     rdx, rcx
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on x86_64,
        /// for a 256-bit subtraction (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 1 `add`, 1 `adc`, 1 `sub`, 3 `sbb`, and 1
        /// `shr` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, qword ptr [rsp + 16]
        ///     mov     r9, rax
        ///     shr     r9, 63
        ///     add     r9, rcx
        ///     adc     r8, 0
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, rax
        ///     sbb     r9, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], r9
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $wrapping_ismall(x0: $u, x1: $s, y: $s) -> ($u, $s) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $wrapping_full(x0, x1, y0, y1)
        }

        /// Const implementation to subtract a small, signed number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, signed value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on x86_64, for a 128-bit subtraction
        /// (1x u64, 1x i64 + 1x i64), it optimizes to 2 `sub`, 1 `sbb`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rdi, rcx
        ///     sar     rdi, 63
        ///     sub     rdx, rdi
        ///     seto    dil
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on x86_64, for a 256-bit subtraction
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `sub`, 4 `sbb`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rdi, qword ptr [rsp + 16]
        ///     mov     r9, rdi
        ///     sar     r9, 63
        ///     sub     rcx, r9
        ///     sbb     r8, r9
        ///     seto    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, rdi
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $overflowing_ismall(x0: $u, x1: $s, y: $s) -> ($u, $s, bool) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $overflowing_full(x0, x1, y0, y1)
        }
    };
}

sub_signed_impl!(
    u8,
    i8,
    wrapping_full => wrapping_sub_i8,
    overflowing_full => overflowing_sub_i8,
    wrapping_usmall => wrapping_sub_usmall_i8,
    overflowing_usmall => overflowing_sub_usmall_i8,
    wrapping_ismall => wrapping_sub_ismall_i8,
    overflowing_ismall => overflowing_sub_ismall_i8
);
sub_signed_impl!(
    u16,
    i16,
    wrapping_full => wrapping_sub_i16,
    overflowing_full => overflowing_sub_i16,
    wrapping_usmall => wrapping_sub_usmall_i16,
    overflowing_usmall => overflowing_sub_usmall_i16,
    wrapping_ismall => wrapping_sub_ismall_i16,
    overflowing_ismall => overflowing_sub_ismall_i16
);
sub_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_sub_i32,
    overflowing_full => overflowing_sub_i32,
    wrapping_usmall => wrapping_sub_usmall_i32,
    overflowing_usmall => overflowing_sub_usmall_i32,
    wrapping_ismall => wrapping_sub_ismall_i32,
    overflowing_ismall => overflowing_sub_ismall_i32
);
sub_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_sub_i64,
    overflowing_full => overflowing_sub_i64,
    wrapping_usmall => wrapping_sub_usmall_i64,
    overflowing_usmall => overflowing_sub_usmall_i64,
    wrapping_ismall => wrapping_sub_ismall_i64,
    overflowing_ismall => overflowing_sub_ismall_i64
);
sub_signed_impl!(
    u128,
    i128,
    wrapping_full => wrapping_sub_i128,
    overflowing_full => overflowing_sub_i128,
    wrapping_usmall => wrapping_sub_usmall_i128,
    overflowing_usmall => overflowing_sub_usmall_i128,
    wrapping_ismall => wrapping_sub_ismall_i128,
    overflowing_ismall => overflowing_sub_ismall_i128
);
sub_signed_impl!(
    usize,
    isize,
    wrapping_full => wrapping_sub_isize,
    overflowing_full => overflowing_sub_isize,
    wrapping_usmall => wrapping_sub_usmall_isize,
    overflowing_usmall => overflowing_sub_usmall_isize,
    wrapping_ismall => wrapping_sub_ismall_isize,
    overflowing_ismall => overflowing_sub_ismall_isize
);

macro_rules! mul_signed_impl {
    ($($u:ty, $s:ty => $full:ident, $narrow:ident, $usmall:ident, $ismall:ident,)*) => ($(
        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses wrapping behavior and has no overflow checking.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (lo, hi) = $narrow(x0, y0);
            let x0_y1 = (x0 as $s).wrapping_mul(y1);
            let x1_y0 = x1.wrapping_mul(y0 as $s);
            let hi = (hi as $s).wrapping_add(x0_y1);
            let hi = hi.wrapping_add(x1_y0);
            (lo, hi)
        }

        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses wrapping behavior and has no overflow checking.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $usmall(x0: $u, x1: $s, n:$u) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            $full(x0, x1, n, 0)
        }

        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses wrapping behavior and has no overflow checking.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, signed factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $ismall(x0: $u, x1: $s, n:$s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // NOTE: This is just `as_iwide`.
            let n1 = <$u>::MIN.wrapping_sub(n.is_negative() as $u);
            let n0 = n as $u;
            let n1 = n1 as $s;
            $full(x0, x1, n0, n1)
        }
    )*);
}

mul_signed_impl! {
    u8, i8 => mul_i8, mul_narrow_u8, mul_usmall_i8, mul_ismall_i8,
    u16, i16 => mul_i16, mul_narrow_u16, mul_usmall_i16, mul_ismall_i16,
    u32, i32 => mul_i32, mul_narrow_u32, mul_usmall_i32, mul_ismall_i32,
    u64, i64 => mul_i64, mul_narrow_u64, mul_usmall_i64, mul_ismall_i64,
    u128, i128 => mul_i128, mul_narrow_u128, mul_usmall_i128, mul_ismall_i128,
    usize, isize => mul_isize, mul_narrow_usize, mul_usmall_isize, mul_ismall_isize,
}

macro_rules! overflowing_mul_signed_impl {
    ($($u:ty, $s:ty => $full:ident, $narrow:ident, $add:ident, $usmall:ident, $ismall:ident,)*) => ($(
        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses checked behavior, and is much slower than wrapping
        /// multiplication. When the overflow check is skipped, it's still
        /// slower (it requires 2 additional jumps and 1 extra add), but it's
        /// mostly comparable to the wrapping implementation.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            const BITS: u32 = <$u>::BITS;
            const MAX_SHIFT: u32 = BITS - 1;

            // NOTE: This is a mask that has each first go to `-1` for
            // the bit pattern if negative, otherwise 0, then it zeros
            // out everything if both are the same sign.
            let mask = ((x1 >> MAX_SHIFT) ^ (y1 >> MAX_SHIFT)) as $u;
            let is_zero = ((x0 == 0) & (x1 == 0)) | ((y0 == 0) & (y1 == 0));
            let should_be_positive = (x1 < 0) ^ (y1 < 0);
            let always_overflows = (x1 != 0) & (y1 != 0);

            // now need to get our absolute values. two's complement so this is easy
            let (xa0, xa1) = if x1 < 0 {
                $add(!x0, !x1, 1, 0)
            } else {
                (x0, x1)
            };
            let (ya0, ya1) = if y1 < 0 {
                $add(!y0, !y1, 1, 0)
            } else {
                (y0, y1)
            };

            let (lo, hi) = $narrow(xa0, ya0);
            let (x0_y1, c0) = xa0.overflowing_mul(ya1 as $u);
            let (x1_y0, c1) = (xa1 as $u).overflowing_mul(ya0);
            let (hi, c2) = hi.overflowing_add(x0_y1);
            let (hi, c3) = hi.overflowing_add(x1_y0);

            // convert back to the correct sign
            let (lo, carry) = (lo ^ mask).overflowing_sub(mask);
            let hi = (hi ^ mask).wrapping_sub(mask).wrapping_sub(carry as $u) as $s;

            let swapped_sign = should_be_positive ^ (hi < 0);
            let overflowed = c0 | c1 | c2 | c3 | swapped_sign | always_overflows;
            (lo, hi, !is_zero & overflowed)
        }

        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses checked behavior, and is much slower than wrapping
        /// multiplication.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $usmall(x0: $u, x1: $s, n:$u) -> ($u, $s, bool) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            $full(x0, x1, n, 0)
        }

        /// Const implementation of `Mul` for internal algorithm use.
        ///
        /// This uses checked behavior, and is much slower than wrapping
        /// multiplication.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `n` - A small, signed factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $ismall(x0: $u, x1: $s, n:$s) -> ($u, $s, bool) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // NOTE: This is just `as_iwide`.
            let n1 = <$u>::MIN.wrapping_sub(n.is_negative() as $u);
            let n0 = n as $u;
            let n1 = n1 as $s;
            $full(x0, x1, n0, n1)

        }
    )*);
}
overflowing_mul_signed_impl! {
    u8, i8 => overflowing_mul_i8, mul_narrow_u8, wrapping_add_i8, overflowing_mul_usmall_i8, overflowing_mul_ismall_i8,
    u16, i16 => overflowing_mul_i16, mul_narrow_u16, wrapping_add_i16, overflowing_mul_usmall_i16, overflowing_mul_ismall_i16,
    u32, i32 => overflowing_mul_i32, mul_narrow_u32, wrapping_add_i32, overflowing_mul_usmall_i32, overflowing_mul_ismall_i32,
    u64, i64 => overflowing_mul_i64, mul_narrow_u64, wrapping_add_i64, overflowing_mul_usmall_i64, overflowing_mul_ismall_i64,
    u128, i128 => overflowing_mul_i128, mul_narrow_u128, wrapping_add_i128, overflowing_mul_usmall_i128, overflowing_mul_ismall_i128,
    usize, isize => overflowing_mul_isize, mul_narrow_usize, wrapping_add_isize, overflowing_mul_usmall_isize, overflowing_mul_ismall_isize,
}

macro_rules! shift_signed_impl {
    ($($u:ty, $s:ty => $shl:ident, $shr:ident,)*) => ($(
        /// Const implementation of `Shl` for internal algorithm use.
        ///
        /// Rust follows the C++20 semantics for this: `a << b` is equal to
        /// `a * 2^b`, which is quite easy to calculate. This result will
        /// wrap. For example, we can get the following:
        ///
        /// ```rust
        /// // From: 0b0000000000000001
        /// // To:   0b1000000000000000
        /// assert_eq!(1i16 << 15, i16::MIN);
        /// ```
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
        // TODO: This optimizes poorly, fix this if possible.
        #[inline(always)]
        pub const fn $shl(x0: $u, x1: $s, shift: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            const BITS: u32 = <$u>::BITS as u32;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                let hi = x0.wrapping_shl(shift - BITS);
                (0, hi as $s)
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = x0.wrapping_shr(BITS - shift);
                (lo, hi | carry as $s)
            }
        }

        /// Const implementation of `Shr` for internal algorithm use.
        ///
        /// Rust follows the C++20 semantics for this: `a >> b` is equal to
        /// `a / 2^b`, rounded-down to -Inf. So, `-a >> b` will be never go
        /// to `0`, at worst it will be `-1`.
        ///
        /// On x86, this is done via the `sar` instruction, which is
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
        // TODO: This optimizes poorly, fix this if possible.
        #[inline(always)]
        pub const fn $shr(x0: $u, x1: $s, shift: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            const BITS: u32 = <$u>::BITS as u32;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                // NOTE: The MSB is 0 if positive and 1 if negative, so this will
                // always shift to 0 if positive and `-1` if negative.
                let hi = x1.wrapping_shr(BITS - 1);
                let lo = x1.wrapping_shr(shift - BITS);
                (lo as $u, hi)
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = (x1 as $u).wrapping_shl(BITS - shift);
                (lo | carry, hi)
            }
        }
    )*);
}

shift_signed_impl! {
    u8, i8 => shl_i8, shr_i8,
    u16, i16 => shl_i16, shr_i16,
    u32, i32 => shl_i32, shr_i32,
    u64, i64 => shl_i64, shr_i64,
    u128, i128 => shl_i128, shr_i128,
    usize, isize => shl_isize, shr_isize,
}

macro_rules! swap_signed_impl {
    ($($u:ty, $s:ty => $swap_bytes:ident, $reverse_bits:ident,)*) => ($(
        /// Reverses the byte order of the integer.
        ///
        /// # Assembly
        ///
        /// This optimizes very nicely, with efficient `bswap` or `rol`
        /// implementations for each.
        #[inline(always)]
        pub const fn $swap_bytes(x0: $u, x1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x1.swap_bytes() as $u, x0.swap_bytes() as $s)
        }

        /// Reverses the order of bits in the integer.
        ///
        /// The least significant bit becomes the most significant bit, second
        /// least-significant bit becomes second most-significant bit, etc.
        /// Reversing bits is also quite inefficient, and for 128-bit and
        /// larger integers (2x `u64`), this is just as efficient as the
        /// native implementation. For smaller type sizes, the compiler can
        /// optimize the implementation, but we go beyond that realm.
        #[inline(always)]
        pub const fn $reverse_bits(x0: $u, x1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // NOTE: Reversing bits is identical to unsigned.
            ((x1 as $u).reverse_bits(), x0.reverse_bits() as $s)
        }
    )*);
}

swap_signed_impl! {
    u8, i8 =>swap_bytesi8, reverse_bits_i8,
    u16, i16 => swap_bytes_i16, reverse_bits_i16,
    u32, i32 => swap_bytes_i32, reverse_bits_i32,
    u64, i64 => swap_bytes_i64, reverse_bits_i64,
    u128, i128 => swap_bytes_i128, reverse_bits_i128,
    usize, isize => swap_bytes_isize, reverse_bits_isize,
}

macro_rules! rotate_signed_impl {
    ($($u:ty, $s:ty => $left:ident, $right:ident,)*) => ($(
        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// This is identical to the unsigned variant: `T::MIN rol 1` is
        /// `1 as T`.
        ///
        /// TODO: Instructions
        // This is basically identical to the unsigned variant.
        //
        // ```asm
        // rotate_left:
        //     mov     r8d, edx
        //     mov     eax, esi
        //     test    r8b, 32
        //     mov     edx, edi
        //     cmove   edx, esi
        //     cmove   eax, edi
        //     mov     esi, r8d
        //     and     esi, 31
        //     je      .LBB
        //     mov     edi, edx
        //     mov     ecx, esi
        //     shl     edi, cl
        //     neg     r8b
        //     mov     r9d, eax
        //     mov     ecx, r8d
        //     shr     r9d, cl
        //     mov     ecx, esi
        //     shl     eax, cl
        //     mov     ecx, r8d
        //     shr     edx, cl
        //     or      r9d, edi
        //     or      eax, edx
        //     mov     edx, r9d
        // .LBB:
        //     ret
        // ```
        #[inline(always)]
        pub const fn $left(x0:$u, x1: $s, n: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // 0bXYFFFF -> 0bFFFFXY
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1 as $u, x0)
            } else {
                (x0, x1 as $u)
            };
            if n == 0 {
                (x0, x1 as $s)
            } else {
                let hi = (x1.wrapping_shl(n)) | (x0.wrapping_shr(BITS - n));
                let lo = (x0.wrapping_shl(n)) | (x1.wrapping_shr(BITS - n));
                (lo, hi as $s)
            }
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        /// TODO: Instructions
        #[inline(always)]
        pub const fn $right(x0:$u, x1: $s, n: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // 0bFFFFXY -> 0bXYFFFF
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1 as $u, x0)
            } else {
                (x0, x1 as $u)
            };
            if n == 0 {
                (x0, x1 as $s)
            } else {
                let hi = (x1.wrapping_shr(n)) | (x0.wrapping_shl(BITS - n));
                let lo = (x0.wrapping_shr(n)) | (x1.wrapping_shl(BITS - n));
                (lo, hi as $s)
            }
        }
    )*);
}

rotate_signed_impl! {
    u8, i8 => rotate_left_i8, rotate_right_i8,
    u16, i16 => rotate_left_i16, rotate_right_i16,
    u32, i32 => rotate_left_i32, rotate_right_i32,
    u64, i64 => rotate_left_i64, rotate_right_i64,
    u128, i128 => rotate_left_i128, rotate_right_i128,
    usize, isize => rotate_left_isize, rotate_right_isize,
}

// Widening and narrowing conversions for primitive types.
macro_rules! signed_primitive_cast {
    (
        $u:ty,
        $s:ty,as_uwide =>
        $as_uwide:ident,as_unarrow =>
        $as_unarrow:ident,as_iwide =>
        $as_iwide:ident,as_inarrow =>
        $as_inarrow:ident,wide_cast =>
        $wide_cast:ident
    ) => {
        // NOTE: This code was all test with the same algorithms in C++,
        // compiling for both little and big endian to ensure the logic
        // is the same, just as a precaution. For example:
        //
        // ```cpp
        // #include <cstdint>
        // #include <limits>
        //
        // int32_t as_inarrow_hard(int64_t v) {
        //     return (int32_t)v;
        // }
        //
        // int32_t as_inarrow_soft(int64_t v) {
        //     uint64_t mask = (uint64_t)std::numeric_limits<uint32_t>::max();
        //     uint64_t lo = ((uint64_t)v) & mask;
        //     return (int32_t)lo;
        // }
        // ```

        /// Convert an unsigned, narrow type to the wide type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_uwide(v: u32) -> u64 {
        ///     // hi bits will always be 0
        ///     v as u64
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_uwide(x: $u) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x, 0)
        }

        /// Convert a signed, narrow type to the wide type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_iwide_hard(v: i32) -> i64 {
        ///     v as i64
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_iwide_soft(x: i32) -> i64 {
        ///     let hi = u32::MIN.wrapping_sub(x.is_negative() as u32) as u64;
        ///     let hi = hi << 32;
        ///     let lo = (x as u32) as u64;
        ///     let x = lo | hi;
        ///     return x as i64;
        /// }
        /// ```
        ///
        /// This is analogous to the following C++ code:
        ///
        /// ```cpp
        /// int64_t as_iwide_hard(int32_t v) {
        ///     return v;
        /// }
        ///
        /// int64_t as_iwide_soft(int32_t v) {
        ///     bool is_negative = v < 0;
        ///     uint64_t hi = uint64_t(0) - uint64_t(is_negative);
        ///     hi <<= 32;
        ///     uint64_t lo = (uint64_t)((uint32_t)v);
        ///     uint64_t x = lo | hi;
        ///     return (int64_t)x;
        /// }
        /// ```
        ///
        /// This is way more efficient than using naive approaches, like checking `< 0`
        /// which brings in a `test` instruction.
        ///
        /// # Assembly
        ///
        /// This gets optimizes out very nicely, as a bit shift for all integers.
        /// ```asm
        /// as_iwide_i64:
        ///     mov     rax, rdi
        ///     mov     rdx, rdi
        ///     sar     rdx, 63
        ///     ret
        ///
        /// as_iwide_i128:
        ///     mov     rax, rdi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     sar     rdx, 63
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 24], rdx
        ///     mov     qword ptr [rdi + 16], rdx
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $as_iwide(x: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let hi = <$u>::MIN.wrapping_sub(x.is_negative() as $u);
            (x as $u, hi as $s)
        }

        /// Convert the wide value to a narrow, unsigned type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_unarrow_hard(v: i64) -> u32 {
        ///     v as u32
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_unarrow_soft(v: i64) -> u32 {
        ///     const MASK: u64 = u32::MAX as u64;
        ///     let lo = (v as u64) & MASK;
        ///     lo as u32
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_unarrow(x0: $u, x1: $s) -> $u {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            x0 as $u
        }

        /// Convert the wide value to a narrow, signed type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_inarrow_hard(v: i64) -> i32 {
        ///     v as i32
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_inarrow_soft(v: i64) -> i32 {
        ///     const MASK: u64 = u32::MAX as u64;
        ///     let lo = (v as u64) & MASK;
        ///     (lo as u32) as i32
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_inarrow(x0: $u, x1: $s) -> $s {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            x0 as $s
        }

        /// Do a wide cast from signed to unsigned.
        #[inline(always)]
        pub const fn $wide_cast(x0: $u, x1: $s) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x0, x1 as $u)
        }
    };
}

signed_primitive_cast!(
    u8,
    i8,
    as_uwide => as_uwide_i8,
    as_unarrow => as_unarrow_i8,
    as_iwide => as_iwide_i8,
    as_inarrow => as_inarrow_i8,
    wide_cast => wide_cast_i8
);
signed_primitive_cast!(
    u16,
    i16,
    as_uwide => as_uwide_i16,
    as_unarrow => as_unarrow_i16,
    as_iwide => as_iwide_i16,
    as_inarrow => as_inarrow_i16,
    wide_cast => wide_cast_i16
);
signed_primitive_cast!(
    u32,
    i32,
    as_uwide => as_uwide_i32,
    as_unarrow => as_unarrow_i32,
    as_iwide => as_iwide_i32,
    as_inarrow => as_inarrow_i32,
    wide_cast => wide_cast_i32
);
signed_primitive_cast!(
    u64,
    i64,
    as_uwide => as_uwide_i64,
    as_unarrow => as_unarrow_i64,
    as_iwide => as_iwide_i64,
    as_inarrow => as_inarrow_i64,
    wide_cast => wide_cast_i64
);
signed_primitive_cast!(
    u128,
    i128,
    as_uwide => as_uwide_i128,
    as_unarrow => as_unarrow_i128,
    as_iwide => as_iwide_i128,
    as_inarrow => as_inarrow_i128,
    wide_cast => wide_cast_i128
);
signed_primitive_cast!(
    usize,
    isize,
    as_uwide => as_uwide_isize,
    as_unarrow => as_unarrow_isize,
    as_iwide => as_iwide_isize,
    as_inarrow => as_inarrow_isize,
    wide_cast => wide_cast_isize
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_u32_test() {
        assert_eq!(overflowing_add_u32(1, 0, 1, 0), (2, 0, false));
        assert_eq!(overflowing_add_u32(u32::MAX, 0, u32::MAX, 0), (u32::MAX - 1, 1, false));
        assert_eq!(overflowing_add_u32(u32::MAX, 1, u32::MAX, 0), (u32::MAX - 1, 2, false));
        assert_eq!(overflowing_add_u32(u32::MAX, u32::MAX, 1, 0), (0, 0, true));
        assert_eq!(overflowing_add_u32(u32::MAX, u32::MAX, 2, 0), (1, 0, true));
        assert_eq!(
            overflowing_add_u32(u32::MAX, u32::MAX, u32::MAX, u32::MAX),
            (u32::MAX - 1, u32::MAX, true)
        );
    }

    #[test]
    fn sub_u32_test() {
        assert_eq!(overflowing_sub_u32(0, 0, 1, 0), (u32::MAX, u32::MAX, true));
        assert_eq!(overflowing_sub_u32(1, 0, 1, 0), (0, 0, false));
        assert_eq!(overflowing_sub_u32(1, 0, 0, 0), (1, 0, false));
        assert_eq!(overflowing_sub_u32(u32::MAX, 1, 0, 2), (u32::MAX, u32::MAX, true));
        assert_eq!(overflowing_sub_u32(0, 1, 0, 2), (0, 4294967295, true));
        assert_eq!(overflowing_sub_u32(0, 1, 1, 1), (u32::MAX, u32::MAX, true));
    }

    #[test]
    fn mul_u32_test() {
        assert_eq!(overflowing_mul_u32(u32::MAX, u32::MAX, u32::MAX, u32::MAX), (1, 0, true));
        assert_eq!(overflowing_mul_u32(1, 0, u32::MAX, 1), (u32::MAX, 1, false));
        assert_eq!(overflowing_mul_u32(2, 0, 2147483648, 0), (0, 1, false));
        assert_eq!(overflowing_mul_u32(1, 0, 1, 0), (1, 0, false));
        assert_eq!(overflowing_mul_u32(1, 0, 0, 0), (0, 0, false));
        assert_eq!(overflowing_mul_u32(u32::MAX, 1, 0, 2), (0, u32::MAX - 1, true));
        assert_eq!(overflowing_mul_u32(0, 1, 0, 2), (0, 0, true));
    }

    #[test]
    fn shl_u32_test() {
        assert_eq!(shl_u32(1, 0, 1), (2, 0));
        assert_eq!(shl_u32(0, 1, 0), (0, 1));
        assert_eq!(shl_u32(0, 1, 1), (0, 2));
        assert_eq!(shl_u32(1, 0, 32), (0, 1));
        assert_eq!(shl_u32(0, 1, 32), (0, 0));
        assert_eq!(shl_u32(2, 0, 31), (0, 1));
        assert_eq!(shl_u32(0, 2, 31), (0, 0));
        assert_eq!(shl_u32(1, 2, 31), (2147483648, 0));
    }

    #[test]
    fn shr_u32_test() {
        assert_eq!(shr_u32(1, 0, 1), (0, 0));
        assert_eq!(shr_u32(0, 1, 0), (0, 1));
        assert_eq!(shr_u32(0, 1, 1), (2147483648, 0));
        assert_eq!(shr_u32(1, 0, 32), (0, 0));
        assert_eq!(shr_u32(0, 1, 32), (1, 0));
        assert_eq!(shr_u32(2, 0, 31), (0, 0));
        assert_eq!(shr_u32(0, 2, 31), (4, 0));
        assert_eq!(shr_u32(1, 2, 31), (4, 0));
    }

    #[test]
    fn add_i32_test() {
        assert_eq!(overflowing_add_i32(1, 0, 1, 0), (2, 0, false));
        assert_eq!(overflowing_add_i32(u32::MAX, 0, u32::MAX, 0), (u32::MAX - 1, 1, false));
        assert_eq!(overflowing_add_i32(u32::MAX, 1, u32::MAX, 0), (u32::MAX - 1, 2, false));
        assert_eq!(overflowing_add_i32(u32::MAX, i32::MAX, 1, 0), (0, i32::MIN, true));
        assert_eq!(overflowing_add_i32(u32::MAX, i32::MAX, 2, 0), (1, i32::MIN, true));
        assert_eq!(
            overflowing_add_i32(u32::MAX, i32::MAX, u32::MAX, i32::MAX),
            (u32::MAX - 1, -1, true)
        );
    }
}
