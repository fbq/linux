// SPDX-License-Identifier: GPL-2.0

//! Atomic primitives.
//!
//! These primitives have the same semantics as their C counterparts: and the precise definitions of
//! semantics can be found at [`LKMM`]. Note that Linux Kernel Memory (Consistency) Model is the
//! only model for Rust code in kernel, and Rust's own atomics should be avoided.
//!
//! # Data races
//!
//! [`LKMM`] atomics have different rules regarding data races:
//!
//! - A normal read doesn't data-race with an atomic read.
//! - A normal write from C side is treated as an atomic write if
//!   CONFIG_KCSAN_ASSUME_PLAIN_WRITES_ATOMIC=y.
//!
//! [`LKMM`]: srctree/tools/memory-mode/

pub mod generic;
pub mod ops;
pub mod ordering;

/// ```rust
/// use kernel::sync::atomic::generic::*;
/// use kernel::sync::atomic::ordering::*;
///
/// let x = Atomic::new(42u64);
///
/// assert_eq!(42, x.read(Relaxed));
/// ```
// SAFETY: `u64` and `i64` has the same size and alignment.
unsafe impl generic::AllowAtomic for u64 {
    type Repr = i64;

    fn into_repr(self) -> Self::Repr {
        self as _
    }

    fn from_repr(repr: Self::Repr) -> Self {
        repr as _
    }
}

/// ```rust
/// use kernel::sync::atomic::generic::*;
/// use kernel::sync::atomic::ordering::*;
///
/// let x = Atomic::new(42u64);
///
/// assert_eq!(42, x.fetch_add(12, Full));
/// assert_eq!(54, x.read(Relaxed));
///
/// x.add(13, Relaxed);
///
/// assert_eq!(67, x.read(Relaxed));
/// ```
impl generic::AllowAtomicArithmetic for u64 {
    type Delta = u64;

    fn delta_into_repr(d: Self::Delta) -> Self::Repr {
        d as _
    }
}

/// ```rust
/// use kernel::sync::atomic::generic::*;
/// use kernel::sync::atomic::ordering::*;
///
/// let x = Atomic::new(42usize);
///
/// assert_eq!(42, x.read(Relaxed));
/// ```
// SAFETY: `usize` has the same size and the alignment as `i64` for 64bit and the same as `i32` for
// 32bit.
unsafe impl generic::AllowAtomic for usize {
    #[cfg(CONFIG_64BIT)]
    type Repr = i64;
    #[cfg(not(CONFIG_64BIT))]
    type Repr = i32;

    fn into_repr(self) -> Self::Repr {
        self as _
    }

    fn from_repr(repr: Self::Repr) -> Self {
        repr as _
    }
}

/// ```rust
/// use kernel::sync::atomic::generic::*;
/// use kernel::sync::atomic::ordering::*;
///
/// let x = Atomic::new(42usize);
///
/// assert_eq!(42, x.fetch_add(12, Full));
/// assert_eq!(54, x.read(Relaxed));
///
/// x.add(13, Relaxed);
///
/// assert_eq!(67, x.read(Relaxed));
/// ```
impl generic::AllowAtomicArithmetic for usize {
    type Delta = usize;

    fn delta_into_repr(d: Self::Delta) -> Self::Repr {
        d as _
    }
}
