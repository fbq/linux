// SPDX-License-Identifier: GPL-2.0

//! Atomic primitives.
//!
//! These primitives have the same semantics as their C counterparts, for precise definitions of
//! the semantics, please refer to tools/memory-model. Note that Linux Kernel Memory (Consistency)
//! Model is the only model for Rust development in kernel right now, please avoid to use Rust's
//! own atomics.

use crate::bindings::{atomic64_t, atomic_t};
use crate::types::Opaque;

mod r#impl;

/// Atomic 32bit signed integers.
pub struct AtomicI32(Opaque<atomic_t>);

/// Atomic 64bit signed integers.
pub struct AtomicI64(Opaque<atomic64_t>);

impl AtomicI32 {
    /// Creates an atomic variable with initial value `v`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::sync::atomic::*;
    ///
    /// let x = AtomicI32::new(0);
    ///
    /// assert_eq!(x.read(), 0);
    /// assert_eq!(x.fetch_add_relaxed(12), 0);
    /// assert_eq!(x.read(), 12);
    /// ```
    pub const fn new(v: i32) -> Self {
        AtomicI32(Opaque::new(atomic_t { counter: v }))
    }
}

// SAFETY: `AtomicI32` is safe to share among execution contexts because all accesses are atomic.
unsafe impl Sync for AtomicI32 {}

impl AtomicI64 {
    /// Creates an atomic variable with initial value `v`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::sync::atomic::*;
    ///
    /// let x = AtomicI64::new(0);
    ///
    /// assert_eq!(x.read(), 0);
    /// assert_eq!(x.fetch_add_relaxed(12), 0);
    /// assert_eq!(x.read(), 12);
    /// ```
    pub const fn new(v: i64) -> Self {
        AtomicI64(Opaque::new(atomic64_t { counter: v }))
    }
}

// SAFETY: `AtomicI64` is safe to share among execution contexts because all accesses are atomic.
unsafe impl Sync for AtomicI64 {}
