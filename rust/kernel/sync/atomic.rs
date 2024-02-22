// SPDX-License-Identifier: GPL-2.0

//! Atomic and barrier primitives.
//!
//! These primitives should have the same semantics as their C counterparts, for precise definitions
//! of the semantics, please refer tools/memory-model.

use core::cell::UnsafeCell;

mod arch;

/// An atomic `i32`.
pub struct AtomicI32(pub(crate) UnsafeCell<i32>);

impl AtomicI32 {
    /// Creates a new atomic value.
    pub fn new(v: i32) -> Self {
        Self(UnsafeCell::new(v))
    }

    /// Adds `i` to the atomic variable with RELAXED ordering.
    ///
    /// Returns the old value before the add.
    ///
    /// # Example
    ///
    /// ```rust
    /// use kernel::sync::atomic::AtomicI32;
    ///
    /// let a = AtomicI32::new(0);
    /// let b = a.fetch_add_relaxed(1);
    /// let c = a.fetch_add_relaxed(2);
    ///
    /// assert_eq!(b, 0);
    /// assert_eq!(c, 1);
    /// ```
    pub fn fetch_add_relaxed(&self, i: i32) -> i32 {
        arch::i32_fetch_add_relaxed(&self.0, i)
    }

    /// Subs `i` to the atomic variable with RELEASE ordering.
    ///
    /// Returns the old value before the sub.
    ///
    /// # Example
    ///
    /// ```rust
    /// use kernel::sync::atomic::AtomicI32;
    ///
    /// let a = AtomicI32::new(1);
    /// let b = a.fetch_sub_release(1);
    /// let c = a.fetch_sub_release(2);
    /// let d = a.fetch_sub_release(3);
    /// let e = a.fetch_sub_release(core::i32::MIN);
    ///
    /// assert_eq!(b, 1);
    /// assert_eq!(c, 0);
    /// assert_eq!(d, -2);
    /// ```
    pub fn fetch_sub_release(&self, i: i32) -> i32 {
        arch::i32_fetch_sub_release(&self.0, i)
    }
}
