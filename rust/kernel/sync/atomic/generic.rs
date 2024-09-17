// SPDX-License-Identifier: GPL-2.0

//! Generic atomic primitives.

use super::ops::*;
use super::ordering::*;
use crate::types::Opaque;

/// A generic atomic variable.
///
/// `T` must impl [`AllowAtomic`], that is, an [`AtomicImpl`] has to be chosen.
#[repr(transparent)]
pub struct Atomic<T: AllowAtomic>(Opaque<T>);

// SAFETY: `Atomic<T>` is safe to share among execution contexts because all accesses are atomic.
unsafe impl<T: AllowAtomic> Sync for Atomic<T> {}

/// Atomics that support basic atomic operations.
///
/// TODO: Unless the `impl` is a `#[repr(transparet)]` new type of an existing [`AllowAtomic`], the
/// impl block should be only done in atomic mod. And currently only basic integer types can
/// implement this trait in atomic mod.
///
/// # Safety
///
/// [`Self`] must have the same size and alignment as [`Self::Repr`].
pub unsafe trait AllowAtomic: Sized + Send + Copy {
    /// The backing atomic implementation type.
    type Repr: AtomicImpl;

    /// Converts into a [`Self::Repr`].
    fn into_repr(self) -> Self::Repr;

    /// Converts from a [`Self::Repr`].
    fn from_repr(repr: Self::Repr) -> Self;
}

// SAFETY: `T::Repr` is `Self` (i.e. `T`), so they have the same size and alignment.
unsafe impl<T: AtomicImpl> AllowAtomic for T {
    type Repr = Self;

    fn into_repr(self) -> Self::Repr {
        self
    }

    fn from_repr(repr: Self::Repr) -> Self {
        repr
    }
}

impl<T: AllowAtomic> Atomic<T> {
    /// Creates a new atomic.
    pub const fn new(v: T) -> Self {
        Self(Opaque::new(v))
    }

    /// Creates a reference to [`Self`] from a pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` has to be a valid pointer.
    /// - `ptr` has to be valid for both reads and writes for the whole life `'a`.
    /// - Accesses via the returned [`Self`] must not cause data race per [`LKMM`].
    ///
    /// [`LKMM`]: srctree/tools/memory-model
    pub unsafe fn from_ptr<'a>(ptr: *mut T) -> &'a Self
    where
        T: Sync,
    {
        // CAST: `T` is transparent to `Atomic<T>`.
        // SAFETY:
        unsafe { &*ptr.cast::<Self>() }
    }
}

impl<T: AllowAtomic> Atomic<T>
where
    T::Repr: AtomicHasBasicOps,
{
    /// Reads the atomic.
    ///
    /// # Examples
    ///
    /// Simple usages:
    ///
    /// ```rust
    /// use kernel::sync::atomic::generic::*;
    /// use kernel::sync::atomic::ordering::*;
    ///
    /// let x = Atomic::new(42i32);
    ///
    /// assert_eq!(42, x.read(Relaxed));
    ///
    /// let x = Atomic::new(42i64);
    ///
    /// assert_eq!(42, x.read(Relaxed));
    /// ```
    ///
    /// Customized new types in [`Atomic`]:
    ///
    /// ```rust
    /// use kernel::sync::atomic::generic::*;
    /// use kernel::sync::atomic::ordering::*;
    ///
    /// #[derive(Clone, Copy)]
    /// #[repr(transparent)]
    /// struct NewType(u32);
    ///
    /// // SAFETY: `NewType` is transparent to `u32`, which has the same size and alignment as
    /// // `i32`.
    /// unsafe impl AllowAtomic for NewType {
    ///     type Repr = i32;
    ///
    ///     fn into_repr(self) -> Self::Repr {
    ///         self.0 as i32
    ///     }
    ///
    ///     fn from_repr(repr: Self::Repr) -> Self {
    ///         NewType(repr as u32)
    ///     }
    /// }
    ///
    /// let n = Atomic::new(NewType(0));
    ///
    /// assert_eq!(0, n.read(Relaxed).0);
    /// ```
    #[inline(always)]
    pub fn read<Ordering: AcquireOrRelaxed>(&self, _: Ordering) -> T {
        let a = self.0.get().cast::<T::Repr>();

        // SAFETY: `self.0.get()` is a valid pointer, and since we have a `&self`, all accesses on
        // the pointed memory object must be atomic, and per the safety requirement of
        // `AllocAtomic`, a `*mut T` is a valid `*mut T::Repr`. Therefore `a` is a valid pointer.
        let v = unsafe {
            if Ordering::IS_RELAXED {
                T::Repr::atomic_read(a)
            } else {
                T::Repr::atomic_read_acquire(a)
            }
        };

        T::from_repr(v)
    }

    /// Sets the atomic.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kernel::sync::atomic::generic::*;
    /// use kernel::sync::atomic::ordering::*;
    ///
    /// let x = Atomic::new(42i32);
    ///
    /// assert_eq!(42, x.read(Relaxed));
    ///
    /// x.set(43, Relaxed);
    ///
    /// assert_eq!(43, x.read(Relaxed));
    /// ```
    ///
    #[inline(always)]
    pub fn set<Ordering: ReleaseOrRelaxed>(&self, v: T, _: Ordering) {
        let v = T::into_repr(v);
        let a = self.0.get().cast::<T::Repr>();

        // SAFETY: `self.0.get()` is a valid pointer, and since we have a `&self`, all accesses on
        // the pointed memory object must be atomic, and per the safety requirement of
        // `AllocAtomic`, a `*mut T` is a valid `*mut T::Repr`. Therefore `a` is a valid pointer.
        unsafe {
            if Ordering::IS_RELAXED {
                T::Repr::atomic_set(a, v)
            } else {
                T::Repr::atomic_set_release(a, v)
            }
        };
    }
}
