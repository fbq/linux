// SPDX-License-Identifier: GPL-2.0

//! Time related primitives.
//!
//! This module contains the kernel APIs related to time and timers that
//! have been ported or wrapped for usage by Rust code in the kernel.
//!
//! C header: [`include/linux/jiffies.h`](srctree/include/linux/jiffies.h).
//! C header: [`include/linux/ktime.h`](srctree/include/linux/ktime.h).

use core::marker::PhantomData;

/// The number of nanoseconds per millisecond.
pub const NSEC_PER_MSEC: i64 = bindings::NSEC_PER_MSEC as i64;

/// The time unit of Linux kernel. One jiffy equals (1/HZ) second.
pub type Jiffies = core::ffi::c_ulong;

/// The millisecond time unit.
pub type Msecs = core::ffi::c_uint;

/// Converts milliseconds to jiffies.
#[inline]
pub fn msecs_to_jiffies(msecs: Msecs) -> Jiffies {
    // SAFETY: The `__msecs_to_jiffies` function is always safe to call no
    // matter what the argument is.
    unsafe { bindings::__msecs_to_jiffies(msecs) }
}

/// A Rust wrapper around a `ktime_t`.
#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct Ktime {
    inner: bindings::ktime_t,
}

impl Ktime {
    /// Create a `Ktime` from a raw `ktime_t`.
    #[inline]
    pub fn from_raw(inner: bindings::ktime_t) -> Self {
        Self { inner }
    }

    /// Get the current time using `CLOCK_MONOTONIC`.
    #[inline]
    pub fn ktime_get() -> Self {
        // SAFETY: It is always safe to call `ktime_get` outside of NMI context.
        Self::from_raw(unsafe { bindings::ktime_get() })
    }

    /// Divide the number of nanoseconds by a compile-time constant.
    #[inline]
    fn divns_constant<const DIV: i64>(self) -> i64 {
        self.to_ns() / DIV
    }

    /// Returns the number of nanoseconds.
    #[inline]
    pub fn to_ns(self) -> i64 {
        self.inner
    }

    /// Returns the number of milliseconds.
    #[inline]
    pub fn to_ms(self) -> i64 {
        self.divns_constant::<NSEC_PER_MSEC>()
    }

    /// Checked substraction on [`Self`].
    ///
    /// Returns [`None`] if an arithmetic overflow would occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::time::Ktime;
    ///
    /// let ts1 = Ktime::ktime_get();
    /// let ts2 = Ktime::ktime_get();
    ///
    /// // An impossible ktime stamp only to demonstrate overflow behaviors.
    /// let impossible = Ktime::from_raw(i64::MIN);
    ///
    /// // `ktime_get()` is monotonic.
    /// assert_eq!(ts2.checked_sub(ts1).map(|d| d.to_ns() >= 0), Some(true));
    ///
    /// // `ktime_get()` is always non-negative, so this will trigger an overflow: `checked_sub()`
    /// // returns `None` in this case.
    /// assert!(ts2.checked_sub(impossible).is_none());
    /// ```
    #[inline]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.inner
            .checked_sub(other.inner)
            .map(|inner| Self { inner })
    }

    /// Wrapping substraction on [`Self`] with overflow detection.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic
    /// overflow would occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::time::Ktime;
    ///
    /// let ts1 = Ktime::ktime_get();
    /// let ts2 = Ktime::ktime_get();
    ///
    /// // An impossible ktime stamp only to demonstrate overflow behaviors.
    /// let impossible = Ktime::from_raw(i64::MIN);
    ///
    /// // `ktime_get()` is monotonic, and overflow shouldn't happen.
    /// let (d, is_overflow) = ts2.overflowing_sub(ts1);
    /// assert!(d.to_ns() >= 0 && !is_overflow);
    ///
    /// // `ktime_get()` is always non-negative, so this will trigger an overflow.
    /// let (_, is_overflow) = ts2.overflowing_sub(impossible);
    /// assert!(is_overflow);
    /// ```
    #[inline]
    pub fn overflowing_sub(self, other: Self) -> (Self, bool) {
        let (inner, is_overflow) = self.inner.overflowing_sub(other.inner);
        (Self { inner }, is_overflow)
    }

    /// Wrapping substraction on [`Self`].
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::time::Ktime;
    ///
    /// let ts1 = Ktime::ktime_get();
    /// let ts2 = Ktime::ktime_get();
    ///
    /// // An impossible ktime stamp only to demonstrate overflow behaviors.
    /// let impossible = Ktime::from_raw(i64::MIN);
    ///
    /// // `ktime_get()` is monotonicpen.
    /// assert!(ts2.wrapping_sub(ts1).to_ns() >= 0);
    ///
    /// // `ktime_get()` is always non-negative, so the wrapped result should always be negative.
    /// assert!(ts2.wrapping_sub(impossible).to_ns() < 0);
    /// ```
    #[inline]
    pub fn wrapping_sub(self, other: Self) -> Self {
        Self {
            inner: self.inner.wrapping_sub(other.inner),
        }
    }
}

/// Returns the number of milliseconds between two ktimes.
#[inline]
pub fn ktime_ms_delta(later: Ktime, earlier: Ktime) -> i64 {
    (later - earlier).to_ms()
}

impl core::ops::Sub for Ktime {
    type Output = Self;

    /// Substraction on [`Self`].
    ///
    /// When overflow, this function performs a wrapping substraction (with an error printed). This
    /// function should only be used when overflows are unexpected to happen, i.e. overflows are
    /// caused by hardware or internal bugs. [`Self::checked_sub`], [`Self::overflowing_sub`] or
    /// [`Self::wrapping_sub`] should be used in other cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::time::Ktime;
    ///
    /// let ts1 = Ktime::ktime_get();
    /// let ts2 = Ktime::ktime_get();
    ///
    /// // An impossible ktime stamp only to demonstrate overflow behaviors.
    /// let impossible = Ktime::from_raw(i64::MIN);
    ///
    /// // `ktime_get()` is monotonic.
    /// assert!((ts2 - ts1).to_ns() >= 0);
    ///
    /// // `ktime_get()` is always non-negative, and this will trigger an overflow, and the wrapped
    /// // result is always negative.
    /// assert!((ts2 - impossible).to_ns() < 0);
    /// ```
    #[inline]
    fn sub(self, other: Self) -> Self {
        // TODO: Use language generated hook (e.g. https://github.com/rust-lang/rfcs/pull/3632) for
        // this.
        let (delta, is_overflow) = self.overflowing_sub(other);

        if is_overflow {
            crate::pr_err!(
                "Ktime substraction overflow: {} - {}\n",
                self.inner,
                other.inner
            );
        }

        delta
    }
}

/// Represents a clock, that is, a unique time source and it can be queried for the current time.
pub trait Clock: Sized {
    /// Returns the current time for this clock.
    fn now() -> Instant<Self>;
}

/// Marker trait for clock sources that are guaranteed to be monotonic.
pub trait MonotonicClock: Clock {}

/// A timestamp reading of a given [`Clock`].
///
/// The only way to get a [`Self`] is via the corresponding [`Clock::now`].
pub struct Instant<T: Clock> {
    ktime: Ktime,
    clock: PhantomData<T>,
}

impl<T: Clock> Clone for Instant<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Clock> Copy for Instant<T> {}

impl<T: Clock> core::ops::Sub for Instant<T> {
    type Output = Ktime;

    /// Returns the difference of two reading of timestamps.
    #[inline]
    fn sub(self, other: Self) -> Self::Output {
        self.ktime - other.ktime
    }
}

impl<T: MonotonicClock> Instant<T> {
    /// Returns the time elapsed since this [`Self`] to now.
    ///
    /// Always returns non-negative values because [`Self`] can be only created by the corresponding
    /// [`Clock::now()`], so the [`Self`] that `&self` references must be created before this
    /// function is called, and given this function only exists for [`MonotonicClock`], `&self` must
    /// be ealier than now.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::time::{Clock, clock::KernelTime};
    ///
    /// let ts = KernelTime::now();
    ///
    /// // `KernelTime` is monotonic.
    /// assert!(ts.elapsed().to_ns() >= 0);
    /// ```
    #[inline]
    pub fn elapsed(&self) -> Ktime {
        T::now() - *self
    }
}

/// Contains the various clock source types available to the kernel.
pub mod clock {
    use super::*;

    /// A clock representing the default kernel time source (`CLOCK_MONOTONIC`).
    pub struct KernelTime;

    impl Clock for KernelTime {
        #[inline]
        fn now() -> Instant<Self> {
            Instant {
                // SAFETY: It is always safe to call `ktime_get` outside of NMI context.
                ktime: Ktime::from_raw(unsafe { bindings::ktime_get() }),
                clock: PhantomData,
            }
        }
    }

    /// `CLOCK_MONOTONIC` is monotonic.
    impl MonotonicClock for KernelTime {}
}
