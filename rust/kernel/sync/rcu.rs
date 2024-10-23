// SPDX-License-Identifier: GPL-2.0

//! RCU support.
//!
//! C header: [`include/linux/rcupdate.h`](srctree/include/linux/rcupdate.h)

use crate::bindings;
use crate::{
    sync::atomic::{generic::Atomic, ordering::*},
    types::ForeignOwnable,
};
use core::{marker::PhantomData, ptr::NonNull};

/// Evidence that the RCU read side lock is held on the current thread/CPU.
///
/// The type is explicitly not `Send` because this property is per-thread/CPU.
///
/// # Invariants
///
/// The RCU read side lock is actually held while instances of this guard exist.
pub struct Guard {
    _not_send: PhantomData<*mut ()>,
}

impl Guard {
    /// Acquires the RCU read side lock and returns a guard.
    pub fn new() -> Self {
        // SAFETY: An FFI call with no additional requirements.
        unsafe { bindings::rcu_read_lock() };
        // INVARIANT: The RCU read side lock was just acquired above.
        Self {
            _not_send: PhantomData,
        }
    }

    /// Explicitly releases the RCU read side lock.
    pub fn unlock(self) {}
}

impl Default for Guard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        // SAFETY: By the type invariants, the rcu read side is locked, so it is ok to unlock it.
        unsafe { bindings::rcu_read_unlock() };
    }
}

/// Acquires the RCU read side lock.
pub fn read_lock() -> Guard {
    Guard::new()
}

/// An RCU protected pointer, the pointed object is protected by RCU.
///
/// # Invariants
///
/// Either the pointer is null, or it points to a return value of [`P::into_foreign`].
pub struct Rcu<P: ForeignOwnable>(Atomic<*mut core::ffi::c_void>, PhantomData<P>);

/// A pointer that has been unpublised, but hasn't waited for a grace period yet.
///
/// The pointed object may still have a existing RCU reader. Therefore a grace period is needed to
/// free the object.
///
/// # Invariants
///
/// The pointer has to be a return value of [`P::into_foreign`].
pub struct RcuOld<P: ForeignOwnable>(NonNull<core::ffi::c_void>, PhantomData<P>);

impl<P: ForeignOwnable> Drop for RcuOld<P> {
    fn drop(&mut self) {
        // SAFETY: As long as called in a sleepable context, which should be checked by klint,
        // `synchronize_rcu()` is safe to call.
        unsafe {
            bindings::synchronize_rcu();
        }

        // SAFETY: `self.0` is a return value of `P::into_foreign()`, so it's safe to call
        // `from_foreign()` on it. Plus, the above `synchronize_rcu()` guarantees no existing
        // `ForeignOwnable::borrow()` anymore.
        let p: P = unsafe { P::from_foreign(self.0.as_ptr()) };
        drop(p);
    }
}

impl<P: ForeignOwnable> Rcu<P> {
    /// Creates a new RCU pointer.
    pub fn new(p: P) -> Self {
        Self(Atomic::new(p.into_foreign().cast_mut()), PhantomData)
    }

    /// Dereferences the protected object.
    ///
    /// Returns `Some(b)`, where `b` is a reference-like borrowed type, if the pointer is not null,
    /// otherwise returns `None`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::alloc::{flags, KBox};
    /// use kernel::sync::rcu::{self, Rcu};
    ///
    /// let x = Rcu::new(KBox::new(100i32, flags::GFP_KERNEL)?);
    ///
    /// // Read in under RCU read lock protection.
    /// let v = x.try_dereference(&rcu::read_lock());
    ///
    /// assert_eq!(v, Some(&100i32));
    ///
    /// # Ok::<(), Error>(())
    /// ```
    pub fn try_dereference(&self, _rcu_guard: &Guard) -> Option<P::Borrowed<'_>> {
        // Ordering: The start of an address dependency.
        let ptr = self.0.read(Relaxed);

        if !ptr.is_null() {
            // SAFETY:
            // - Since `ptr` is not null, so it has to be a return value of `P::into_foreign()`.
            // - A RCU Guard outlives the returned `Borrowed`, this guarantees the return value
            //   will only be used under RCU read lock, and the RCU read lock prevents the pass of
            //   a grace period that `RcuOld` is waiting for, therefore no `from_foreign()` will be
            //   called for `ptr` as long as `Borrowed` exists.
            //
            //      CPU 0                                       CPU 1
            //      =====                                       =====
            //      { `x` is a reference to Rcu<Box<i32>> }
            //      let g = rcu::read_lock();
            //
            //      if let Some(b) = x.try_dereference(&g) {
            //      // drop(g); cannot be done, since `b` is still alive.
            //
            //                                              if let Some(old) = x.try_retire() {
            //                                                  // `x` is null now.
            //          println!("{}", b);
            //      }
            //                                                  drop(old):
            //                                                    synchronize_rcu();
            //      drop(g);
            //                                                    // a grace period passed.
            //                                                    // No `Borrowed` exists now.
            //                                                    from_foreign(...);
            //                                              }
            Some(unsafe { P::borrow(ptr) })
        } else {
            None
        }
    }

    /// Atomically replaces the pointer with new value.
    ///
    /// Returns `None` if the pointer's old value is null, otherwise returns `Some(old)`, where old
    /// is a [`RcuOld`] which can be used to free the old object eventually.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::alloc::{flags, KBox};
    /// use kernel::sync::rcu::{self, Rcu};
    ///
    /// let x = Rcu::new(KBox::new(100i32, flags::GFP_KERNEL)?);
    /// let q = KBox::new(101i32, flags::GFP_KERNEL)?;
    ///
    /// // Read in under RCU read lock protection.
    /// let g = rcu::read_lock();
    /// let v = x.try_dereference(&g);
    ///
    /// // Replace with a new object.
    /// let old = x.replace(q);
    ///
    /// assert!(old.is_some());
    ///
    /// // `v` should still read the old value.
    /// assert_eq!(v, Some(&100i32));
    ///
    /// // New readers should get the new value.
    /// assert_eq!(x.try_dereference(&rcu::read_lock()), Some(&101i32));
    ///
    /// drop(g);
    ///
    /// // Can free the object outside the read-side critical section.
    /// drop(old);
    /// # Ok::<(), Error>(())
    /// ```
    pub fn replace(&self, new: P) -> Option<RcuOld<P>> {
        let new_ptr = new.into_foreign().cast_mut();

        // Ordering: Pairs with the address dependency in `try_dereference()`.
        let old_ptr = self.0.xchg(new_ptr, Release);

        Some(RcuOld(NonNull::new(old_ptr)?, PhantomData))
    }

    /// Atomically takes away the object.
    ///
    /// This sets the pointer to null and returns the old pointer value if not null.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::alloc::{flags, KBox};
    /// use kernel::sync::rcu::{self, Rcu};
    ///
    /// let x = Rcu::new(KBox::new(100i32, flags::GFP_KERNEL)?);
    ///
    /// // Read in under RCU read lock protection.
    /// let g = rcu::read_lock();
    /// let v = x.try_dereference(&g);
    ///
    /// // Take the old object.
    /// let old = x.take();
    ///
    /// assert!(old.is_some());
    ///
    /// // `v` should still read the old value.
    /// assert_eq!(v, Some(&100i32));
    ///
    /// // New readers should get nothing.
    /// assert_eq!(x.try_dereference(&rcu::read_lock()), None);
    ///
    /// drop(g);
    ///
    /// // Can free the object outside the read-side critical section.
    /// drop(old);
    /// # Ok::<(), Error>(())
    /// ```
    pub fn take(&self) -> Option<RcuOld<P>> {
        // Fast return if old is null.
        if self.0.read(Relaxed).is_null() {
            return None;
        }

        // Ordering: Setting to a null pointer doesn't need to be Release.
        let old_ptr = self.0.xchg(core::ptr::null_mut(), Relaxed);

        Some(RcuOld(NonNull::new(old_ptr)?, PhantomData))
    }
}

impl<P: ForeignOwnable> Drop for Rcu<P> {
    fn drop(&mut self) {
        let ptr = *self.0.get_mut();
        if !ptr.is_null() {
            // SAFETY: Per type invariants, the pointer must be a return value of
            // `ForeignOwnable::into_foreign()` if it's not null. And having the mutable referece
            // of `Rcu` proves there is no existing readers (because `try_dereference()` takes a
            // immutable reference of `Rcu`.), and because of that, it's safe to free the object
            // without waiting for a grace period.
            drop(unsafe { P::from_foreign(ptr) });
        }
    }
}
