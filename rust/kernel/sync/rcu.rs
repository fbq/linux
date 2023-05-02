// SPDX-License-Identifier: GPL-2.0

//! RCU support.
//!
//! C header: [`include/linux/rcupdate.h`](../../../../include/linux/rcupdate.h)

use crate::{
    bindings,
    sync::lock::{Backend, Lock},
    types::ForeignOwnable,
};

use core::marker::PhantomData;
use core::ops::Deref;
use core::sync::atomic::{AtomicPtr, Ordering::*};

/// Evidence that the RCU read side lock is held on the current thread/CPU.
///
/// The type is explicitly not `Send` because this property is per-thread/CPU.
///
/// # Invariants
///
/// The RCU read side lock is actually held while instances of this guard exist.
pub struct RcuGuard {
    _not_send: PhantomData<*mut ()>,
}

impl RcuGuard {
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

impl Default for RcuGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for RcuGuard {
    fn drop(&mut self) {
        // SAFETY: By the type invariants, the rcu read side is locked, so it is ok to unlock it.
        unsafe { bindings::rcu_read_unlock() };
    }
}

/// Acquires the RCU read side lock.
pub fn read_lock() -> RcuGuard {
    RcuGuard::new()
}

/// A RCU protected pointer.
///
/// # Invariants
///
/// `ptr` must be a result of [`ForeignOwnable::into_foregin`], and its value gets replaced every
/// time a `&mut self` function reads and [`ForeignOwnable::from_foreign`] the old value.
pub struct Rcu<P: ForeignOwnable> {
    ptr: AtomicPtr<core::ffi::c_void>,
    phantom: PhantomData<P>,
}

/// A retired RCU pointer.
///
/// Drop of this will eventually free it.
pub struct RcuOld<P: ForeignOwnable>(P);

impl<P: ForeignOwnable> Rcu<P> {
    /// Creates an RCU pointer.
    pub fn new(new: P) -> Self {
        Rcu {
            // XXX: should store(Release) used here? If that's not needed, it means we have
            // guarantees that every time we publish the RCU pointers, we make sure the previous
            // memory operations are visible.
            ptr: AtomicPtr::new(new.into_foreign() as *mut _),
            phantom: PhantomData,
        }
    }

    /// Reads the current RCU pointer.
    pub fn read(&self) -> *const core::ffi::c_void {
        self.ptr.load(Relaxed)
    }

    /// Dereferences the RCU pointer.
    ///
    /// The `_guard` parameter guarantees that a RCU read lock must be held and the borrowed
    /// reference cannot outlive the read-side critical section.
    pub fn dereference<'a, 'rcu>(&'a self, _guard: &'rcu RcuGuard) -> P::Borrowed<'rcu> {
        // SAFETY: Since we have `_guard` outlives the return value, per RCU guarantees the return
        // value must be valid until the end of its lifetime.
        //
        // ORDERING: Uses `Acquire` here since 1) Rust doesn't have `Consume` ordering 2) nor does
        // Rust respect address dependencies.
        unsafe { P::borrow(self.ptr.load(Acquire)) }
    }

    /// Atomically swap the old value with a new one.
    pub fn unsafe_swap_atomic(&self, new: P) -> RcuOld<P> {
        // XXX: The ordering here is that the load of the old `ptr` could pair with the store in
        // another `swap` or `atomic_swap`, in C side, we rely on address dependencies for the
        // paired ordering, however Rust doesn't have `Consume` ordering and address dependency
        // ordering may not be guaranteed, hence `Acquire` is used.
        let old_ptr = self.ptr.swap(new.into_foreign() as *mut _, AcqRel);

        RcuOld(
            // SAFETY: Per type invariants, `old_ptr` comes from previous `into_foreign`, the value
            // hasn't been consumed by other `from_foreign`.
            unsafe { P::from_foreign(old_ptr) },
        )
    }

    /// Non-atomically swap the old value with a new one.
    ///
    /// # Safety
    ///
    /// Since the swap is not atomic, the caller must guarantee that all [`swap_unsafe`]s are
    /// serialised (mostly via a lock).
    ///
    /// Note that since RCU provides that readers (i.e. [`Self::dereference`]) are not blocked by
    /// the updaters, so we cannot define this function a mutable one, hence the `unsafe` is used.
    pub(crate) unsafe fn unsafe_swap(&self, new: P) -> RcuOld<P> {
        let old_ptr = self.ptr.load(Acquire);

        self.ptr.store(new.into_foreign().cast_mut(), Release);

        RcuOld(
            // SAFETY: Per type invariants, `old_ptr` comes from previous `into_foreign`, the value
            // hasn't been consumed by other `from_foreign`.
            unsafe { P::from_foreign(old_ptr) },
        )
    }
}

impl<P: ForeignOwnable> Drop for Rcu<P> {
    fn drop(&mut self) {
        // XXX: The ordering here is that the load of the old `ptr` could pair with the store in
        // another `swap` or `atomic_swap`, in C side, we rely on address dependencies for the
        // paired ordering, however Rust doesn't have `Consume` ordering and address dependency
        // ordering may not be guaranteed, hence `Acquire` is used.
        let old_ptr = self.ptr.load(Acquire);

        // SAFETY: TODO
        unsafe {
            bindings::synchronize_rcu();
        }

        // SAFETY: Per type invariants, `old_ptr` comes from previous `into_foreign`, the value
        // hasn't been consumed by other `from_foreign`.
        drop(unsafe { P::from_foreign(old_ptr) });
    }
}

impl<P: ForeignOwnable> Drop for RcuOld<P> {
    fn drop(&mut self) {
        // SAFETY: TODO
        unsafe {
            bindings::synchronize_rcu();
        }
    }
}

pub unsafe trait Field<Base: ?Sized> {
    /// The type of the field.
    type Type: ?Sized;

    /// The anem of the field.
    const NAME: &'static str;

    /// Adjust the pointer from the containing type.
    ///
    /// # Safety
    ///
    /// `base` must be a non-null and aligned pointer to [`Self::Base`].
    unsafe fn field_of(base: *const Base) -> *const Self::Type;
}

pub unsafe trait FieldMut<Base: ?Sized>: Field<Base> {}

macro_rules! impl_field {
    (projection $base:ty { mut $field_name:ident: $field:ty } as $name:ident) => {
        struct $name;
        unsafe impl $crate::sync::rcu::Field<$base> for $name {
            type Type = $field;
            const NAME: &'static str = stringify!($field_name);
            unsafe fn field_of(base: *const $base) -> *const $field {
                unsafe { ::core::ptr::addr_of!((*base).$field_name) }
            }
        }
        unsafe impl $crate::sync::rcu::FieldMut<$base> for $name {}
    };
    (projection $base:ty { $field_name:ident: $field:ty } as $name:ident) => {
        struct $name;
        unsafe impl $crate::sync::rcu::Field<$base> for $name {
            type Type = $field;
            const NAME: &'static str = stringify!($field_name);
            unsafe fn field_of(base: *const $base) -> *const $field {
                unsafe { ::core::ptr::addr_of!((*base).$field_name) }
            }
        }
    };
}

#[pin_data]
pub struct RcuAndLock<T: ?Sized, B: Backend> {
    #[pin]
    lock: Lock<T, B>,
}

pub struct Updater<'a, T: ?Sized, B: Backend> {
    /// The lock guard held by an updater.
    guard: crate::sync::lock::Guard<'a, T, B>,
}

/// An updater can access all the fields immutably.
impl<T: ?Sized, B: Backend> Deref for Updater<'_, T, B> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Type invariants guarantee the lock is held.
        &*self.guard
    }
}

impl<T: ?Sized, B: Backend> Updater<'_, T, B> {
    /// Updates a RCU field.
    pub fn update<P: ForeignOwnable, F>(&self, new: P) -> RcuOld<P>
    where
        F: Field<T, Type = Rcu<P>>,
    {
        // SAFETY: `self.lock.data.get()` is non-null and aligned to `T`.
        let ptr = unsafe { F::field_of(self.guard.lock.data.get()) };

        // SAFETY: `T` owns the RCU field, and with `Guard` of `T` means exclusive accesses among
        // updaters.
        unsafe { (*ptr).unsafe_swap(new) }
    }

    /// Reads a RCU field.
    ///
    /// Since we are holding the updater side lock, we don't need RCU read-side locks.
    pub fn read_rcu<P: ForeignOwnable, F>(&self) -> P::Borrowed<'_>
    where
        F: Field<T, Type = Rcu<P>>,
    {
        // SAFETY: `self.lock.data.get()` is non-null and aligned to `T`.
        let ptr = unsafe { F::field_of(self.guard.lock.data.get()) };

        // SAFETY: We can read RCU fields since we are holding the updater lock.
        // ORDERING: Since we hold the updater side lock, we can avoid using ACQUIRE.
        unsafe { P::borrow((*ptr).read()) }
    }

    /// Accesses a non-RCU field mutably.
    pub fn project_mut<F>(&self) -> &mut <F as Field<T>>::Type
    where
        F: FieldMut<T>,
    {
        // SAFETY: `self.lock.data.get()` is non-null and aligned to `T`.
        let ptr = unsafe { <F as Field<T>>::field_of(self.guard.lock.data.get()) };

        // SAFETY: According to the safety requirement of `HasRcu`, `ptr` should point to a valid
        // `Rcu<_>` object.
        unsafe { &mut *(ptr as *mut _) }
    }
}

use crate::init::PinInit;
use crate::macros::pin_data;
use crate::pin_init;
use crate::sync::lock::spinlock::SpinLockBackend;

impl<T: ?Sized, B: Backend> RcuAndLock<T, B> {
    /// Projects the inner RCU field.
    pub fn project<P: ForeignOwnable, F>(&self) -> &Rcu<P>
    where
        F: Field<T, Type = Rcu<P>>,
    {
        // SAFETY: `self.lock.data.get()` is non-null and aligned to `T`.
        let ptr = unsafe { F::field_of(self.lock.data.get()) };

        // SAFETY: According to the safety requirement of `HasRcu`, `ptr` should point to a valid
        // `Rcu<_>` object.
        unsafe { &*ptr }
    }

    pub fn updater(&self) -> Updater<'_, T, B> {
        Updater {
            guard: self.lock.lock(),
        }
    }
}

impl<T, B: Backend> RcuAndLock<T, B> {
    /// Creates a [`RcuAndLock`] from a lock if the inner type has RCU fields.
    pub fn new(lock: impl PinInit<Lock<T, B>>) -> impl PinInit<Self> {
        pin_init!(Self {
            lock <- lock,
        })
    }
}

type RcuAndSpinLock<T> = RcuAndLock<T, SpinLockBackend>;

use crate::macros::kunit_tests;

#[kunit_tests(rust_rcu)]
mod tests {

    #[test]
    fn test_rcu() {
        use super::*;
        use alloc::boxed::Box;
        use kernel::prelude::*;
        use kernel::sync::Arc;
        use kernel::sync::SpinLock;
        use kernel::{c_str, static_lock_class};

        /*
         * ```c
         * struct bar {
         *   refcount_t ref;
         *   u64 x;
         * }
         * ```
         */
        struct Bar {
            x: u64,
        }

        /*
         * ```c
         * struct foo {
         *   spinlock_t lock;
         *   int a;
         *   struct bar __rcu *b;
         *   int __rcu *c;
         * }
         * ```
         */
        struct Foo {
            a: i32,
            b: Rcu<Arc<Bar>>,
            c: Rcu<Box<i32>>,
        }

        impl_field!(projection Foo { mut a: i32 } as FooA);
        impl_field!(projection Foo { b: Rcu<Arc<Bar>> } as FooB);
        impl_field!(projection Foo { c: Rcu<Box<i32>> } as FooC);

        /*
         * ```c
         * struct foo *foo = kzalloc(sizeof(*foo));
         * struct bar *tmp_bar;
         * int *tmp_c;
         *
         * foo->a = 12;
         *
         * tmp_bar = kzalloc(sizeof(struct bar));
         * refcount_set(&tmp_bar->ref, 1);
         * tmp_bar->x = 11;
         * foo->b = tmp_bar;
         *
         * tmp_c = kzalloc(sizeof(int));
         * *tmp_c = 42;
         * ```
         */
        let foo = Foo {
            a: 12,
            b: Rcu::new(Arc::try_new(Bar { x: 11 }).unwrap()),
            c: Rcu::new(Box::try_new(42i32).unwrap()),
        };

        let foo_lock: Pin<Box<RcuAndSpinLock<Foo>>> = Box::pin_init(RcuAndSpinLock::new(
            SpinLock::new(foo, c_str!("test"), static_lock_class!()),
        ))
        .expect("Allocation succeeds");

        // foo->a == 12
        assert_eq!(foo_lock.updater().a, 12);

        // Update
        //
        // ```c
        // int* new_c = kalloc(sizeof(int));
        // *new_c = 43;
        // ```
        let new_c = Box::try_new(43).unwrap();

        let old = foo_lock //
            .updater() // spin_lock(&foo->lock);
            .update::<_, FooC>(new_c); // foo->
        drop(old);

        /*
         * Won't compile.
        let c_ref = foo_lock.project::<_, FooA>().dereference(&Guard::new());
        pr_info!("{}", c_ref.0);
        */

        assert_eq!(foo_lock.project::<_, FooC>().dereference(&read_lock()), &43);
        assert_eq!(
            foo_lock
                .project::<_, FooB>()
                .dereference(&RcuGuard::new())
                .x,
            11
        );

        let old = foo_lock
            .updater()
            .update::<_, FooC>(Box::try_new(44).unwrap());
        drop(old);

        assert_eq!(foo_lock.project::<_, FooC>().dereference(&read_lock()), &44);
    }
}
