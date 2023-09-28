// SPDX-License-Identifier: GPL-2.0

//! RCU support.
//!
//! C header: [`include/linux/rcupdate.h`](../../../../include/linux/rcupdate.h)

use crate::{
    bindings,
    error::Result,
    sync::lock::{Backend, Lock},
    types::ForeignOwnable,
};

use core::marker::PhantomData;
use core::ops::Deref;
use core::sync::atomic::{AtomicPtr, Ordering::*};
use core::sync::atomic::fence;
use alloc::boxed::Box;

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

/// An unsafe wrapper of RCU pointers
///
/// # Invariants
///
/// `ptr` needs to be either null or a valid pointer to T and protected by RCU
pub struct UnsafeRcu<T> {
    ptr: AtomicPtr<T>
}

impl<T> UnsafeRcu<T> {
    pub fn load(&self) -> *mut T {
        self.ptr.load(Relaxed)
    }

    /// Get a RCU protected reference.
    ///
    /// Note that the reference cannot outlive the corresponding RCU read lock guard, however it's
    /// possible the it outlives the pointer.
    pub fn dereference<'rcu>(&self, _guard: &'rcu RcuGuard) -> Option<&'rcu T> {
        let p = self.load();

        if p.is_null() {
            return None;
        }

        // ORDERING: Address dependencies are provided by the stronger Acquire.
        fence(Acquire);

        // SAFETY: Per invariants, `p` is a valid pointer, and since there is an RCU read-side
        // critical section outlives the return value, so the reference is under RCU protection and
        // therefore is valid through the whole lifetime.
        Some(unsafe { &* p })
    }

    /// Set a new value to the pointer
    ///
    /// # Safety
    ///
    /// * `new` needs to a either null or a valid pointer to T
    /// * `new` needs to be under RCU protection, i.e. recycling of `new` will need to wait for
    /// pre-existing RCU readers to finish.
    pub unsafe fn set(&self, new: *mut T) {
        self.ptr.store(new, Release);
    }

    pub unsafe fn new(ptr: *mut T) -> Self {
        Self {
            ptr: AtomicPtr::new(ptr)
        }
    }

    pub unsafe fn swap(&self, new: *mut T) -> *mut T {
        // xchg
        self.ptr.swap(new, AcqRel)
    }

    pub fn null() -> Self {
        Self {
            ptr: AtomicPtr::new(core::ptr::null_mut())
        }
    }
}

pub struct BoxRcu<T> {
    ptr: UnsafeRcu<T>,
    _owned: PhantomData<T>
}

impl<T> BoxRcu<T> {
    pub fn new(data: T) -> Result<Self> {
        Ok(Self {
            ptr: unsafe { UnsafeRcu::new(Box::into_raw(Box::try_new(data)?)) },
            _owned: PhantomData
        })
    }

    pub fn null() -> Self {
        Self {
            ptr: UnsafeRcu::null(),
            _owned: PhantomData
        }
    }

    pub fn dereference<'rcu>(&self, guard: &'rcu RcuGuard) -> Option<&'rcu T> {
        self.ptr.dereference(guard)
    }

    pub unsafe fn swap(&self, new: Box<T>) -> Option<Box<T>> {
        let old = unsafe {
            self.ptr.swap(Box::into_raw(new))
        };

        if old.is_null() {
            None
        } else {
            Some(unsafe { Box::from_raw(old) })
        }
    }

    pub fn update(&self, new: Box<T>) {
        // SAFETY: We are going to `synchronize_rcu()` before dropping the return, so it's safe.
        let old = unsafe { self.swap(new) };

        if let Some(old) = old {
            unsafe { bindings::synchronize_rcu(); }

            drop(old);
        }
    }
}

impl<T> Drop for BoxRcu<T> {
    fn drop(&mut self) {
        unsafe { bindings::synchronize_rcu(); }
    }
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
    pub(crate) unsafe fn replace(&self, new: P) -> RcuOld<P> {
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
        unsafe { (*ptr).replace(new) }
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
    fn test_rcu_unsafe() {
        use super::*;
        use alloc::boxed::Box;
        use kernel::prelude::*;
        use kernel::sync::Arc;
        use kernel::sync::SpinLock;
        use kernel::{c_str, static_lock_class};
        use core::ptr::{addr_of, addr_of_mut};

        #[derive(Copy, Clone)]
        struct Config {
            x: i32,
            y: i32,
            z: i32,
        }

        fn update<T>(data: &UnsafeRcu<T>, new: T) -> Result {
            let new_box: Box<T> = Box::try_new(new)?;

            let new: *mut T = Box::into_raw(new_box);

            let old = unsafe { data.swap(new) };

            if !old.is_null() {
                unsafe { bindings::synchronize_rcu(); }

                // SAFETY: `old` was previously set by the update function, so it comes from
                // a previous `Box::into_raw`, and since we called `synchronize_rcu` after `swap`,
                // no reader is referencing the old data now.
                drop(unsafe { Box::from_raw(old) });
            }

            Ok(())
        }

        unsafe fn copy_update<T: Copy>(data: &UnsafeRcu<T>, update: fn(&mut T)) -> Result {
            let old = data.load();

            if old.is_null() {
                return Ok(());
            }

            let mut new_box: Box<T> = Box::try_new(unsafe {*old})?;

            update(&mut new_box);

            let new: *mut T = Box::into_raw(new_box);

            unsafe { data.set(new); }

            if !old.is_null() {
                unsafe { bindings::synchronize_rcu(); }

                // SAFETY: `old` was previously set by the update function, so it comes from
                // a previous `Box::into_raw`, and since we called `synchronize_rcu` after `swap`,
                // no reader is referencing the old data now.
                drop(unsafe { Box::from_raw(old) });
            }

            Ok(())
        }

        let d = UnsafeRcu::null();

        update(&d, Config { x: 1, y: 2, z: 3 }).unwrap();

        assert_eq!(d.dereference(&RcuGuard::new()).unwrap().x, 1);

        update(&d, Config { x: 2, y: 2, z: 3 }).unwrap();

        assert_eq!(d.dereference(&RcuGuard::new()).unwrap().x, 2);

        unsafe { copy_update(&d, |cfg| { cfg.x = 3 }); }

        assert_eq!(d.dereference(&RcuGuard::new()).unwrap().x, 3);
        assert_eq!(d.dereference(&RcuGuard::new()).unwrap().y, 2);
    }

    #[test]
    fn test_rcu_list() {
        use super::*;
        use alloc::boxed::Box;
        use kernel::prelude::*;
        use kernel::sync::Arc;
        use kernel::sync::SpinLock;
        use kernel::{c_str, static_lock_class};

        struct Foo {
            x: i32,
            next: Rcu<Box<Option<Foo>>>,
        }
        impl_field!(projection Foo { next: Rcu<Box<Option<Foo>>> } as FooNext);

        fn for_each<F: FnMut(&Foo)>(list: &Rcu<Box<Option<Foo>>>, mut f: F) {
            let mut tmp = list;
            let g = read_lock();

            while let Some(foo) = tmp.dereference(&g).as_ref() {
                tmp = &foo.next;
                f(foo);
            }
        }

        let foo0 = Foo { x: 3, next: Rcu::new(Box::try_new(None).unwrap()) };
        let foo1 = Foo { x: 2, next: Rcu::new(Box::try_new(Some(foo0)).unwrap()) };
        let foo2 = Foo { x: 1, next: Rcu::new(Box::try_new(Some(foo1)).unwrap()) };

        let mut count = 0;
        let mut sum = 0;
        for_each(&Rcu::new(Box::try_new(Some(foo2)).unwrap()), |foo: &Foo| {
            count += 1;
            sum += foo.x;
        });

        assert_eq!(count, 3);
        assert_eq!(sum, 6);
    }

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
         * let c_ref = foo_lock.project::<_, FooC>().dereference(&read_lock());
         */

        // reference can outlive a RCU pointer but not the RCU read side lock.
        let g = read_lock();
        let c_ref = {
            let f = foo_lock.project::<_, FooC>();
            f.dereference(&g)
        };

        assert_eq!(c_ref, &43);
        drop(g);
        /* */

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
