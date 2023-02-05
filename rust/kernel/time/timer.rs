//! Timers
//!
//! This module allows Rust code to use the coarse-gained kernel timers (jiffies based).
//!
//! C header: [`include/linux/timer.h`](../../../../include/linux/timer.h)

use core::{
    marker::{PhantomData, PhantomPinned},
    pin::Pin,
};

use crate::container_of;
use crate::{
    bindings::timer_list, init::PinInit, prelude::*, str::CStr, sync::LockClassKey, types::Opaque,
};

use super::*;

/// A raw timer.
#[pin_data(PinnedDrop)]
#[repr(transparent)]
pub struct RawTimer {
    #[pin]
    opaque: Opaque<timer_list>,

    /// [`RawTimer`] is `!Unpin`, since [`timer_list`] contains self-referential pointers.
    #[pin]
    _p: PhantomPinned,
}

/// Timeout trait.
///
/// # Safety
///
/// This trait is unsafe because this trait implies there is a [`RawTimer`] inside the struct,
/// and if it's armed, it may be called at any time and may access the struct. Therefore the `drop`
/// function of an `impl Timeout` needs to make sure the [`RawTimer`] is shutdown before freeing
/// other members, otherwise it's UAF.
pub unsafe trait Timeout: Sized {
    /// Called with time is up.
    ///
    /// # Safety
    ///
    /// This can only be called inside [`RawTimer::bridge`], otherwise there may be a data race.
    ///
    /// # Implementation
    ///
    /// * `timeout` can only access the outer type.
    /// * `timeout` cannot operate on the [`RawTimer`].
    /// * `timeout` should be locally safe.
    unsafe fn timeout(_: *mut RawTimer) -> Result<Next>;

    /// Gets the pinned reference to the inner [`RawTimer`].
    fn raw_timer(self: Pin<&Self>) -> Pin<&RawTimer>;
}

impl RawTimer {
    /// Creates a [`RawTimer`].
    pub fn new<T: Timeout>(
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) -> impl PinInit<Self> {
        pin_init!(Self {
            opaque <- Opaque::ffi_init(|timer_list| {
                // SAFTEFY: `timer_list` is a valid pointer to a [`timer_list`], and
                // `Self::bridge::<T>` is a safe function.
                unsafe {
                    bindings::init_timer_key(
                        timer_list,
                        Some(Self::bridge::<T>),
                        flags,
                        name.as_char_ptr(),
                        key.as_ptr(),
                    );
                }
            }),
            _p: PhantomPinned,
        })
    }

    extern "C" fn bridge<T: Timeout>(ptr: *mut bindings::timer_list) {
        let ptr = ptr.cast::<RawTimer>();

        // SAFETY: Inside [`RawTimer::bridge`], it's safe.
        let next = unsafe { T::timeout(ptr) };

        // SAFETY: See the `expire_timers` function at C side, `ptr` points to this very same
        // [`RawTimer`] object (transparent to a `timer_list`), therefore `ptr` is valid.
        let timer = unsafe { &*ptr };

        match next {
            Ok(Next::Again(duration)) => {
                timer.schedule_at(jiffies_later(duration));
            }
            Err(_err) => {
                todo!("need Error::name()");
            }
            _ => {}
        }
    }

    /// Schedules a timer.
    ///
    /// Interior mutability is provided by `mod_timer()`. It's safe to call even inside a timer
    /// callback.
    pub fn schedule_at(&self, expires: Jiffies) {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of [`RawTimer::new`].
        unsafe {
            bindings::mod_timer(self.opaque.get(), expires);
        }
    }

    /// Cancels a scheduled timer.
    ///
    /// Callers should guarantee that the timer will eventually stop re-schedule itself, otherwise
    /// it's not guaranteed that this function will return.
    ///
    /// This function will wait until the timer callback finishes. Return `true` is the timer was
    /// pending and got deactivated.
    pub fn cancel(&self) -> bool {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of `init`.
        (unsafe { bindings::timer_delete_sync(self.opaque.get()) }) != 0
    }

    /// Shutdowns a scheduled timer.
    ///
    /// This function will wait until the timer callback finishes, and also make any future
    /// schedule of the timer no-ops.
    pub fn shutdown(&self) {
        // SAFETY: `self.opaque.get()` is a valid pointer to a [`timer_list`] and it's already
        // initialized per the safe guarantee of `init`.
        unsafe {
            bindings::timer_shutdown_sync(self.opaque.get());
        }
    }
}

#[pinned_drop]
impl PinnedDrop for RawTimer {
    fn drop(self: Pin<&mut Self>) {
        self.shutdown();
    }
}

// SAFETY: A `timer_list` can be transferred between threads.
unsafe impl Send for RawTimer {}

/// Next action of the timer.
pub enum Next {
    /// No more next step.
    Done,
    /// Schedules a timer to trigger later.
    Again(Jiffies),
}

/// A simple closure timer.
#[pin_data(PinnedDrop)]
pub struct FnTimer<F>
where
    F: Sync, // SYNC: `F` may be called on other CPU.
    F: FnMut() -> Result<Next>,
{
    #[pin]
    raw: RawTimer,
    f: F,
}

/// On-stack initializer for [`FnTimer`].
pub struct FnTimerStackInitialzer<F, I: PinInit<FnTimer<F>>>
where
    F: Sync, // SYNC: `F` may be called on other CPU.
    F: FnMut() -> Result<Next>,
{
    init: I,
    _p: PhantomData<F>,
}

impl<F, I: PinInit<FnTimer<F>>> FnTimerStackInitialzer<F, I>
where
    F: Sync, // SYNC: `F` may be called on other CPU.
    F: FnMut() -> Result<Next>,
{
    /// Initialises a [`FnTimer`] and do something until it gets dropped.
    pub fn with_timer<R>(self, g: impl FnOnce(Pin<&mut FnTimer<F>>) -> R) -> Result<R> {
        let pinned = core::pin::pin!(crate::init::__internal::StackInit::uninit());
        let pinned = crate::init::__internal::StackInit::init(pinned, self.init)?;
        Ok(g(pinned))
    }
}

impl<F> FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    /// Creates a [`FnTimer`].
    fn new(
        f: F,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) -> impl PinInit<Self> {
        pin_init!(Self {
            raw <- RawTimer::new::<Self>(flags, name, key),
            f,
        })
    }

    /// Creates a initializer for on-stack usage.
    pub fn new_on_stack(
        f: F,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) -> FnTimerStackInitialzer<F, impl PinInit<Self>> {
        FnTimerStackInitialzer {
            init: Self::new(f, flags, name, key),
            _p: PhantomData,
        }
    }
}

impl<F> FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
    F: 'static,
{
    /// Initialise a pinned object on heap.
    pub fn new_on_heap<I: InPlaceInit<Self>>(
        f: F,
        flags: u32,
        name: &'static CStr,
        key: &'static LockClassKey,
    ) -> Result<Pin<I>> {
        I::try_pin_init(try_pin_init!(Self {
            raw <- RawTimer::new::<Self>(flags, name, key),
            f,
        }))
    }
}

// SAFETY: [`FnTimer::drop`] shutdown the [`RawTimer`] first.
unsafe impl<F> Timeout for FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    fn raw_timer(self: Pin<&Self>) -> Pin<&RawTimer> {
        // SAFETY: `self` is pinned, therefore its field should always be pinned.
        unsafe { self.map_unchecked(|f| &f.raw) }
    }

    unsafe fn timeout(ptr: *mut RawTimer) -> Result<Next> {
        let obj = container_of!(ptr, Self, raw) as *mut Self;

        // IPML & SAFETY: Per safety guarantee of `timeout`, it's only called inside a timer bridge
        // function, and `ptr` is a pointer to [`Self::raw`], therefore `obj` is a vaild pointer
        // to [`Self`]. [`FnTimer`] is pinned-init, so no risk of being moved. No other way to
        // access [`FnTimer::f`], so no data race. And [`FnTimer::drop`] needs to wait for the
        // ongoing timer to finish, so no UAF. Hence it safe to dereference as mut here.
        unsafe { ((*obj).f)() }
    }
}

#[pinned_drop]
impl<F> PinnedDrop for FnTimer<F>
where
    F: Sync,
    F: FnMut() -> Result<Next>,
{
    fn drop(self: Pin<&mut Self>) {
        self.as_ref().raw_timer().shutdown()
    }
}

use crate::macros::kunit_tests;

#[kunit_tests(rust_timer)]
mod tests {
    #[test]
    fn test_timer() {
        use core::sync::atomic::{AtomicBool, Ordering};
        use kernel::c_str;
        use kernel::prelude::*;
        use kernel::sync::Arc;
        use kernel::thread::ThreadRef;
        use kernel::time::{
            jiffies_later,
            timer::{FnTimer, Next, Timeout},
        };

        // Tells whether the thread is already starting.
        let start = Arc::try_new(AtomicBool::new(false)).expect("allocaction of start succeeds");
        let start_in_thread = start.clone();

        let thread = ThreadRef::try_new(c_str!("hello"), move || {
            start_in_thread.store(true, Ordering::Relaxed);

            let mut local = 0;
            let flag = AtomicBool::new(false);

            static CLASS: kernel::sync::LockClassKey = kernel::sync::LockClassKey::new();

            let mut counter = 0;
            let timer = FnTimer::new_on_heap::<Box<_>>(
                move || {
                    counter += 1;

                    pr_info!("counter is {}", counter);
                    Ok(Next::Again(1000))
                },
                0,
                c_str!("rust tiemr"),
                &CLASS,
            )?;

            timer.as_ref().raw_timer().schedule_at(jiffies_later(0));
            core::mem::forget(timer);

            FnTimer::new_on_stack(
                || {
                    local += 1;

                    pr_info!("local is {}", local);

                    // Notifies the thread after 10 times
                    if local == 10 {
                        flag.store(true, Ordering::Relaxed);
                    }

                    Ok(Next::Again(1000))
                },
                0,
                c_str!("rust tiemr"),
                &CLASS,
            )
            .with_timer(|timer| {
                timer.as_ref().raw_timer().schedule_at(jiffies_later(0));
                while !flag.load(Ordering::Relaxed) {
                    // SAFETY: This is a sleeplable context and the current task state is not `TASK_DEAD`.
                    unsafe {
                        kernel::bindings::schedule();
                    }
                }
            })?;

            Ok(())
        })
        .expect("creation of thread succeeds");

        thread.wake_up();

        while !start.load(Ordering::Relaxed) {
            // SAFETY: This is a sleeplable context and the current task state is not `TASK_DEAD`.
            unsafe {
                kernel::bindings::schedule();
            }
        }

        thread.stop().expect("stop of thread succeeds");
    }
}
