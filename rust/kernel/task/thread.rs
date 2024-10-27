// SPDX-License-Identifier: GPL-2.0

//! A kernel thread (kthread).
//!
//! This module allows Rust code to create/wakeup/stop a kernel thread.

use core::ops::FnOnce;

use crate::{
    alloc::{flags::GFP_KERNEL, KBox},
    bindings, c_str,
    error::{from_err_ptr, to_result, Result},
    str::CStr,
    types::ARef,
};

use super::Task;

/// Raw kernel threads.
///
/// The threads are created via C-style functions and machine-word sized arguments.
///
/// # Safety
///
/// The creation of [`RawThread`] is unsafe because if a caller provides an incorrect thread
/// function or an incorrect thread argument, the new thread will corrupt memory or do other unsafe
/// behaviors.
pub struct RawThread {
    task: ARef<Task>,
}

impl RawThread {
    /// Creates a new thread using a C-style function pointer.
    ///
    /// # Safety
    ///
    /// This function actually doesn't dereference `arg` or call `f`, so even if the users pass
    /// incorrect parameters this function won't run into trouble. But if the users provide
    /// incorrect `arg` or `f` the new thread will corrupt memory or do other unsafe behaviors, so
    /// make it `unsafe`.
    ///
    /// The safety requirements of calling this function are:
    ///
    /// - Make sure `arg` is a proper pointer that points to a valid memory location when the new
    ///   thread begins to run.
    ///
    /// - Make sure `f` is a proper function pointer and `f` handles `arg` correctly.
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory allocation and
    /// waiting for the completion, therefore do not call this in atomic contexts (i.e.
    /// preemption-off contexts).
    pub unsafe fn try_new(
        name: &CStr,
        f: unsafe extern "C" fn(*mut core::ffi::c_void) -> core::ffi::c_int,
        arg: *mut core::ffi::c_void,
    ) -> Result<Self> {
        // SAFETY: `kthread_create_on_node` will copy the content of `name`, so we don't need to
        // make the `name` live longer.
        let task_ptr = from_err_ptr(unsafe {
            bindings::kthread_create_on_node(
                Some(f),
                arg,
                bindings::NUMA_NO_NODE,
                c_str!("%s").as_ptr() as _,
                name.as_ptr(),
            )
        })?;

        // SAFETY: `task_ptr` is a valid pointer for a `task_struct` because we've checked with
        // `from_err_ptr` above.
        let task_ref = unsafe { &*(task_ptr.cast::<Task>()) };

        // Increases the refcount of the task, so that it won't go away if it `do_exit`.
        Ok(RawThread {
            task: task_ref.into(),
        })
    }

    /// Wakes up the thread.
    ///
    /// Note that a newly created thread (via [`RawThread::try_new`]) will not run until a
    /// [`RawThread::wake_up`] is called.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn wake_up(&self) {
        self.task.wake_up();
    }

    /// Stops the thread.
    ///
    /// - If the thread hasn't been waken up after creation, the thread function won't be called,
    ///   and this function will return `-EINTR`. Note that a thread may not be waken up even after
    ///   [`RawThread::wake_up`] is called.
    ///
    /// - Otherwise, waits for the thread function to return or the thread `do_exit` itself.
    ///
    /// Consumes the [`RawThread`] so that it's not accessible and return the exit code of the
    /// thread.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn stop(self) -> Result {
        // SAFETY: `self.task.0.get()` is a valid pointer to a kernel thread structure, the refcount
        // of which is increased in `[RawThread::try_new`], so it won't point to a freed
        // `task_struct`. And it's not stopped because `stop` will consume the [`RawThread`].
        let ret = unsafe { bindings::kthread_stop(self.task.0.get()) };

        to_result(ret)
    }
}

/// Bridge function of type `F` from Rust ABI to C.
extern "C" fn bridge<F>(data: *mut core::ffi::c_void) -> i32
where
    F: FnOnce() -> Result,
{
    // SAFETY: `data` is the result of [`KBox::into_raw`], therefore it's safe to [`KBox::from_raw`]
    // here.
    let f = unsafe { KBox::from_raw(data as *mut F) };

    // TODO: Make KBox<FnOnce()> impl FnOnce<Args>.
    let f = KBox::into_inner(f);

    match f() {
        Ok(()) => 0,
        Err(e) =>
        // Changes the return value if it's `-ENITR`, in other words, we don't allow a thread
        // function to return `-EINTR`.
        //
        // Rationale: the kernel uses `-EINTR` to indicate that the kernel thread gets stopped
        // before it's able to run (the exit code is set at C side via a special call to `do_exit`).
        // In that case, there is no new thread to own the thread argument, therefore the `stop`
        // functions need to recycle the thread argument. If we allow thread function to return
        // `-EINTR`, [`Thread::stop`] will receive it as the exit code, and we're unable to differ
        // these two cases:
        // 1) stopped before run and 2) returning `-ENITR` from thread function.
        //
        // Note that currently in kernel, no one actually calls `do_exit` with `-EINTR` or returns
        // `-EINTR` from thread function other than the special case mentioned above.
        {
            if e.to_errno() == -(bindings::EINTR as i32) {
                -(bindings::EINVAL as i32)
            } else {
                e.to_errno()
            }
        }
    }
}

/// A kernel thread handle.
pub struct Thread {
    /// Raw kernel thread.
    raw: RawThread,

    /// Pointer to the thread argument.
    arg_ptr: *const core::ffi::c_void,

    /// Drop function to recycle arg
    drop_arg: fn(*const core::ffi::c_void),
}

impl Thread {
    /// Creates a new thread.
    ///
    /// Note that newly created thread will not run until a [`Self::wake_up`] is called.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::prelude::*;
    /// use kernel::{c_str, sync::{new_condvar, new_mutex, Arc, CondVar, Mutex}, task::Thread};
    ///
    /// let boxed = KBox::new(42, GFP_KERNEL)?;
    /// let lock = Arc::pin_init(new_mutex!(false), GFP_KERNEL)?;
    /// let cv = Arc::pin_init(new_condvar!(), GFP_KERNEL)?;
    ///
    /// let t = Thread::try_new(c_str!("rust-thread"), {
    ///     let lock = lock.clone();
    ///     let cv = cv.clone();
    ///     move || {
    ///         *(lock.lock()) = true;
    ///         cv.notify_all();
    ///         Ok(())
    ///     }
    /// })?;
    ///
    /// t.wake_up();
    ///
    /// let mut g = lock.lock();
    /// while !*g {
    ///     cv.wait(&mut g);
    /// }
    ///
    /// assert!(t.stop().is_ok());
    ///
    /// # Ok::<(), Error>(())
    /// ```
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory allocation and
    /// waiting for the completion, therefore do not call this in atomic contexts (i.e.
    /// preemption-off contexts).
    pub fn try_new<F>(name: &CStr, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result,
        F: Send + 'static,
    {
        // Allocate closure here, because this function may return before the bridged function (the
        // function that uses the closure) get executed.
        let boxed_fn = KBox::new(f, GFP_KERNEL)?;
        let data = KBox::into_raw(boxed_fn);

        // SAFETY: `bridge::<F>` is a proper function pointer to a C function, and
        // [`KBox::from_raw`] will be used in it to consume the raw pointer in the new thread.
        let result = unsafe { RawThread::try_new(name, bridge::<F>, data as _) };

        if result.is_err() {
            // Creation fails, we need to consume the raw pointer `data` because there is no new
            // thread to own the underlying object, we should let the current thread own it.
            //
            // SAFETY: We [`KBox::from_raw`] back what we just [`KBox::into_raw`], and since the new
            // thread is not created, so no one touches `data`.
            unsafe {
                KBox::from_raw(data);
            }
        }

        result.map(|raw| Thread {
            raw,
            arg_ptr: data as _,
            drop_arg: |ptr: *const core::ffi::c_void| {
                // SAFETY: `ptr` is what we [`KBox::into_raw`] and store at [`Thread::arg_ptr`], and
                // `drop_arg` only get called if the thread hasn't run, which means no one
                // [`KBox::from_raw`] the `ptr`, and that means we can safely do it.
                unsafe {
                    KBox::from_raw(ptr as *mut F);
                }
            },
        })
    }

    /// Wakes up the thread.
    ///
    /// Note that a newly created thread (e.g. via [`Thread::try_new`]) will not run until a
    /// [`Thread::wake_up`] is called.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn wake_up(&self) {
        self.raw.wake_up()
    }

    /// Creates a new thread and run it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::prelude::*;
    /// use kernel::{c_str, sync::{new_condvar, new_mutex, Arc, CondVar, Mutex}, task::Thread};
    ///
    /// let boxed = KBox::new(42, GFP_KERNEL)?;
    /// let lock = Arc::pin_init(new_mutex!(false), GFP_KERNEL)?;
    /// let cv = Arc::pin_init(new_condvar!(), GFP_KERNEL)?;
    ///
    /// let t = Thread::try_run(c_str!("rust-thread"), {
    ///     let lock = lock.clone();
    ///     let cv = cv.clone();
    ///     move || {
    ///         *(lock.lock()) = true;
    ///         cv.notify_all();
    ///         Ok(())
    ///     }
    /// })?;
    ///
    /// let mut g = lock.lock();
    /// while !*g {
    ///     cv.wait(&mut g);
    /// }
    ///
    /// assert!(t.stop().is_ok());
    ///
    /// # Ok::<(), Error>(())
    /// ```
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory allocation and
    /// waiting for the completion, therefore do not call this in atomic contexts (i.e.
    /// preemption-off contexts).
    pub fn try_run<F>(name: &CStr, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result,
        F: Send + 'static,
    {
        let t = Self::try_new(name, f)?;

        t.wake_up();

        Ok(t)
    }

    /// Stops the thread.
    ///
    /// - If the thread hasn't been waken up after creation, the thread closure won't be called, and
    ///   will return `-EINTR`. Note that a thread may not be waken up even after
    ///   [`Thread::wake_up`] is called.
    ///
    /// - Otherwise, waits for the closure to return or the thread `do_exit` itself.
    ///
    /// Consumes the [`Thread`]. In case of error, returns the exit code of the thread.
    ///
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    pub fn stop(self) -> Result {
        let result = self.raw.stop();

        if let Err(e) = result {
            if e.to_errno() == -(bindings::EINTR as i32) {
                (self.drop_arg)(self.arg_ptr);
            }
            return Err(e);
        }
        result
    }
}
