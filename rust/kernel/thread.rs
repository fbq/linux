// SPDX-License-Identifier: GPL-2.0

//! A kernel thread (kthread).
//!
//! This module allows Rust code to create/stop a kernel thread.

use crate::error::{from_err_ptr, to_result, Result};
use crate::str::CStr;
use crate::task::Task;
use crate::types::ARef;
use crate::{bindings, c_str};

use alloc::boxed::Box;
use core::ops::{Deref, FnOnce};

/// Raw kernel thread references.
///
/// The threads are created via C-style functions and machine-word sized
/// arguments. The reference represents the capability to stop the
/// corresponding thread.
///
/// # Safety
///
/// The creation of [`RawThreadRef`] is unsafe because if a caller provides
/// an incorrect thread function or an incorrect thread argument, the
/// new thread will corrupt memory or do other unsafe behaviors.
struct RawThreadRef {
    task: ARef<Task>,
}

impl RawThreadRef {
    /// Creates a new thread using a C-style function pointer.
    ///
    /// # Safety
    ///
    /// This function actually doesn't dereference `arg` or call `f`, so even if
    /// the users pass incorrect parameters this function won't run into
    /// trouble. But if the users provide incorrect `arg` or `f` the new thread
    /// will corrupt memory or invoke undefined behaviors, so make it `unsafe`.
    ///
    /// The safety requirements of calling this function are:
    ///
    /// - Make sure `arg` is a proper pointer that points to a valid memory
    ///   location when the new thread begins to run.
    ///
    /// - Make sure `f` is a proper function pointer and `f` handles `arg`
    ///   correctly.
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory
    /// allocation and waiting for the completion, therefore do not call this
    /// in atomic contexts (i.e. preemption-off contexts).
    unsafe fn try_new(
        name: &CStr,
        f: unsafe extern "C" fn(*mut core::ffi::c_void) -> core::ffi::c_int,
        arg: *mut core::ffi::c_void,
    ) -> Result<Self> {
        // SAFETY: `kthread_create_on_node` will copy the content of `name`, so
        // we don't need to make the `name` live longer.
        let task_ptr = from_err_ptr(unsafe {
            bindings::kthread_create_on_node(
                Some(f),
                arg,
                bindings::NUMA_NO_NODE,
                c_str!("%s").as_ptr() as _,
                name.as_ptr(),
            )
        })?;

        // SAFETY: `task_ptr` is a valid pointer for a `task_struct` because
        // we've checked with `from_err_ptr` above.
        //
        // The refcount of `task` has been increased during `into()`, see the
        // `ARef::from(&T)` for more information.
        let task = unsafe { (&*task_ptr.cast::<Task>()).into() };

        // Increases the refcount of the task, so that it won't go away if it
        // `do_exit`.
        Ok(RawThreadRef { task })
    }

    /// Stops the thread.
    ///
    /// - If the thread function hasn't been called after creation, this
    /// function will return [`Error::-EINTR`] and the thread function will
    /// never be called.
    ///
    /// - Otherwise, waits for the thread function to return or the thread
    /// `do_exit` itself.
    ///
    /// Consumes the [`RawThreadRef`] so that it's not accessible and return the
    /// exit code of the thread.
    /// # Context
    ///
    /// This function might sleep, don't call it in atomic contexts.
    fn stop(self) -> Result {
        // SAFETY: `self.task.0.get()` is a valid pointer to a kernel thread
        // structure, the refcount of which is increased in
        // `[RawThread::try_new`], so it won't point to a freed `task_struct`.
        // And it's not stopped because `stop` will consume the [`RawThreadRef`].
        to_result(unsafe { bindings::kthread_stop(self.task.0.get()) })
    }
}

/// Bridge function of type `F` from Rust ABI to C.
extern "C" fn bridge<F>(data: *mut core::ffi::c_void) -> i32
where
    F: FnOnce() -> Result,
{
    // SAFETY: `data` is the result of [`Box::into_raw`], therefore it's safe to
    // [`Box::from_raw`] here.
    let f = unsafe { Box::from_raw(data as *mut F) };

    match f() {
        Ok(_) => 0,
        Err(e) => {
            // Changes the return value if it's `-ENITR`, in other words, we
            // don't allow a thread function to return `-EINTR`.
            //
            // Rationale: the kernel uses `-EINTR` to indicate that the kernel
            // thread gets stopped before it's able to run (the exit code is
            // set at C side via a special call to `do_exit`). In that case,
            // there is no new thread to own the thread argument, therefore the
            // `stop` functions need to recycle the thread argument. If we allow
            // thread function to return `-EINTR`, [`ThreadRef::stop`] will receive
            // it as the exit code, and we're unable to differ these two cases:
            // 1) stopped before run and 2) returning `-ENITR` from thread
            // function.
            //
            // Note that currently in kernel, no one actually calls `do_exit`
            // with `-EINTR` or returns `-EINTR` from thread function other
            // than the special case mentioned above.
            if e.to_errno() == -(bindings::EINTR as i32) {
                -(bindings::EINVAL as i32)
            } else {
                e.to_errno()
            }
        }
    }
}

/// A kernel thread reference.
///
/// A thread reference provides ways to operate the corresponding kthreads:
/// gets the reference to the [`Task`], stops the corresponding kthread, etc.
pub struct ThreadRef {
    /// Raw kernel thread reference.
    raw: RawThreadRef,

    /// Pointer to the thread argument.
    arg_ptr: *const core::ffi::c_void,

    /// Drop function to recycle arg
    drop_arg: fn(*const core::ffi::c_void),
}

impl ThreadRef {
    /// Creates a new thread.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use kernel::prelude::*;
    /// use kernel::{c_str, thread::ThreadRef};
    ///
    /// fn test() -> Result {
    ///     let boxed = Box::try_new(42)?;
    ///
    ///     let t = ThreadRef::try_new(c_str!("rust-thread"), move || {
    ///         pr_info!("boxed is {}", boxed);
    ///         Ok(())
    ///     })?;
    ///
    ///     t.wake_up();
    ///
    ///     Ok(())
    /// }
    /// ```
    ///
    /// # Context
    ///
    /// This function might sleep in `kthread_create_on_node` due to the memory
    /// allocation and waiting for the completion, therefore do not call this
    /// in atomic contexts (i.e. preemption-off contexts).
    pub fn try_new<F>(name: &CStr, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result,
        F: Send + 'static,
    {
        // Allocate closure here, because this function may return before
        // the bridged function (the function that uses the closure) get executed.
        let boxed_fn = Box::try_new(f)?;
        let data = Box::into_raw(boxed_fn);

        // SAFETY: `bridge::<F>` is a proper function pointer to a C function,
        // and [`Box::from_raw`] will be used in it to consume the raw pointer
        // in the new thread.
        let result = unsafe { RawThreadRef::try_new(name, bridge::<F>, data as _) };

        if result.is_err() {
            // Creation fails, we need to consume the raw pointer `data` because
            // there is no new thread to own the underlying object, we should
            // let the current thread own it.
            //
            // SAFETY: We [`Box::from_raw`] back what we just [`Box::into_raw`],
            // and since the new thread is not created, so no one touches
            // `data`.
            unsafe {
                drop(Box::from_raw(data));
            }
        }

        result.map(|raw| ThreadRef {
            raw,
            arg_ptr: data as _,
            drop_arg: |ptr: *const core::ffi::c_void| {
                // SAFETY: `ptr` is what we [`Box::into_raw`] and store at
                // [`Thread::arg_ptr`], and `drop_arg` only get called if
                // the thread hasn't run, which means no one [`Box::from_raw`]
                // the `ptr`, and that means we can safely do it.
                unsafe {
                    drop(Box::from_raw(ptr as *mut F));
                }
            },
        })
    }

    /// Stops the thread.
    ///
    /// - If the thread hasn't been waken up after creation, the thread closure
    ///   won't be called, and will return `-EINTR`. Note that a thread may not
    ///   be waken up even after [`Task::wake_up`] is called.
    ///
    /// - Otherwise, waits for the closure to return or the thread `do_exit`
    ///   itself.
    ///
    /// Consumes the [`ThreadRef`]. In case of error, returns the exit code of the
    /// thread.
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
        }

        result
    }
}

/// A kthread is a special [`Task`].
impl Deref for ThreadRef {
    type Target = Task;

    fn deref(&self) -> &Self::Target {
        self.raw.task.deref()
    }
}
