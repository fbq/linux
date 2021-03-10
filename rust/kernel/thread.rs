// SPDX-License-Identifier: GPL-2.0

use crate::bindings;
use crate::c_types;

use alloc::boxed::Box;
use core::ops::FnOnce;

#[no_mangle]
unsafe extern "C" fn rust_thread_func(data: *mut c_types::c_void) -> c_types::c_int {
    Box::from_raw(data as *mut Box<dyn FnOnce()>)();
    0
}

pub struct Thread {
    task: *mut bindings::task_struct,
}

impl Thread {
    pub fn new<F>(f: F, name: &str) -> Self
    where
        F: FnOnce(),
        F: Send + 'static,
    {
        let bf: Box<dyn FnOnce() + 'static> = Box::new(f);

        unsafe {
            let task = bindings::kthread_create_on_node(
                Some(rust_thread_func),
                Box::into_raw(Box::new(bf)) as *mut _,
                bindings::NUMA_NO_NODE,
                "%s".as_ptr() as *const c_types::c_char,
                name.as_ptr(),
            );
            Thread { task: task }
        }
    }

    pub fn wake_up(&self) {
        unsafe {
            bindings::wake_up_process(self.task);
        }
    }
}
