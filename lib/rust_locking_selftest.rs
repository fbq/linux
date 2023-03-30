// SPDX-License-Identifier: GPL-2.0

//! Selftests for Rust locking APIs.

use kernel::pr_cont;
use kernel::prelude::*;
const __LOG_PREFIX: &[u8] = b"locking selftest\0";

extern "C" {
    fn dotest(
        testcase_fn: extern "C" fn(),
        expected: core::ffi::c_int,
        lockclass_mask: core::ffi::c_int,
    );
}

/// Same as the definition in lib/locking-selftest.c
#[allow(dead_code)]
enum Expectation {
    Failure = 0,
    Success = 1,
    Timeout = 2,
}

trait LockTest {
    const EXPECTED: Expectation;
    const MASK: i32;

    fn test();
}

extern "C" fn bridge<T: LockTest>() {
    T::test();
}

fn test<T: LockTest>() {
    pr_cont!("\n");
    pr_cont!("{}: ", core::any::type_name::<T>());
    unsafe {
        dotest(bridge::<T>, T::EXPECTED as core::ffi::c_int, T::MASK);
    }
    pr_cont!("\n");
}

struct SpinLockAATest;

impl LockTest for SpinLockAATest {
    const EXPECTED: Expectation = Expectation::Failure;
    const MASK: i32 = 0x100; // TODO

    fn test() {
        use kernel::static_lock_class;
        use kernel::sync::SpinLock;
        use kernel::{c_str, stack_pin_init};

        let key = static_lock_class!();
        let name = c_str!("A1");

        stack_pin_init!(
            let a1 = SpinLock::new(0, name, key)
        );

        stack_pin_init!(
            let a2 = SpinLock::new(0, name, key)
        );

        let _x = a1.lock();
        let _y = a2.lock();
    }
}

struct MutexAATest;

impl LockTest for MutexAATest {
    const EXPECTED: Expectation = Expectation::Failure;
    const MASK: i32 = 0x100; // TODO

    fn test() {
        use kernel::static_lock_class;
        use kernel::sync::Mutex;
        use kernel::{c_str, stack_pin_init};

        let key = static_lock_class!();
        let name = c_str!("A1");

        stack_pin_init!(
            let a1 = Mutex::new(0, name, key)
        );

        stack_pin_init!(
            let a2 = Mutex::new(0, name, key)
        );

        let _x = a1.lock();
        let _y = a2.lock();
    }
}

/// Entry point for tests.
#[no_mangle]
pub extern "C" fn rust_locking_test() {
    pr_info!("Selftests for Rust locking APIs");
    test::<SpinLockAATest>();
    test::<MutexAATest>();
}
