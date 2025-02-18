// SPDX-License-Identifier: GPL-2.0
//! A simple self test for the rust per-CPU API.

use core::ffi::c_void;

use kernel::{
    bindings::on_each_cpu, bindings::smp_processor_id, define_per_cpu, percpu::cpu_guard::*,
    percpu::*, pr_info, prelude::*, unsafe_get_per_cpu_ref,
};

module! {
    type: PerCpuTestModule,
    name: "percpu_test_rust",
    author: "Mitchell Levy",
    description: "Test code to exercise the Rust Per CPU variable API",
    license: "GPL v2",
}

struct PerCpuTestModule;

define_per_cpu!(PERCPU: i64 = 0);
define_per_cpu!(UPERCPU: u64 = 0);

impl kernel::Module for PerCpuTestModule {
    fn init(_module: &'static ThisModule) -> Result<Self, Error> {
        pr_info!("rust percpu test start\n");

        let mut native: i64 = 0;
        let mut pcpu: PerCpuRef<'static, i64> =
            unsafe { unsafe_get_per_cpu_ref!(PERCPU, CpuGuard::new()) };
        pr_info!("The contents of pcpu are {}", *pcpu);

        native += -1;
        *pcpu += -1;
        pr_info!("Native: {}, *pcpu: {}\n", native, *pcpu);
        assert!(native == *pcpu && native == -1);

        native += 1;
        *pcpu += 1;
        pr_info!("Native: {}, *pcpu: {}\n", native, *pcpu);
        assert!(native == *pcpu && native == 0);

        let mut unative: u64 = 0;
        let mut upcpu: PerCpuRef<'static, u64> =
            unsafe { unsafe_get_per_cpu_ref!(UPERCPU, CpuGuard::new()) };

        unative += 1;
        *upcpu += 1;
        pr_info!("Unative: {}, *upcpu: {}\n", unative, *upcpu);
        assert!(unative == *upcpu && unative == 1);

        unative = unative.wrapping_add((-1i64) as u64);
        *upcpu = upcpu.wrapping_add((-1i64) as u64);
        pr_info!("Unative: {}, *upcpu: {}\n", unative, *upcpu);
        assert!(unative == *upcpu && unative == 0);

        unative = unative.wrapping_add((-1i64) as u64);
        *upcpu = upcpu.wrapping_add((-1i64) as u64);
        pr_info!("Unative: {}, *upcpu: {}\n", unative, *upcpu);
        assert!(unative == *upcpu && unative == (-1i64) as u64);

        unative = 0;
        *upcpu = 0;

        unative = unative.wrapping_sub(1);
        *upcpu = upcpu.wrapping_sub(1);
        pr_info!("Unative: {}, *upcpu: {}\n", unative, *upcpu);
        assert!(unative == *upcpu && unative == (-1i64) as u64);
        assert!(unative == *upcpu && unative == u64::MAX);

        pr_info!("rust static percpu test done\n");

        pr_info!("rust dynamic percpu test start\n");
        let mut test: PerCpu<u32> = PerCpu::new().unwrap();
        *test.get(CpuGuard::new()) = 0;

        unsafe {
            on_each_cpu(Some(inc_percpu), (&raw mut test) as *mut c_void, 0);
            on_each_cpu(Some(inc_percpu), (&raw mut test) as *mut c_void, 0);
            on_each_cpu(Some(inc_percpu), (&raw mut test) as *mut c_void, 0);
            on_each_cpu(Some(inc_percpu), (&raw mut test) as *mut c_void, 1);
            on_each_cpu(Some(check_percpu), (&raw mut test) as *mut c_void, 1);
        }

        pr_info!("rust dynamic percpu test done\n");

        // Return Err to unload the module
        Result::Err(EINVAL)
    }
}

unsafe extern "C" fn inc_percpu(info: *mut c_void) {
    // SAFETY: We know that info is a vaoid *const PerCpu<u32> and PerCpu<u32> is Send.
    let mut pcpu = unsafe { (&*(info as *const PerCpu<u32>)).clone() };
    // SAFETY: smp_processor_id has no preconditions
    pr_info!("Incrementing on {}\n", unsafe { smp_processor_id() });

    *pcpu.get(CpuGuard::new()) += 1;
}

unsafe extern "C" fn check_percpu(info: *mut c_void) {
    // SAFETY: We know that info is a vaoid *const PerCpu<u32> and PerCpu<u32> is Send.
    let mut pcpu = unsafe { (&*(info as *const PerCpu<u32>)).clone() };
    // SAFETY: smp_processor_id has no preconditions
    pr_info!("Asserting on {}\n", unsafe { smp_processor_id() });

    assert!(*pcpu.get(CpuGuard::new()) == 4);
}
