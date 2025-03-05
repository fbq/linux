// SPDX-License-Identifier: GPL-2.0
//! This module contains abstractions for creating and using per-CPU variables from Rust. In
//! particular, see the define_per_cpu! and unsafe_get_per_cpu_ref! macros.
pub mod cpu_guard;
// pub mod ref_count;

use bindings::{alloc_percpu, free_percpu};

use crate::percpu::cpu_guard::CpuGuard;
use crate::prelude::*;
use crate::sync::Arc;
use crate::unsafe_get_per_cpu_ref;

use core::arch::asm;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use ffi::c_void;

/// Holds a dynamically allocated per-CPU variable.
pub struct PerCpu<T> {
    alloc: Arc<PerCpuAllocation<T>>,
}

/// Represents an allocation of a per-CPU variable via alloc_percpu. Calls free_percpu when
/// dropped.
struct PerCpuAllocation<T> {
    pub offset: usize,
    pub deref_type: PhantomData<T>,
}

/// A PerCpuRef is obtained by the unsafe_get_per_cpu_ref! macro used on a StaticPerCpuSymbol
/// defined via the define_per_cpu! macro.
///
/// This type will transparently deref(mut) into a &(mut) T referencing this CPU's instance of the
/// underlying variable.
pub struct PerCpuRef<'a, T> {
    offset: usize,
    deref_type: PhantomData<&'a T>,
    _guard: CpuGuard,
}

/// A wrapper used for declaring static per-CPU variables. These symbols are "virtual" in that the
/// linker uses them to generate offsets into each cpu's per-cpu area, but shouldn't be read
/// from/written to directly. The fact that the statics are immutable prevents them being written
/// to (generally), this struct having _val be non-public prevents reading from them.
///
/// The end-user of the per-CPU API should make use of the define_per_cpu! macro instead of
/// declaring variables of this type directly.
#[repr(transparent)]
pub struct StaticPerCpuSymbol<T> {
    _val: T, // generate a correctly sized type
}

impl<T> PerCpu<T> {
    /// Allocate a new per-CPU variable
    pub fn new() -> Option<Self> {
        // TODO is this right? (e.g., do we need to see if the alloc should be atomic?)
        // SAFETY: No preconditions to call alloc_percpu
        let ptr: *mut c_void = unsafe { alloc_percpu(size_of::<T>(), align_of::<T>()) };
        if ptr.is_null() {
            return None;
        }

        // TODO maybe not GFP_KERNEL?
        let alloc = Arc::new(
            PerCpuAllocation {
                offset: ptr as usize,
                deref_type: PhantomData,
            },
            GFP_KERNEL,
        );
        if alloc.is_err() {
            return None;
        }

        Some(Self {
            alloc: alloc.unwrap(),
        })
    }

    /// Gets a PerCpuRef referring to the underlying per-CPU variable.
    pub fn get<'a>(&'a mut self, guard: CpuGuard) -> PerCpuRef<'a, T> {
        // SAFETY: self.offset was returned by alloc_percpu, and so was a valid pointer into the
        // percpu area, and has remained valid by the invariants of PerCpu<T>.
        unsafe { PerCpuRef::new::<'a>(self.alloc.offset, guard) }
    }

    /// Creates a new PerCpu<T> pointing to the same underlying variable
    ///
    /// # Safety
    /// The returned PerCpu<T> must be immediately moved to another thread without its `get`
    /// method being called on the current thread. No thread may have more than one PerCpu<T>
    /// pointing at the same underlying per-CPU variable.
    pub unsafe fn clone(&self) -> Self {
        Self {
            alloc: self.alloc.clone(),
        }
    }
}

/// TODO
pub trait PerCpuCallback<T: Sized> {
    /// # Safety
    ///
    /// TODO
    unsafe extern "C" fn percpu_fn(ptr: *mut c_void) {
        let pcpu = unsafe { (&*(ptr as *const PerCpu<T>)).clone() };
        Self::callback(pcpu);
    }

    /// TODO
    fn callback(pcpu: PerCpu<T>);
}

/// TODO
///
/// # Examples
///
/// ```
/// use kernel::prelude::*;
/// use kernel::percpu::{cpu_guard::CpuGuard, PerCpu, PerCpuCallback, on_each_cpu};
///
/// struct IncPerCpu;
///
/// impl PerCpuCallback<i32> for IncPerCpu {
///     fn callback(mut pcpu: PerCpu<i32>) {
///         unsafe {
///             *pcpu.get(CpuGuard::new()) += 1;
///         }
///     }
/// }
/// let mut test = PerCpu::new().ok_or(ENOMEM)?;
///
/// // let my_ref = unsafe { test.get(CpuGuard::new()) };
/// // build error if uncomment above and comment below.
///
/// on_each_cpu::<_, IncPerCpu>(&test);
///
/// let my_ref = unsafe { test.get(CpuGuard::new()) };
///
/// // each CPU has been increased by 1;
/// assert_eq!(*my_ref, 1);
/// # Ok::<(), Error>(())
/// ```
pub fn on_each_cpu<T, C: PerCpuCallback<T>>(pcpu: &PerCpu<T>) {
    // TODO
    unsafe {
        bindings::on_each_cpu(Some(C::percpu_fn), pcpu as *const _ as *mut c_void, 1);
    }
}

impl<T> Drop for PerCpuAllocation<T> {
    fn drop(&mut self) {
        // SAFETY: self.offset was returned by alloc_percpu, and so was a valid pointer into the
        // percpu area, and has remained valid by the invariants of PerCpu<T>.
        unsafe { free_percpu(self.offset as *mut c_void) }
    }
}

impl<'a, T> PerCpuRef<'a, T> {
    /// You should be using the unsafe_get_per_cpu! macro (if accessing a static percpu) or
    /// PerCpu::get (if accessing a dynamic percpu) instead
    ///
    /// 'b is the lifetime of the returned PerCpuRef, and should correspond to the lifetime of the
    /// borrowed PerCpu<T> (if dynamically allocated) or 'static (if statically allocated).
    ///
    /// # Safety
    /// offset must be a valid offset into the per cpu area
    pub unsafe fn new<'b>(offset: usize, guard: CpuGuard) -> PerCpuRef<'b, T> {
        PerCpuRef {
            offset,
            deref_type: PhantomData,
            _guard: guard,
        }
    }

    /// Computes this_cpu_ptr as a usize, ignoring issues of ownership and borrowing
    fn this_cpu_ptr_usize(&self) -> usize {
        // SAFETY: this_cpu_off is read only as soon as the per-CPU subsystem is initialized
        let off: PerCpuRef<'static, u64> =
            unsafe { unsafe_get_per_cpu_ref!(this_cpu_off, CpuGuard::new()) };
        let mut this_cpu_area: *mut c_void;
        // SAFETY: gs + off_val is guaranteed to be a valid pointer by the per-CPU subsystem and
        // the invariants guaranteed by PerCpuRef (i.e., off.offset is valid)
        unsafe {
            asm!(
                // For some reason, the asm! parser doesn't like
                //     mov {out}, [gs:{off_val}]
                // so we use the less intuitive prefix version instead
                "gs mov {out}, [{off_val}]",
                off_val = in(reg) off.offset,
                out = out(reg) this_cpu_area,
            )
        };
        // SAFETY: this_cpu_area + self.offset is guaranteed to be a valid pointer by the per-CPU
        // subsystem and the invariant that self.offset is a valid offset into the per-CPU area.
        unsafe { (this_cpu_area.add(self.offset)) as usize }
    }

    /// Returns a pointer to self's associated per-CPU variable. Logically equivalent to C's
    /// this_cpu_ptr
    pub fn this_cpu_ptr(&self) -> *const T {
        self.this_cpu_ptr_usize() as *const T
    }

    /// Returns a mut pointer to self's associated per-CPU variable. Logically equivalent to C's
    /// this_cpu_ptr
    pub fn this_cpu_ptr_mut(&mut self) -> *mut T {
        self.this_cpu_ptr_usize() as *mut T
    }
}

impl<'a, T> Deref for PerCpuRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &'a Self::Target {
        // SAFETY: By the contract of unsafe_get_per_cpu_ref!, we know that self is the only
        // PerCpuRef associated with the underlying per-CPU variable and that the underlying
        // variable is not mutated outside of rust.
        unsafe { &*(self.this_cpu_ptr()) }
    }
}

impl<'a, T> DerefMut for PerCpuRef<'a, T> {
    fn deref_mut(&mut self) -> &'a mut Self::Target {
        // SAFETY: By the contract of unsafe_get_per_cpu_ref!, we know that self is the only
        // PerCpuRef associated with the underlying per-CPU variable and that the underlying
        // variable is not mutated outside of rust.
        unsafe { &mut *(self.this_cpu_ptr_mut()) }
    }
}

/// define_per_cpu! is analogous to the C DEFINE_PER_CPU macro in that it lets you create a
/// statically allocated per-CPU variable.
///
/// # Example
/// ```
/// use kernel::define_per_cpu;
/// use kernel::percpu::StaticPerCpuSymbol;
///
/// define_per_cpu!(pub MY_PERCPU: u64 = 0);
/// ```
#[macro_export]
macro_rules! define_per_cpu {
    ($vis:vis $id:ident: $ty:ty = $expr:expr) => {
        $crate::macros::paste! {
            // Expand $expr outside of the unsafe block to avoid silently allowing unsafe code to be
            // used without a user-facing unsafe block
            static [<__INIT_ $id>]: $ty = $expr;

            // SAFETY: StaticPerCpuSymbol<T> is #[repr(transparent)], so we can freely convert from T
            #[link_section = ".data..percpu"]
            $vis static $id: StaticPerCpuSymbol<$ty> = unsafe {
                core::mem::transmute::<$ty, StaticPerCpuSymbol<$ty>>([<__INIT_ $id>])
            };
        }
    };
}

/// Goes from a StaticPerCpuSymbol to a usable PerCpuRef. $id is the identifier of the
/// StaticPerCpuSymbol and $guard is an expression that evaluates to a CpuGuard.
///
/// # Safety
/// Don't create two PerCpuRef that point at the same per-cpu variable, as this would allow you to
/// accidentally break aliasing rules. Unless T is Sync, the returned PerCpuRef should not be used
/// from interrupt contexts.
///
/// If $id is `extern "C"` (i.e., declared via declare_extern_per_cpu!) then the underlying per-CPU
/// variable must not be written from C code while a PerCpuRef exists in Rust. That is, the
/// underlying per-CPU variable must not be written in any IRQ context (unless the user ensures
/// IRQs are disabled) and no FFI calls can be made to C functions that may write the per-CPU
/// variable. The underlying StaticPerCpuSymbol created via declare_extern_per_cpu must also have
/// the correct type.
#[macro_export]
macro_rules! unsafe_get_per_cpu_ref {
    ($id:ident, $guard:expr) => {{
        let off = core::ptr::addr_of!($id);
        PerCpuRef::new::<'static>(off as usize, $guard)
    }};
}

/// Declares a StaticPerCpuSymbol corresponding to a per-CPU variable defined in C. Be sure to read
/// the safety requirements of unsafe_get_per_cpu_ref!.
#[macro_export]
macro_rules! declare_extern_per_cpu {
    ($id:ident: $ty:ty) => {
        extern "C" {
            static $id: StaticPerCpuSymbol<$ty>;
        }
    };
}

declare_extern_per_cpu!(this_cpu_off: u64);
