#include <linux/percpu.h>
#include <linux/smp.h>

// TODO: Profile whether or not this extra function call (needing to call the
// helper to end up eventually calling the underlying pcpu_alloc_noprof) has a
// significant performance burden. Hopefully we can instead not have to peek
// too far into the pcpu internals.
void __percpu *rust_helper_alloc_percpu(size_t sz, size_t align) {
	return __alloc_percpu(sz, align);
}

void rust_helper_on_each_cpu(smp_call_func_t func, void *info, int wait) {
	on_each_cpu(func, info, wait);
}

int rust_helper_smp_processor_id(void) {
	return smp_processor_id();
}

