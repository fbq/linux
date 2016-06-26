/*
 * Primitives for checking the vcpu preemption from the guest.
 */

static long __vcpu_preempt_count(void)
{
	return 0;
}

static bool __vcpu_has_preempted(long vpc)
{
	return false;
}

static bool __vcpu_is_preempted(int cpu)
{
	return false;
}

struct vcpu_preempt_ops {
	/*
	 * Get the current vcpu's "preempt count", which is going to use for
	 * checking whether the current vcpu has ever been preempted
	 */
	long (*preempt_count)(void);

	/*
	 * Return whether a vcpu is preempted
	 */
	bool (*is_preempted)(int cpu);

	/*
	 * Given a "vcpu preempt count", Return whether a vcpu preemption ever
	 * happened after the .preempt_count() was called.
	 */
	bool (*has_preempted)(long vpc);
};

extern struct vcpu_preempt_ops vcpu_preempt_ops;

/* Default boilerplate */
#define DEFAULT_VCPU_PREEMPT_OPS			\
	{						\
		.preempt_count = __vcpu_preempt_count,	\
		.is_preempted = __vcpu_is_preempted,	\
		.has_preempted = __vcpu_has_preempted	\
	}

#ifdef CONFIG_HAS_VCPU_PREEMPTION_DETECTION
/*
 * vcpu_preempt_count: Get the current cpu's "vcpu preempt count"(vpc).
 *
 * The vpc is used for checking whether the current vcpu has ever been
 * preempted via vcpu_has_preempted().
 *
 * This function and vcpu_has_preepmted() should be called in the same
 * preemption disabled critical section.
 */
#define vcpu_preempt_count()	vcpu_preempt_ops.preempt_count()

/*
 * vcpu_is_preempted: Check whether @cpu's vcpu is preempted.
 */
#define vcpu_is_preempted(cpu)	vcpu_preempt_ops.is_preempted(cpu)

/*
 * vcpu_has_preepmted: Check whether the current cpu's vcpu has ever been
 * preempted.
 *
 * The checked duration is between the vcpu_preempt_count() which returns @vpc
 * is called and this function called.
 *
 * This function and corresponding vcpu_preempt_count() should be in the same
 * preemption disabled cirtial section.
 */
#define vcpu_has_preempted(vpc)	vcpu_preempt_ops.has_preempted(vpc)

#else /* CONFIG_HAS_VCPU_PREEMPTION_DETECTION */
#define vcpu_preempt_count() __vcpu_preempt_count()
#define vcpu_is_preempted(cpu) __vcpu_is_preempted(cpu)
#define vcpu_has_preempted(vpc) __vcpu_has_preempted(vpc)
#endif /* CONFIG_HAS_VCPU_PREEPMTION_DETECTION */
