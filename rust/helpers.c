// SPDX-License-Identifier: GPL-2.0
/*
 * Non-trivial C macros cannot be used in Rust. Similarly, inlined C functions
 * cannot be called either. This file explicitly creates functions ("helpers")
 * that wrap those so that they can be called from Rust.
 *
 * Even though Rust kernel modules should never use directly the bindings, some
 * of these helpers need to be exported because Rust generics and inlined
 * functions may not get their code generated in the crate where they are
 * defined. Other helpers, called from non-inline functions, may not be
 * exported, in principle. However, in general, the Rust compiler does not
 * guarantee codegen will be performed for a non-inline function either.
 * Therefore, this file exports all the helpers. In the future, this may be
 * revisited to reduce the number of exports after the compiler is informed
 * about the places codegen is required.
 *
 * All symbols are exported as GPL-only to guarantee no GPL-only feature is
 * accidentally exposed.
 *
 * Sorted alphabetically.
 */

#include <kunit/test-bug.h>
#include <linux/bug.h>
#include <linux/build_bug.h>
#include <linux/cred.h>
#include <linux/err.h>
#include <linux/errname.h>
#include <linux/fs.h>
#include <linux/mutex.h>
#include <linux/refcount.h>
#include <linux/sched/signal.h>
#include <linux/security.h>
#include <linux/spinlock.h>
#include <linux/task_work.h>
#include <linux/wait.h>
#include <linux/workqueue.h>

__noreturn void rust_helper_BUG(void)
{
	BUG();
}

void rust_helper_mutex_lock(struct mutex *lock)
{
	mutex_lock(lock);
}

void rust_helper___spin_lock_init(spinlock_t *lock, const char *name,
				  struct lock_class_key *key)
{
#ifdef CONFIG_DEBUG_SPINLOCK
	__raw_spin_lock_init(spinlock_check(lock), name, key, LD_WAIT_CONFIG);
#else
	spin_lock_init(lock);
#endif
}

void rust_helper_spin_lock(spinlock_t *lock)
{
	spin_lock(lock);
}

void rust_helper_spin_unlock(spinlock_t *lock)
{
	spin_unlock(lock);
}

void rust_helper_init_wait(struct wait_queue_entry *wq_entry)
{
	init_wait(wq_entry);
}

int rust_helper_signal_pending(struct task_struct *t)
{
	return signal_pending(t);
}

refcount_t rust_helper_REFCOUNT_INIT(int n)
{
	return (refcount_t)REFCOUNT_INIT(n);
}

void rust_helper_refcount_inc(refcount_t *r)
{
	refcount_inc(r);
}

bool rust_helper_refcount_dec_and_test(refcount_t *r)
{
	return refcount_dec_and_test(r);
}

__force void *rust_helper_ERR_PTR(long err)
{
	return ERR_PTR(err);
}

bool rust_helper_IS_ERR(__force const void *ptr)
{
	return IS_ERR(ptr);
}

long rust_helper_PTR_ERR(__force const void *ptr)
{
	return PTR_ERR(ptr);
}

const char *rust_helper_errname(int err)
{
	return errname(err);
}

extern inline struct task_struct *rust_helper_get_current(void)
{
	return current;
}

void rust_helper_get_task_struct(struct task_struct *t)
{
	get_task_struct(t);
}

void rust_helper_put_task_struct(struct task_struct *t)
{
	put_task_struct(t);
}

kuid_t rust_helper_task_uid(struct task_struct *task)
{
	return task_uid(task);
}

kuid_t rust_helper_task_euid(struct task_struct *task)
{
	return task_euid(task);
}

#ifndef CONFIG_USER_NS
uid_t rust_helper_from_kuid(struct user_namespace *to, kuid_t uid)
{
	return from_kuid(to, uid);
}
#endif /* CONFIG_USER_NS */

bool rust_helper_uid_eq(kuid_t left, kuid_t right)
{
	return uid_eq(left, right);
}

kuid_t rust_helper_current_euid(void)
{
	return current_euid();
}

struct user_namespace *rust_helper_current_user_ns(void)
{
	return current_user_ns();
}

pid_t rust_helper_task_tgid_nr_ns(struct task_struct *tsk,
				  struct pid_namespace *ns)
{
	return task_tgid_nr_ns(tsk, ns);
}

struct kunit *rust_helper_kunit_get_current_test(void)
{
	return kunit_get_current_test();
}

void rust_helper_init_work_with_key(struct work_struct *work, work_func_t func,
				    bool onstack, const char *name,
				    struct lock_class_key *key)
{
	__init_work(work, onstack);
	work->data = (atomic_long_t)WORK_DATA_INIT();
	lockdep_init_map(&work->lockdep_map, name, key, 0);
	INIT_LIST_HEAD(&work->entry);
	work->func = func;
}

struct file *rust_helper_get_file(struct file *f)
{
	return get_file(f);
}

const struct cred *rust_helper_get_cred(const struct cred *cred)
{
	return get_cred(cred);
}

void rust_helper_put_cred(const struct cred *cred)
{
	put_cred(cred);
}

#ifndef CONFIG_SECURITY
void rust_helper_security_cred_getsecid(const struct cred *c, u32 *secid)
{
	security_cred_getsecid(c, secid);
}

int rust_helper_security_secid_to_secctx(u32 secid, char **secdata, u32 *seclen)
{
	return security_secid_to_secctx(secid, secdata, seclen);
}

void rust_helper_security_release_secctx(char *secdata, u32 seclen)
{
	security_release_secctx(secdata, seclen);
}
#endif

void rust_helper_init_task_work(struct callback_head *twork,
				task_work_func_t func)
{
	init_task_work(twork, func);
}

/*
 * `bindgen` binds the C `size_t` type as the Rust `usize` type, so we can
 * use it in contexts where Rust expects a `usize` like slice (array) indices.
 * `usize` is defined to be the same as C's `uintptr_t` type (can hold any
 * pointer) but not necessarily the same as `size_t` (can hold the size of any
 * single object). Most modern platforms use the same concrete integer type for
 * both of them, but in case we find ourselves on a platform where
 * that's not true, fail early instead of risking ABI or
 * integer-overflow issues.
 *
 * If your platform fails this assertion, it means that you are in
 * danger of integer-overflow bugs (even if you attempt to add
 * `--no-size_t-is-usize`). It may be easiest to change the kernel ABI on
 * your platform such that `size_t` matches `uintptr_t` (i.e., to increase
 * `size_t`, because `uintptr_t` has to be at least as big as `size_t`).
 */
static_assert(
	sizeof(size_t) == sizeof(uintptr_t) &&
	__alignof__(size_t) == __alignof__(uintptr_t),
	"Rust code expects C `size_t` to match Rust `usize`"
);
