#include <linux/list.h>
#include <linux/spinlock.h>
#include <linux/rbtree.h>

typedef void* hazptr_t;

#define HAZPTR_SLOT_PER_CTX 8

struct hazptr_slot_snap {
	struct rb_node node;
	unsigned long slot;
};

struct hazptr_context {
	// The lock of the percpu context lists.
	spinlock_t *lock;

	struct list_head list;
	struct hazptr_slot_snap snaps[HAZPTR_SLOT_PER_CTX];
	____cacheline_aligned unsigned long slots[HAZPTR_SLOT_PER_CTX];
};

void init_hazptr_context(struct hazptr_context *hzcp);
void cleanup_hazptr_context(struct hazptr_context *hzcp);
hazptr_t *hazptr_alloc(struct hazptr_context *hzcp);
void hazptr_free(struct hazptr_context *hzcp, hazptr_t *hzp);

#define hazptr_tryprotect(hzp, gp, field)	(typeof(gp))__hazptr_tryprotect(hzp, (void **)&(gp), offsetof(typeof(*gp), field))
#define hazptr_protect(hzp, gp, field) ({				\
	typeof(gp) ___p;						\
									\
	___p = hazptr_tryprotect(hzp, gp, field);			\
	BUG_ON(!___p);							\
	___p;								\
})

static inline void *__hazptr_tryprotect(hazptr_t *hzp,
					void *const *p,
					unsigned long head_offset)
{
	void *ptr;
	struct callback_head *head;

	ptr = READ_ONCE(*p);

	if (ptr == NULL)
		return NULL;

	head = (struct callback_head *)(ptr + head_offset);

	WRITE_ONCE(*hzp, head);
	smp_mb();

	ptr = READ_ONCE(*p); // read again

	if (ptr + head_offset != head) { // pointer changed
		WRITE_ONCE(*hzp, NULL);  // reset hazard pointer
		return NULL;
	} else
		return ptr;
}

static inline void hazptr_clear(hazptr_t *hzp)
{
	/* Pairs with smp_load_acquire() in reader scan. */
	smp_store_release(hzp, NULL);
}

void call_hazptr(struct callback_head *head, rcu_callback_t func);
