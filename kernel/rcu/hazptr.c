// SPDX-License-Identifier: GPL-2.0+

#include <linux/spinlock.h>
#include <linux/cleanup.h>
#include <linux/hazptr.h>
#include <linux/percpu.h>
#include <linux/workqueue.h>

#define HAZPTR_UNUSED (1ul)

struct hazptr_percpu {
	spinlock_t ctx_lock;
	struct list_head ctx_list;
	spinlock_t callback_lock;
	struct callback_head *queued;
	struct callback_head **tail;
};

DEFINE_PER_CPU(struct hazptr_percpu, hzpcpu);

struct hazptr_reader_tree {
	spinlock_t lock;
	struct rb_root root;
};

static void init_hazptr_reader_tree(struct hazptr_reader_tree *tree)
{
	spin_lock_init(&tree->lock);
	tree->root = RB_ROOT;
}

static bool is_null_or_unused(unsigned long slot)
{
	return slot == 0 || slot == HAZPTR_UNUSED;
}

static int hazptr_node_cmp(const void *key, const struct rb_node *curr)
{
	unsigned long slot = (unsigned long)key;
	struct hazptr_slot_snap *curr_snap = container_of(curr, struct hazptr_slot_snap, node);

	if (slot < curr_snap->slot)
		return -1;
	else if (slot > curr_snap->slot)
		return 1;
	else
		return 0;
}

static bool hazptr_node_less(struct rb_node *new, const struct rb_node *curr)
{
	struct hazptr_slot_snap *new_snap = container_of(new, struct hazptr_slot_snap, node);

	return hazptr_node_cmp((void *)new_snap->slot, curr) < 0;
}

// Add the snapshot into search tree. tree->lock must be held.
static inline void reader_add_locked(struct hazptr_reader_tree *tree,
				     struct hazptr_slot_snap *snap)
{
	lockdep_assert_held(&tree->lock);
	BUG_ON(is_null_or_unused(snap->slot));

	rb_add(&snap->node, &tree->root, hazptr_node_less);
}

static inline void reader_add(struct hazptr_reader_tree *tree,
			      struct hazptr_slot_snap *snap)
{
	guard(spinlock_irqsave)(&tree->lock);

	reader_add_locked(tree, snap);
}

// Delete the snapshot into search tree. tree->lock must be held.
static inline void reader_del_locked(struct hazptr_reader_tree *tree,
				     struct hazptr_slot_snap *snap)
{
	lockdep_assert_held(&tree->lock);

	rb_erase(&snap->node, &tree->root);
}

static inline void reader_del(struct hazptr_reader_tree *tree,
			      struct hazptr_slot_snap *snap)
{
	guard(spinlock_irqsave)(&tree->lock);

	reader_del_locked(tree, snap);
}

// Find whether a read exists. tree->lock must be held.
static inline bool reader_exist_locked(struct hazptr_reader_tree *tree,
				       unsigned long slot)
{
	lockdep_assert_held(&tree->lock);

	return !!rb_find((void *)slot, &tree->root, hazptr_node_cmp);
}

static inline bool reader_exist(struct hazptr_reader_tree *tree,
				unsigned long slot)
{
	guard(spinlock_irqsave)(&tree->lock);

	return reader_exist_locked(tree, slot);
}

// Scan the reader and update the global readers tree.
static void hazptr_context_snap_readers_locked(struct hazptr_reader_tree *tree,
					       struct hazptr_context *hzcp)
{
	lockdep_assert_held(hzcp->lock);

	for (int i = 0; i < HAZPTR_SLOT_PER_CTX; i++) {
		/*
		 * Pairs with smp_store_release() in hazptr_{clear,free}().
		 *
		 * Ensure
		 *
		 * <reader>		<updater>
		 *
		 * [access protected pointers]
		 * hazptr_clear();
		 *   smp_store_release()
		 *			// in reader scan.
		 *			smp_load_acquire(); // is null or unused.
		 *			[run callbacks] // all accesses from
		 *					// reader must be
		 *					//observed.
		 */
		unsigned long val = smp_load_acquire(&hzcp->slots[i]);

		if (!is_null_or_unused(val)) {
			struct hazptr_slot_snap *snap = &hzcp->snaps[i];

			// Already in the tree, need to remove first.
			if (!is_null_or_unused(snap->slot)) {
				reader_del(tree, snap);
				snap->slot = val;
				reader_add(tree, snap);
			}
		}
	}
}

void init_hazptr_context(struct hazptr_context *hzcp)
{
	struct hazptr_percpu *pcpu = this_cpu_ptr(&hzpcpu);

	for (int i = 0; i < HAZPTR_SLOT_PER_CTX; i++) {
		hzcp->slots[i] = HAZPTR_UNUSED;
		hzcp->snaps[i].slot = HAZPTR_UNUSED;
	}

	guard(spinlock_irqsave)(&pcpu->ctx_lock);
	list_add(&hzcp->list, &pcpu->ctx_list);
	hzcp->lock = &pcpu->ctx_lock;
}

struct hazptr_struct {
	struct work_struct work;
	bool scheduled;

	// list of callbacks, we move percpu queued callbacks into the global
	// queued list in workqueue function.
	spinlock_t callback_lock;
	struct callback_head *queued;
	struct callback_head **tail;

	struct hazptr_reader_tree readers;
};

static struct hazptr_struct hazptr_struct;

void cleanup_hazptr_context(struct hazptr_context *hzcp)
{
	if (hzcp->lock) {
		scoped_guard(spinlock_irqsave, hzcp->lock) {
			list_del(&hzcp->list);
			hzcp->lock = NULL;
		}

		for (int i = 0; i < HAZPTR_SLOT_PER_CTX; i++) {
			struct hazptr_slot_snap *snap = &hzcp->snaps[i];

			if (!is_null_or_unused(snap->slot))
				reader_del(&hazptr_struct.readers, snap);
		}
	}
}

hazptr_t *hazptr_alloc(struct hazptr_context *hzcp)
{
	unsigned long unused;

	for (int i = 0; i < HAZPTR_SLOT_PER_CTX; i++) {
		if (READ_ONCE(hzcp->slots[i]) == HAZPTR_UNUSED) {
			unused = HAZPTR_UNUSED;

			/*
			 * rwm-sequence is relied on here.
			 *
			 * This is needed since in case of a previous reader:
			 *
			 * <reader 1>		<reader 2>		<updater>
			 * [access protected potiners]
			 * hazptr_free():
			 *   smp_store_release(); // hzptr == UNUSED
			 *			hazptr_alloc():
			 *			  try_cmpxchg_relaxed(); // hzptr == NULL
			 *
			 *						// in reader scan
			 *						smp_load_acquire(); // is null
			 *						[run callbacks]
			 * Because of the rwm-sequence of release operations,
			 * when callbacks are run, accesses from reader 1 must
			 * be observed by updater.
			 */
			if (try_cmpxchg_relaxed(&hzcp->slots[i], &unused, (unsigned long)NULL)) {
				return (hazptr_t *)&hzcp->slots[i];
			}
		}
	}

	return NULL;
}

void hazptr_free(struct hazptr_context *hzcp, hazptr_t *hzptr)
{
	WARN_ON(((unsigned long)*hzptr) == HAZPTR_UNUSED);

	/* Pairs with smp_load_acquire() in reader scan */
	smp_store_release(hzptr, (void *)HAZPTR_UNUSED);
}

// Scan all possible readers, and update the global reader tree.
static void check_readers(struct hazptr_struct *hzst)
{
	int cpu;

	for_each_possible_cpu(cpu) {
		struct hazptr_percpu *pcpu = per_cpu_ptr(&hzpcpu, cpu);
		struct hazptr_context *ctx;

		guard(spinlock_irqsave)(&pcpu->ctx_lock);
		list_for_each_entry(ctx, &pcpu->ctx_list, list)
			hazptr_context_snap_readers_locked(&hzst->readers, ctx);
	}
}

// Call with hazptr_struct lock held.
static void kick_hazptr_work(void)
{
	if (hazptr_struct.scheduled)
		return;

	queue_work(system_wq, &hazptr_struct.work);
	hazptr_struct.scheduled = true;
}

/*
 * Check if which callbacks are ready to call.
 *
 * Return: a callback list that no reader is referencing the corresponding
 * objects.
 */
static struct callback_head *do_hazptr(struct hazptr_struct *hzst)
{
	struct callback_head *tmp, **curr;
	struct callback_head *todo = NULL, **todo_tail = &todo;

	// Currently, the lock is unnecessary, but maybe we will have multiple
	// work_structs sharing the same callback list in the future;
	guard(spinlock_irqsave)(&hzst->callback_lock);

	curr = &hzst->queued;

	while ((tmp = *curr)) {
		// No reader, we can free the object.
		if (!reader_exist(&hzst->readers, (unsigned long)tmp)) {
			// Add tmp into todo.
			*todo_tail = tmp;
			todo_tail = &tmp->next;

			// Delete the tmp and move to the next entry.
			*curr = tmp->next;
		} else
			curr = &tmp->next;
	}

	hzst->tail = curr;

	// Keep checking if callback list is not empty.
	if (hzst->queued)
		kick_hazptr_work();

	*todo_tail = NULL;

	return todo;
}

static void hazptr_work_func(struct work_struct *work)
{
	struct hazptr_struct *hzst = container_of(work, struct hazptr_struct, work);
	struct callback_head *todo;

	// Advance callbacks from hzpcpu to hzst
	scoped_guard(spinlock_irqsave, &hzst->callback_lock) {
		int cpu;

		hzst->scheduled = false;
		for_each_possible_cpu(cpu) {
			struct hazptr_percpu *pcpu = per_cpu_ptr(&hzpcpu, cpu);

			guard(spinlock)(&pcpu->callback_lock);

			if (pcpu->queued) {
				*(hzst->tail) = pcpu->queued;
				hzst->tail = pcpu->tail;
				pcpu->queued = NULL;
				pcpu->tail = &pcpu->queued;
			}
		}
	}

	// Pairs with the smp_mb() on the reader side. This guarantees that if
	// the hazptr work picked up the callback from an updater and the
	// updater set the global pointer to NULL before enqueue the callback,
	// the hazptr work must observe a reader that protects the hazptr before
	// the updater.
	//
	// <reader>		<updater>		<hazptr work>
	// ptr = READ_ONCE(gp);
	// WRITE_ONCE(*hazptr, ptr);
	// smp_mb(); // => ->strong-fence
	//			tofree = gp;
	// ptr = READ_ONCE(gp); // re-read, gp is not NULL
	//			// => ->fre
	//			WRITE_ONCE(gp, NULL);
	//			call_hazptr(gp, ...):
	//			  lock(->callback_lock);
	//			  [queued the callback]
	//			  unlock(->callback_lock);// => ->po-unlock-lock-po
	//						lock(->callback_lock);
	//						[move from hzpcpu to hzst]
	//
	//						smp_mb(); => ->strong-fence
	//						ptr = READ_ONCE(*hazptr);
	//						// ptr == gp, otherwise => ->fre
	//
	// And
	//	->strong-fence ->fre ->po-unlock-lock-po ->strong-fence ->fre
	// is
	//	->strong-fence ->prop ->strong-fence ->hb ->prop
	// is
	//	->prop ->strong-fence ->prop ->strong-fence ->hb
	// is
	//	->pb ->pb
	//
	smp_mb();
	check_readers(hzst);

	todo = do_hazptr(hzst);

	while (todo) {
		struct callback_head *next = todo->next;
		void (*func)(struct callback_head *) = todo->func;

		func(todo);

		todo = next;
	}
}

void call_hazptr(struct callback_head *head, rcu_callback_t func)
{
	struct hazptr_percpu *pcpu = this_cpu_ptr(&hzpcpu);

	head->func = func;
	head->next = NULL;

	scoped_guard(spinlock_irqsave, &pcpu->callback_lock) {
		*(pcpu->tail) = head;
		pcpu->tail = &head->next;
	}

	guard(spinlock_irqsave)(&hazptr_struct.callback_lock);
	kick_hazptr_work();
}

static int init_hazptr_struct(void)
{
	int cpu;

	INIT_WORK(&hazptr_struct.work, hazptr_work_func);

	spin_lock_init(&hazptr_struct.callback_lock);
	hazptr_struct.queued = NULL;
	hazptr_struct.tail = &hazptr_struct.queued;

	for_each_possible_cpu(cpu) {
		struct hazptr_percpu *pcpu = per_cpu_ptr(&hzpcpu, cpu);

		spin_lock_init(&pcpu->ctx_lock);
		INIT_LIST_HEAD(&pcpu->ctx_list);

		spin_lock_init(&pcpu->callback_lock);
		pcpu->queued = NULL;
		pcpu->tail = &pcpu->queued;

	}

	init_hazptr_reader_tree(&hazptr_struct.readers);

	return 0;
}
early_initcall(init_hazptr_struct);
