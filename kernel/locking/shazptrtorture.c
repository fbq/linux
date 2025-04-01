// SPDX-License-Identifier: GPL-2.0+
/*
 * Module-based torture test facility for shazptr
 *
 * Copyright (C) Microsoft Corporation, 2025
 *
 * Author: Boqun Feng <boqun.feng@gmail.com>
 *	Based on kernel/rcu/torture.c.
 */

#define pr_fmt(fmt) fmt

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/torture.h>

MODULE_DESCRIPTION("torture test facility for locking");
MODULE_LICENSE("GPL");
MODULE_AUTHOR("Boqun Feng <boqun.feng@gmail.com>");

torture_param(int, verbose, 1, "Enable verbose debugging printk()s");

static int __init shazptr_torture_init(void)
{
	if (!torture_init_begin("shazptr", verbose))
		return -EBUSY;
	torture_init_end();
	return 0;
}

static void shazptr_torture_cleanup(void)
{
}

module_init(shazptr_torture_init);
module_exit(shazptr_torture_cleanup);
