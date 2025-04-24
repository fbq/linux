// SPDX-License-Identifier: GPL-2.0

#include <linux/bitops.h>
#include "helpers.h"

__rust_helper void rust_helper___set_bit(unsigned int nr, unsigned long *addr)
{
	__set_bit(nr, addr);
}

__rust_helper void rust_helper___clear_bit(unsigned int nr, unsigned long *addr)
{
	__clear_bit(nr, addr);
}

__rust_helper void rust_helper_set_bit(unsigned int nr, volatile unsigned long *addr)
{
	set_bit(nr, addr);
}

__rust_helper void rust_helper_clear_bit(unsigned int nr, volatile unsigned long *addr)
{
	clear_bit(nr, addr);
}
