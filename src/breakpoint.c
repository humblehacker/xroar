/*  Copyright 2003-2015 Ciaran Anscomb
 *
 *  This file is part of XRoar.
 *
 *  XRoar is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  XRoar is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with XRoar.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "config.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "slist.h"
#include "xalloc.h"

#include "breakpoint.h"
#include "crclist.h"
#include "logging.h"
#include "machine.h"
#include "mc6809.h"
#include "sam.h"
#include "xroar.h"

static struct slist *bp_instruction_list = NULL;

static struct slist *wp_read_list = NULL;
static struct slist *wp_write_list = NULL;

static struct slist *iter_next = NULL;

static void bp_instruction_hook(void *);

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static _Bool is_in_list(struct slist *bp_list, struct breakpoint *bp) {
	for (struct slist *iter = bp_list; iter; iter = iter->next) {
		if (bp == iter->data)
			return 1;
	}
	return 0;
}

void bp_add(struct breakpoint *bp) {
	if (is_in_list(bp_instruction_list, bp))
		return;
	bp->address_end = bp->address;
	bp_instruction_list = slist_prepend(bp_instruction_list, bp);
	struct MC6809 *cpu = machine_get_cpu(0);
	cpu->instruction_hook = DELEGATE_AS0(void, bp_instruction_hook, cpu);
}

void bp_add_n(struct breakpoint *bp, int n) {
	for (int i = 0; i < n; i++) {
		if ((bp[i].add_cond & BP_MACHINE_ARCH) && xroar_machine_config->architecture != bp[i].cond_machine_arch)
			continue;
		if ((bp[i].add_cond & BP_CRC_COMBINED) && (!has_combined || !crclist_match(bp[i].cond_crc_combined, crc_combined)))
			continue;
		if ((bp[i].add_cond & BP_CRC_EXT) && (!has_extbas || !crclist_match(bp[i].cond_crc_extbas, crc_extbas)))
			continue;
		if ((bp[i].add_cond & BP_CRC_BAS) && (!has_bas || !crclist_match(bp[i].cond_crc_bas, crc_bas)))
			continue;
		// XXX always overriding the handler data here.  It's never set
		// to anything else so far, but without this, adding static
		// breakpoints will not update the CPU pointer.
		bp[i].handler_data = machine_get_cpu(0);
		bp_add(&bp[i]);
	}
}

void bp_remove(struct breakpoint *bp) {
	if (iter_next && iter_next->data == bp)
		iter_next = iter_next->next;
	bp_instruction_list = slist_remove(bp_instruction_list, bp);
	if (!bp_instruction_list) {
		struct MC6809 *cpu = machine_get_cpu(0);
		if (cpu)
			cpu->instruction_hook.func = NULL;
	}
}

void bp_remove_n(struct breakpoint *bp, int n) {
	int i;
	for (i = 0; i < n; i++) {
		bp_remove(&bp[i]);
	}
}

static struct breakpoint *trap_find(struct slist *bp_list, unsigned addr, unsigned addr_end,
				    unsigned match_mask, unsigned match_cond) {
	for (struct slist *iter = bp_list; iter; iter = iter->next) {
		struct breakpoint *bp = iter->data;
		if (bp->address == addr && bp->address_end == addr_end
		    && bp->match_mask == match_mask
		    && bp->match_cond == match_cond
		    && bp->handler == xroar_machine_trap)
			return bp;
	}
	return NULL;
}

static void trap_add(struct slist **bp_list, unsigned addr, unsigned addr_end,
		     unsigned match_mask, unsigned match_cond) {
	if (trap_find(*bp_list, addr, addr_end, match_mask, match_cond))
		return;
	struct breakpoint *new = xmalloc(sizeof(*new));
	new->match_mask = match_mask;
	new->match_cond = match_cond;
	new->address = addr;
	new->address_end = addr_end;
	new->handler = xroar_machine_trap;
	*bp_list = slist_prepend(*bp_list, new);
}

static void trap_remove(struct slist **bp_list, unsigned addr, unsigned addr_end,
			unsigned match_mask, unsigned match_cond) {
	struct breakpoint *bp = trap_find(*bp_list, addr, addr_end, match_mask, match_cond);
	if (bp) {
		if (iter_next && iter_next->data == bp)
			iter_next = iter_next->next;
		*bp_list = slist_remove(*bp_list, bp);
		free(bp);
	}
}

void bp_hbreak_add(unsigned addr, unsigned match_mask, unsigned match_cond) {
	trap_add(&bp_instruction_list, addr, addr, match_mask, match_cond);
	if (bp_instruction_list) {
		struct MC6809 *cpu = machine_get_cpu(0);
		cpu->instruction_hook = DELEGATE_AS0(void, bp_instruction_hook, cpu);
	}
}

void bp_hbreak_remove(unsigned addr, unsigned match_mask, unsigned match_cond) {
	trap_remove(&bp_instruction_list, addr, addr, match_mask, match_cond);
	if (!bp_instruction_list) {
		struct MC6809 *cpu = machine_get_cpu(0);
		cpu->instruction_hook.func = NULL;
	}
}

void bp_wp_add(unsigned type, unsigned addr, unsigned nbytes, unsigned match_mask, unsigned match_cond) {
	switch (type) {
	case 2:
		trap_add(&wp_write_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	case 3:
		trap_add(&wp_read_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	case 4:
		trap_add(&wp_write_list, addr, addr + nbytes - 1, match_mask, match_cond);
		trap_add(&wp_read_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	default:
		break;
	}
}

void bp_wp_remove(unsigned type, unsigned addr, unsigned nbytes, unsigned match_mask, unsigned match_cond) {
	switch (type) {
	case 2:
		trap_remove(&wp_write_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	case 3:
		trap_remove(&wp_read_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	case 4:
		trap_remove(&wp_write_list, addr, addr + nbytes - 1, match_mask, match_cond);
		trap_remove(&wp_read_list, addr, addr + nbytes - 1, match_mask, match_cond);
		break;
	default:
		break;
	}
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

/* Check the supplied list for any matching hooks.  These are temporarily
 * addded to a new list for dispatch, as the handler may call routines that
 * alter the original list. */

static void bp_hook(struct slist *bp_list, unsigned address) {
	unsigned sam_register = sam_get_register(SAM0);
	unsigned cond = sam_register & 0x8400;
	for (struct slist *iter = bp_list; iter; iter = iter_next) {
		iter_next = iter->next;
		struct breakpoint *bp = iter->data;
		if ((cond & bp->match_mask) != bp->match_cond)
			continue;
		if (address < bp->address)
			continue;
		if (address > bp->address_end)
			continue;
		bp->handler(bp->handler_data);
	}
	iter_next = NULL;
}

static void bp_instruction_hook(void *sptr) {
	struct MC6809 *cpu = sptr;
	uint16_t old_pc;
	do {
		old_pc = cpu->reg_pc;
		bp_hook(bp_instruction_list, old_pc);
	} while (old_pc != cpu->reg_pc);
}

void bp_wp_read_hook(unsigned address) {
	if (wp_read_list)
		bp_hook(wp_read_list, address);
}

void bp_wp_write_hook(unsigned address) {
	if (wp_read_list)
		bp_hook(wp_write_list, address);
}
