/*  Copyright 2003-2016 Ciaran Anscomb
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

#include "xalloc.h"

#include "becker.h"
#include "cart.h"
#include "delegate.h"
#include "mpi.h"
#include "logging.h"
#include "xroar.h"

static struct cart *mpi_new(struct cart_config *);

struct cart_module cart_mpi_module = {
	.name = "mpi",
	.description = "Multi-Pak Interface",
	.new = mpi_new,
};

struct mpi;

struct mpi_slot {
	struct mpi *mpi;
	int id;
	struct cart *cart;
};

struct mpi {
	struct cart cart;
	_Bool switch_enable;
	int cts_route;
	int p2_route;
	unsigned firq_state;
	unsigned nmi_state;
	unsigned halt_state;
	struct mpi_slot slot[4];
};

/* Protect against chained MPI initialisation */

static _Bool mpi_active = 0;

/* Slot configuration */

static char *slot_cart_name[4];
static unsigned initial_slot = 0;

/* Handle signals from cartridges */
static void set_firq(void *, _Bool);
static void set_nmi(void *, _Bool);
static void set_halt(void *, _Bool);

static uint8_t mpi_read(struct cart *c, uint16_t A, _Bool P2, uint8_t D);
static void mpi_write(struct cart *c, uint16_t A, _Bool P2, uint8_t D);
static void mpi_reset(struct cart *c);
static void mpi_attach(struct cart *c);
static void mpi_detach(struct cart *c);
static _Bool mpi_has_interface(struct cart *c, const char *ifname);
static void mpi_attach_interface(struct cart *c, const char *ifname, void *intf);

static void select_slot(struct cart *c, unsigned D);

static struct cart *mpi_new(struct cart_config *cc) {
	if (mpi_active) {
		LOG_WARN("Chaining Multi-Pak Interfaces not supported.\n");
		return NULL;
	}
	mpi_active = 1;

	struct mpi *m = xmalloc(sizeof(*m));
	struct cart *c = &m->cart;

	c->config = cc;
	cart_rom_init(c);
	c->read = mpi_read;
	c->write = mpi_write;
	c->reset = mpi_reset;
	c->attach = mpi_attach;
	c->detach = mpi_detach;
	c->has_interface = mpi_has_interface;
	c->attach_interface = mpi_attach_interface;

	m->switch_enable = 1;
	m->cts_route = 0;
	m->p2_route = 0;
	m->firq_state = 0;
	m->nmi_state = 0;
	m->halt_state = 0;
	for (int i = 0; i < 4; i++) {
		m->slot[i].mpi = m;
		m->slot[i].id = i;
		m->slot[i].cart = NULL;
		if (slot_cart_name[i]) {
			struct cart *c2 = cart_new_named(slot_cart_name[i]);
			if (c2) {
				c2->signal_firq = DELEGATE_AS1(void, bool, set_firq, &m->slot[i]);
				c2->signal_nmi = DELEGATE_AS1(void, bool, set_nmi, &m->slot[i]);
				c2->signal_halt = DELEGATE_AS1(void, bool, set_halt, &m->slot[i]);
				m->slot[i].cart = c2;
			}
		}
	}
	select_slot(c, (initial_slot << 4) | initial_slot);

	return c;
}

static void mpi_reset(struct cart *c) {
	struct mpi *m = (struct mpi *)c;
	m->firq_state = 0;
	m->nmi_state = 0;
	m->halt_state = 0;
	for (int i = 0; i < 4; i++) {
		struct cart *c2 = m->slot[i].cart;
		if (c2 && c2->reset) {
			c2->reset(c2);
		}
	}
}

static void mpi_attach(struct cart *c) {
	(void)c;
}

static void mpi_detach(struct cart *c) {
	struct mpi *m = (struct mpi *)c;
	for (int i = 0; i < 4; i++) {
		cart_free(m->slot[i].cart);
		m->slot[i].cart = NULL;
	}
	mpi_active = 0;
}

static _Bool mpi_has_interface(struct cart *c, const char *ifname) {
	struct mpi *m = (struct mpi *)c;
	for (int i = 0; i < 4; i++) {
		struct cart *c2 = m->slot[i].cart;
		if (c2 && c2->has_interface) {
			if (c2->has_interface(c2, ifname))
				return 1;
		}
	}
	return 0;
}

static void mpi_attach_interface(struct cart *c, const char *ifname, void *intf) {
	struct mpi *m = (struct mpi *)c;
	for (int i = 0; i < 4; i++) {
		struct cart *c2 = m->slot[i].cart;
		if (c2 && c2->has_interface) {
			if (c2->has_interface(c2, ifname)) {
				c2->attach_interface(c2, ifname, intf);
				return;
			}
		}
	}
}

static void debug_cart_name(struct cart *c) {
	if (!c) {
		LOG_PRINT("<empty>");
	} else if (!c->config) {
		LOG_PRINT("<unknown>");
	} else if (c->config->description) {
		LOG_PRINT("%s", c->config->description);
	} else {
		LOG_PRINT("%s", c->config->name);
	}
}

static void select_slot(struct cart *c, unsigned D) {
	struct mpi *m = (struct mpi *)c;
	m->cts_route = (D >> 4) & 3;
	m->p2_route = D & 3;
	if (log_level >= 2) {
		LOG_PRINT("MPI selected: %02x: ROM=", D & 0x33);
		debug_cart_name(m->slot[m->cts_route].cart);
		LOG_PRINT(", IO=");
		debug_cart_name(m->slot[m->p2_route].cart);
		LOG_PRINT("\n");
	}
}

void mpi_switch_slot(struct cart *c, unsigned slot) {
	struct mpi *m = (struct mpi *)c;
	if (!m || !m->switch_enable)
		return;
	if (slot > 3)
		return;
	select_slot(c, (slot << 4) | slot);
}

static uint8_t mpi_read(struct cart *c, uint16_t A, _Bool P2, uint8_t D) {
	struct mpi *m = (struct mpi *)c;
	if (A == 0xff7f) {
		return (m->cts_route << 4) | m->p2_route;
	}
	struct cart *c2 = NULL;
	if (P2) {
		c2 = m->slot[m->p2_route].cart;
	} else {
		c2 = m->slot[m->cts_route].cart;
	}
	if (c2)
		return c2->read(c2, A, P2, D);
	return D;
}

static void mpi_write(struct cart *c, uint16_t A, _Bool P2, uint8_t D) {
	struct mpi *m = (struct mpi *)c;
	if (A == 0xff7f) {
		m->switch_enable = 0;
		select_slot(c, D);
		return;
	}
	struct cart *c2 = NULL;
	if (P2) {
		c2 = m->slot[m->p2_route].cart;
	} else {
		c2 = m->slot[m->cts_route].cart;
	}
	if (c2)
		c2->write(c2, A, P2, D);
}

static void set_firq(void *sptr, _Bool value) {
	struct mpi_slot *ms = sptr;
	struct mpi *m = ms->mpi;
	unsigned firq_bit = 1 << ms->id;
	if (value) {
		m->firq_state |= firq_bit;
	} else {
		m->firq_state &= ~firq_bit;
	}
	DELEGATE_CALL1(m->cart.signal_firq, m->firq_state);
}

static void set_nmi(void *sptr, _Bool value) {
	struct mpi_slot *ms = sptr;
	struct mpi *m = ms->mpi;
	unsigned nmi_bit = 1 << ms->id;
	if (value) {
		m->nmi_state |= nmi_bit;
	} else {
		m->nmi_state &= ~nmi_bit;
	}
	DELEGATE_CALL1(m->cart.signal_nmi, m->nmi_state);
}

static void set_halt(void *sptr, _Bool value) {
	struct mpi_slot *ms = sptr;
	struct mpi *m = ms->mpi;
	unsigned halt_bit = 1 << ms->id;
	if (value) {
		m->halt_state |= halt_bit;
	} else {
		m->halt_state &= ~halt_bit;
	}
	DELEGATE_CALL1(m->cart.signal_halt, m->halt_state);
}

/* Configure */

void mpi_set_initial(int slot) {
	if (slot < 0 || slot > 3) {
		LOG_WARN("MPI: Invalid slot '%d'\n", slot);
		return;
	}
	initial_slot = slot;
}

void mpi_set_cart(int slot, const char *name) {
	if (slot < 0 || slot > 3) {
		LOG_WARN("MPI: Invalid slot '%d'\n", slot);
		return;
	}
	if (slot_cart_name[slot]) {
		free(slot_cart_name[slot]);
	}
	slot_cart_name[slot] = xstrdup(name);
}
