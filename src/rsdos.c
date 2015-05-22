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

/* Sources:
 *     CoCo DOS cartridge detail:
 *         http://www.coco3.com/unravalled/disk-basic-unravelled.pdf
 */

#include "config.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "xalloc.h"

#include "becker.h"
#include "cart.h"
#include "delegate.h"
#include "logging.h"
#include "rsdos.h"
#include "vdrive.h"
#include "wd279x.h"
#include "xroar.h"

struct rsdos {
	struct cart cart;
	unsigned ic1_old;
	unsigned ic1_drive_select;
	_Bool ic1_density;
	_Bool drq_flag;
	_Bool intrq_flag;
	_Bool halt_enable;
	_Bool have_becker;
	WD279X *fdc;
};

static uint8_t rsdos_read(struct cart *c, uint16_t A, _Bool P2, uint8_t D);
static void rsdos_write(struct cart *c, uint16_t A, _Bool P2, uint8_t D);
static void rsdos_reset(struct cart *c);
static void rsdos_detach(struct cart *c);
static void ff40_write(struct rsdos *r, unsigned flags);

/* Handle signals from WD2793 */
static void set_drq(void *, _Bool);
static void set_intrq(void *, _Bool);

static void rsdos_init(struct rsdos *r) {
	struct cart *c = (struct cart *)r;
	struct cart_config *cc = c->config;
	cart_rom_init(c);
	c->read = rsdos_read;
	c->write = rsdos_write;
	c->reset = rsdos_reset;
	c->detach = rsdos_detach;
	r->have_becker = (cc->becker_port && becker_open());
	r->fdc = wd279x_new(WD2793);
	r->fdc->set_dirc = DELEGATE_AS1(void, int, vdrive_set_dirc, NULL);
	r->fdc->set_dden = DELEGATE_AS1(void, bool, vdrive_set_dden, NULL);
	r->fdc->set_drq = DELEGATE_AS1(void, bool, set_drq, c);
	r->fdc->set_intrq = DELEGATE_AS1(void, bool, set_intrq, c);
	vdrive_ready = DELEGATE_AS1(void, bool, wd279x_ready, r->fdc);
	vdrive_tr00 = DELEGATE_AS1(void, bool, wd279x_tr00, r->fdc);
	vdrive_index_pulse = DELEGATE_AS1(void, bool, wd279x_index_pulse, r->fdc);
	vdrive_write_protect = DELEGATE_AS1(void, bool, wd279x_write_protect, r->fdc);
	wd279x_update_connection(r->fdc);
	vdrive_update_connection();
}

struct cart *rsdos_new(struct cart_config *cc) {
	struct rsdos *r = xmalloc(sizeof(*r));
	r->cart.config = cc;
	rsdos_init(r);
	return (struct cart *)r;
}

static void rsdos_reset(struct cart *c) {
	struct rsdos *r = (struct rsdos *)c;
	wd279x_reset(r->fdc);
	r->ic1_old = -1;
	r->ic1_drive_select = -1;
	r->drq_flag = r->intrq_flag = 0;
	ff40_write(r, 0);
	if (r->have_becker)
		becker_reset();
}

static void rsdos_detach(struct cart *c) {
	struct rsdos *r = (struct rsdos *)c;
	vdrive_ready = DELEGATE_DEFAULT1(void, bool);
	vdrive_tr00 = DELEGATE_DEFAULT1(void, bool);
	vdrive_index_pulse = DELEGATE_DEFAULT1(void, bool);
	vdrive_write_protect = DELEGATE_DEFAULT1(void, bool);
	wd279x_free(r->fdc);
	r->fdc = NULL;
	if (r->have_becker)
		becker_close();
	cart_rom_detach(c);
}

static uint8_t rsdos_read(struct cart *c, uint16_t A, _Bool P2, uint8_t D) {
	struct rsdos *r = (struct rsdos *)c;
	if (!P2) {
		return c->rom_data[A & 0x3fff];
	}
	if (A & 0x8) {
		return wd279x_read(r->fdc, A);
	}
	if (r->have_becker) {
		switch (A & 3) {
		case 0x1:
			return becker_read_status();
		case 0x2:
			return becker_read_data();
		default:
			break;
		}
	}
	return D;
}

static void rsdos_write(struct cart *c, uint16_t A, _Bool P2, uint8_t D) {
	struct rsdos *r = (struct rsdos *)c;
	if (!P2)
		return;
	if (A & 0x8) {
		wd279x_write(r->fdc, A, D);
		return;
	}
	if (r->have_becker) {
		/* XXX not exactly sure in what way anyone has tightened up the
		 * address decoding for the becker port */
		switch (A & 3) {
		case 0x0:
			ff40_write(r, D);
			break;
		case 0x2:
			becker_write_data(D);
			break;
		default:
			break;
		}
	} else {
		if (!(A & 8))
			ff40_write(r, D);
	}
}

/* RSDOS cartridge circuitry */
static void ff40_write(struct rsdos *r, unsigned flags) {
	struct cart *c = (struct cart *)r;
	unsigned new_drive_select = 0;
	flags ^= 0x20;
	if (flags & 0x01) {
		new_drive_select = 0;
	} else if (flags & 0x02) {
		new_drive_select = 1;
	} else if (flags & 0x04) {
		new_drive_select = 2;
	}
	vdrive_set_sso(NULL, (flags & 0x40) ? 1 : 0);
	if (flags != r->ic1_old) {
		LOG_DEBUG(2, "RSDOS: Write to FF40: ");
		if (new_drive_select != r->ic1_drive_select) {
			LOG_DEBUG(2, "DRIVE SELECT %u, ", new_drive_select);
		}
		if ((flags ^ r->ic1_old) & 0x08) {
			LOG_DEBUG(2, "MOTOR %s, ", (flags & 0x08)?"ON":"OFF");
		}
		if ((flags ^ r->ic1_old) & 0x20) {
			LOG_DEBUG(2, "DENSITY %s, ", (flags & 0x20)?"SINGLE":"DOUBLE");
		}
		if ((flags ^ r->ic1_old) & 0x10) {
			LOG_DEBUG(2, "PRECOMP %s, ", (flags & 0x10)?"ON":"OFF");
		}
		if ((flags ^ r->ic1_old) & 0x40) {
			LOG_DEBUG(2, "SIDE %d, ", (flags & 0x40) >> 6);
		}
		if ((flags ^ r->ic1_old) & 0x80) {
			LOG_DEBUG(2, "HALT %s, ", (flags & 0x80)?"ENABLED":"DISABLED");
		}
		LOG_DEBUG(2, "\n");
		r->ic1_old = flags;
	}
	r->ic1_drive_select = new_drive_select;
	vdrive_set_drive(r->ic1_drive_select);
	r->ic1_density = flags & 0x20;
	wd279x_set_dden(r->fdc, !r->ic1_density);
	if (r->ic1_density && r->intrq_flag) {
		DELEGATE_CALL1(c->signal_nmi, 1);
	}
	r->halt_enable = flags & 0x80;
	if (r->intrq_flag) r->halt_enable = 0;
	DELEGATE_CALL1(c->signal_halt, r->halt_enable && !r->drq_flag);
}

static void set_drq(void *sptr, _Bool value) {
	struct cart *c = sptr;
	struct rsdos *r = sptr;
	r->drq_flag = value;
	if (value) {
		DELEGATE_CALL1(c->signal_halt, 0);
	} else {
		if (r->halt_enable) {
			DELEGATE_CALL1(c->signal_halt, 1);
		}
	}
}

static void set_intrq(void *sptr, _Bool value) {
	struct cart *c = sptr;
	struct rsdos *r = sptr;
	r->intrq_flag = value;
	if (value) {
		r->halt_enable = 0;
		DELEGATE_CALL1(c->signal_halt, 0);
		if (!r->ic1_density && r->intrq_flag) {
			DELEGATE_CALL1(c->signal_nmi, 1);
		}
	} else {
		DELEGATE_CALL1(c->signal_nmi, 0);
	}
}
