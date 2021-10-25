/** \file
 *
 *  \brief Dragon keyboard.
 *
 *  \copyright Copyright 2003-2021 Ciaran Anscomb
 *
 *  \licenseblock This file is part of XRoar, a Dragon/Tandy CoCo emulator.
 *
 *  XRoar is free software; you can redistribute it and/or modify it under the
 *  terms of the GNU General Public License as published by the Free Software
 *  Foundation, either version 3 of the License, or (at your option) any later
 *  version.
 *
 *  See COPYING.GPL for redistribution conditions.
 *
 *  \endlicenseblock
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdlib.h>
#include <string.h>

#include "delegate.h"
#include "sds.h"
#include "sdsx.h"
#include "slist.h"
#include "xalloc.h"

#include "breakpoint.h"
#include "debug_cpu.h"
#include "dkbd.h"
#include "events.h"
#include "keyboard.h"
#include "logging.h"
#include "machine.h"
#include "mc6801.h"
#include "mc6809.h"
#include "part.h"
#include "tape.h"
#include "xroar.h"

// Might want to make a more general automation interface out of this at some
// point, but for now here it is, in with the keyboard stuff:

enum auto_type {
	auto_type_basic_command,  // type a command into BASIC
	auto_type_press_play,     // press play on tape
};

struct auto_event {
	enum auto_type type;
	union {
		sds string;
	} data;
};

/* Current chording mode - only affects how backslash is typed: */
static enum keyboard_chord_mode chord_mode = keyboard_chord_mode_dragon_32k_basic;

struct keyboard_interface_private {
	struct keyboard_interface public;

	struct machine *machine;
	struct debug_cpu *debug_cpu;
	_Bool is_6809;
	_Bool is_6801;

	struct slist *auto_event_list;
	unsigned command_index;  // when typing a basic command
};

extern inline void keyboard_press_matrix(struct keyboard_interface *ki, int col, int row);
extern inline void keyboard_release_matrix(struct keyboard_interface *ki, int col, int row);
extern inline void keyboard_press(struct keyboard_interface *ki, int s);
extern inline void keyboard_release(struct keyboard_interface *ki, int s);

static void do_auto_event(void *);

static struct machine_bp basic_command_breakpoint[] = {
	BP_DRAGON_ROM(.address = 0xbbe5, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_COCO_BAS10_ROM(.address = 0xa1c1, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_COCO_BAS11_ROM(.address = 0xa1c1, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_COCO_BAS12_ROM(.address = 0xa1cb, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_COCO_BAS13_ROM(.address = 0xa1cb, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_COCO3_ROM(.address = 0xa1cb, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_MC10_ROM(.address = 0xf883, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
	BP_MX1600_BAS_ROM(.address = 0xa1cb, .handler = DELEGATE_INIT(do_auto_event, NULL) ),
};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static void auto_event_free(struct auto_event *ae) {
	if (!ae)
		return;
	switch (ae->type) {
	case auto_type_basic_command:
		sdsfree(ae->data.string);
		break;
	default:
		break;
	}
	free(ae);
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

struct keyboard_interface *keyboard_interface_new(struct machine *m) {
	struct keyboard_interface_private *kip = xmalloc(sizeof(*kip));
	*kip = (struct keyboard_interface_private){0};
	struct keyboard_interface *ki = &kip->public;
	kip->machine = m;
	kip->debug_cpu = (struct debug_cpu *)part_component_by_id_is_a((struct part *)m, "CPU", "DEBUG-CPU");
	kip->is_6809 = part_is_a(&kip->debug_cpu->part, "MC6809");
	kip->is_6801 = part_is_a(&kip->debug_cpu->part, "MC6801");
	for (int i = 0; i < 8; i++) {
		ki->keyboard_column[i] = ~0;
		ki->keyboard_row[i] = ~0;
	}
	return ki;
}

void keyboard_interface_free(struct keyboard_interface *ki) {
	struct keyboard_interface_private *kip = (struct keyboard_interface_private *)ki;
	if (kip->debug_cpu)
		machine_bp_remove_list(kip->machine, basic_command_breakpoint);
	slist_free_full(kip->auto_event_list, (slist_free_func)auto_event_free);
	free(kip);
}

void keyboard_set_keymap(struct keyboard_interface *ki, int map) {
	map %= dkbd_num_layouts;
	xroar_machine_config->keymap = map;
	dkbd_map_init(&ki->keymap, map);
}

void keyboard_set_chord_mode(struct keyboard_interface *ki, enum keyboard_chord_mode mode) {
	chord_mode = mode;
	if (ki->keymap.layout == dkbd_layout_dragon) {
		if (mode == keyboard_chord_mode_dragon_32k_basic) {
			ki->keymap.unicode_to_dkey['\\'].dk_key = DSCAN_COMMA;
		} else {
			ki->keymap.unicode_to_dkey['\\'].dk_key = DSCAN_INVALID;
		}
	}
}

/* Compute sources & sinks based on inputs to the matrix and the current state
 * of depressed keys. */

void keyboard_read_matrix(struct keyboard_interface *ki, struct keyboard_state *state) {
	/* Ghosting: combine columns that share any pressed rows.  Repeat until
	 * no change in the row mask. */
	unsigned old;
	do {
		old = state->row_sink;
		for (int i = 0; i < 8; i++) {
			if (~state->row_sink & ~ki->keyboard_column[i]) {
				state->col_sink &= ~(1 << i);
				state->row_sink &= ki->keyboard_column[i];
			}
		}
	} while (old != state->row_sink);
	/* Likewise combining rows. */
	do {
		old = state->col_sink;
		for (int i = 0; i < 7; i++) {
			if (~state->col_sink & ~ki->keyboard_row[i]) {
				state->row_sink &= ~(1 << i);
				state->col_sink &= ki->keyboard_row[i];
			}
		}
	} while (old != state->col_sink);

	/* Sink & source any directly connected rows & columns */
	for (int i = 0; i < 8; i++) {
		if (!(state->col_sink & (1 << i))) {
			state->row_sink &= ki->keyboard_column[i];
		}
		if (state->col_source & (1 << i)) {
			state->row_source |= ~ki->keyboard_column[i];
		}
	}
	for (int i = 0; i < 7; i++) {
		if (!(state->row_sink & (1 << i))) {
			state->col_sink &= ki->keyboard_row[i];
		}
		if (state->row_source & (1 << i)) {
			state->col_source |= ~ki->keyboard_row[i];
		}
	}
}

void keyboard_unicode_press(struct keyboard_interface *ki, unsigned unicode) {
	if (unicode >= DKBD_U_TABLE_SIZE)
		return;
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_SHIFT)
		KEYBOARD_PRESS_SHIFT(ki);
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_UNSHIFT)
		KEYBOARD_RELEASE_SHIFT(ki);
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_CLEAR)
		KEYBOARD_PRESS_CLEAR(ki);
	int s = ki->keymap.unicode_to_dkey[unicode].dk_key;
	keyboard_press_matrix(ki, ki->keymap.point[s].col, ki->keymap.point[s].row);
	DELEGATE_SAFE_CALL(ki->update);
}

void keyboard_unicode_release(struct keyboard_interface *ki, unsigned unicode) {
	if (unicode >= DKBD_U_TABLE_SIZE)
		return;
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_SHIFT)
		KEYBOARD_RELEASE_SHIFT(ki);
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_UNSHIFT)
		KEYBOARD_PRESS_SHIFT(ki);
	if (ki->keymap.unicode_to_dkey[unicode].dk_mod & DK_MOD_CLEAR)
		KEYBOARD_RELEASE_CLEAR(ki);
	int s = ki->keymap.unicode_to_dkey[unicode].dk_key;
	keyboard_release_matrix(ki, ki->keymap.point[s].col, ki->keymap.point[s].row);
	DELEGATE_SAFE_CALL(ki->update);
}

static void do_auto_event(void *sptr) {
	struct keyboard_interface_private *kip = sptr;
	struct MC6801 *cpu01 = (struct MC6801 *)kip->debug_cpu;
	struct MC6809 *cpu09 = (struct MC6809 *)kip->debug_cpu;

	if (!kip->auto_event_list)
		return;

	// Default to no key pressed
	if (kip->is_6809 && cpu09) {
		MC6809_REG_A(cpu09) = 0;
		cpu09->reg_cc |= 4;
	}
	if (kip->is_6801 && cpu01) {
		MC6801_REG_A(cpu01) = 0;
		cpu01->reg_cc |= 4;
	}

	struct auto_event *ae = kip->auto_event_list->data;

	if (ae->type == auto_type_basic_command) {
		// type a command into BASIC
		if (kip->command_index < sdslen(ae->data.string)) {
			uint8_t byte = ae->data.string[kip->command_index++];
			// CHR$(0)="[" on Dragon 200-E, so clear Z flag even if zero,
			// as otherwise BASIC will skip it.
			if (kip->is_6809 && cpu09) {
				MC6809_REG_A(cpu09) = byte;
				cpu09->reg_cc &= ~4;
			}
			if (kip->is_6801 && cpu01) {
				MC6801_REG_A(cpu01) = byte;
				cpu01->reg_cc &= ~4;
			}
		}
		if (kip->command_index >= sdslen(ae->data.string)) {
			kip->auto_event_list = slist_remove(kip->auto_event_list, ae);
			kip->command_index = 0;
			auto_event_free(ae);
			ae = kip->auto_event_list ? kip->auto_event_list->data : NULL;
		}
	}

	// Process all non-typing queued events that might follow - this allows
	// us to press PLAY immediately after typing when the keyboard
	// breakpoint won't be useful.

	while (ae && ae->type != auto_type_basic_command) {
		switch (ae->type) {

		case auto_type_press_play:
			// press play on tape
			tape_set_playing(xroar_tape_interface, 1, 1);
			break;

		default:
			break;
		}

		kip->auto_event_list = slist_remove(kip->auto_event_list, ae);
		auto_event_free(ae);
		ae = kip->auto_event_list ? kip->auto_event_list->data : NULL;
	}

	// Use CPU read routine to pull return address back off stack
	kip->machine->op_rts(kip->machine);

	if (!kip->auto_event_list) {
		machine_bp_remove_list(kip->machine, basic_command_breakpoint);
	}
}

static sds parse_string(sds s, enum dkbd_layout layout) {
	if (!s)
		return NULL;
	// treat everything as unsigned char
	const unsigned char *p = (unsigned char *)s;
	size_t len = sdslen(s);
	sds new = sdsempty();
	while (len > 0) {
		unsigned char chr = *(p++);
		len--;

		// Most translations here are for the Dragon 200-E keyboard,
		// but we map '\e' specially to BREAK:
		if (chr == 0x1b) {
			chr = 0x03;
		}

		if (layout == dkbd_layout_dragon200e) {
			switch (chr) {
			case '[': chr = 0x00; break;
			case ']': chr = 0x01; break;
			case '\\': chr = 0x0b; break;
			// some very partial utf-8 decoding:
			case 0xc2:
				if (len > 0) {
					len--;
					switch (*(p++)) {
					case 0xa1: chr = 0x5b; break; // ¡
					case 0xa7: chr = 0x13; break; // §
					case 0xba: chr = 0x14; break; // º
					case 0xbf: chr = 0x5d; break; // ¿
					default: p--; len++; break;
					}
				}
				break;
			case 0xc3:
				if (len > 0) {
					len--;
					switch (*(p++)) {
					case 0x80: case 0xa0: chr = 0x1b; break; // à
					case 0x81: case 0xa1: chr = 0x16; break; // á
					case 0x82: case 0xa2: chr = 0x0e; break; // â
					case 0x83: case 0xa3: chr = 0x0a; break; // ã
					case 0x84: case 0xa4: chr = 0x05; break; // ä
					case 0x87: case 0xa7: chr = 0x7d; break; // ç
					case 0x88: case 0xa8: chr = 0x1c; break; // è
					case 0x89: case 0xa9: chr = 0x17; break; // é
					case 0x8a: case 0xaa: chr = 0x0f; break; // ê
					case 0x8b: case 0xab: chr = 0x06; break; // ë
					case 0x8c: case 0xac: chr = 0x1d; break; // ì
					case 0x8d: case 0xad: chr = 0x18; break; // í
					case 0x8e: case 0xae: chr = 0x10; break; // î
					case 0x8f: case 0xaf: chr = 0x09; break; // ï
					case 0x91: chr = 0x5c; break; // Ñ
					case 0x92: case 0xb2: chr = 0x1e; break; // ò
					case 0x93: case 0xb3: chr = 0x19; break; // ó
					case 0x94: case 0xb4: chr = 0x11; break; // ô
					case 0x96: case 0xb6: chr = 0x07; break; // ö
					case 0x99: case 0xb9: chr = 0x1f; break; // ù
					case 0x9a: case 0xba: chr = 0x1a; break; // ú
					case 0x9b: case 0xbb: chr = 0x12; break; // û
					case 0x9c: chr = 0x7f; break; // Ü
					case 0x9f: chr = 0x02; break; // ß (also β)
					case 0xb1: chr = 0x7c; break; // ñ
					case 0xbc: chr = 0x7b; break; // ü
					default: p--; len++; break;
					}
				}
				break;
			case 0xce:
				if (len > 0) {
					len--;
					switch (*(p++)) {
					case 0xb1: case 0x91: chr = 0x04; break; // α
					case 0xb2: case 0x92: chr = 0x02; break; // β (also ß)
					default: p--; len++; break;
					}
				}
				break;
			default: break;
			}
		}

		new = sdscatlen(new, (char *)&chr, 1);
	}
	return new;
}

static void queue_auto_event(struct keyboard_interface_private *kip, struct auto_event *ae) {
	machine_bp_remove_list(kip->machine, basic_command_breakpoint);
	kip->auto_event_list = slist_append(kip->auto_event_list, ae);
	if (kip->auto_event_list) {
		machine_bp_add_list(kip->machine, basic_command_breakpoint, kip);
	}
}

void keyboard_queue_basic_sds(struct keyboard_interface *ki, sds s) {
	struct keyboard_interface_private *kip = (struct keyboard_interface_private *)ki;
	if (s) {
		struct auto_event *ae = xmalloc(sizeof(*ae));
		ae->type = auto_type_basic_command;
		ae->data.string = parse_string(s, ki->keymap.layout);
		queue_auto_event(kip, ae);
	}
}

void keyboard_queue_basic(struct keyboard_interface *ki, const char *str) {
	sds s = str ? sdsx_parse_str(str): NULL;
	keyboard_queue_basic_sds(ki, s);
	if (s)
		sdsfree(s);
}

void keyboard_queue_press_play(struct keyboard_interface *ki) {
	struct keyboard_interface_private *kip = (struct keyboard_interface_private *)ki;
	struct auto_event *ae = xmalloc(sizeof(*ae));
	ae->type = auto_type_press_play;
	queue_auto_event(kip, ae);
}
