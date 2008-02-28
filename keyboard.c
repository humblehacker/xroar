/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2008  Ciaran Anscomb
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include <string.h>

#include "types.h"
#include "events.h"
#include "keyboard.h"
#include "logging.h"
#include "machine.h"
#include "mc6821.h"
#include "xroar.h"

/* These map virtual scancodes to keyboard matrix points */
static Keymap dragon_keymap = {
	{7,6}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 0 - 7 */
	{5,5}, {6,5}, {4,5}, {8,8}, {1,6}, {0,6}, {8,8}, {8,8}, /* 8 - 15 */
	{8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 16 - 23 */
	{8,8}, {8,8}, {8,8}, {2,6}, {8,8}, {8,8}, {8,8}, {8,8}, /* 24 - 31 */
	{7,5}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 32 - 39 */
	{8,8}, {8,8}, {8,8}, {8,8}, {4,1}, {5,1}, {6,1}, {7,1}, /* 40 - 47 */
	{0,0}, {1,0}, {2,0}, {3,0}, {4,0}, {5,0}, {6,0}, {7,0}, /* 48 - 55 */
	{0,1}, {1,1}, {2,1}, {3,1}, {8,8}, {8,8}, {8,8}, {8,8}, /* 56 - 63 */
	{0,2}, {1,2}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, /* 64 - 71 */
	{0,3}, {1,3}, {2,3}, {3,3}, {4,3}, {5,3}, {6,3}, {7,3}, /* 72 - 79 */
	{0,4}, {1,4}, {2,4}, {3,4}, {4,4}, {5,4}, {6,4}, {7,4}, /* 80 - 87 */
	{0,5}, {1,5}, {2,5}, {8,8}, {8,8}, {8,8}, {3,5}, {8,8}, /* 88 - 95 */
	{1,6}, {1,2}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, /* 96 - 103 */
	{0,3}, {1,3}, {2,3}, {3,3}, {4,3}, {5,3}, {6,3}, {7,3}, /* 104 - 111 */
	{0,4}, {1,4}, {2,4}, {3,4}, {4,4}, {5,4}, {6,4}, {7,4}, /* 112 - 119 */
	{0,5}, {1,5}, {2,5}, {8,8}, {8,8}, {8,8}, {8,8}, {5,5}, /* 120 - 127 */
};
static Keymap coco_keymap = {
	{7,6}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 0 - 7 */
	{5,3}, {6,3}, {4,3}, {8,8}, {1,6}, {0,6}, {8,8}, {8,8}, /* 8 - 15 */
	{8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 16 - 23 */
	{8,8}, {8,8}, {8,8}, {2,6}, {8,8}, {8,8}, {8,8}, {8,8}, /* 24 - 31 */
	{7,3}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, {8,8}, /* 32 - 39 */
	{8,8}, {8,8}, {8,8}, {8,8}, {4,5}, {5,5}, {6,5}, {7,5}, /* 40 - 47 */
	{0,4}, {1,4}, {2,4}, {3,4}, {4,4}, {5,4}, {6,4}, {7,4}, /* 48 - 55 */
	{0,5}, {1,5}, {2,5}, {3,5}, {8,8}, {5,5}, {8,8}, {8,8}, /* 56 - 63 */
	{0,0}, {1,0}, {2,0}, {3,0}, {4,0}, {5,0}, {6,0}, {7,0}, /* 64 - 71 */
	{0,1}, {1,1}, {2,1}, {3,1}, {4,1}, {5,1}, {6,1}, {7,1}, /* 72 - 79 */
	{0,2}, {1,2}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, /* 80 - 87 */
	{0,3}, {1,3}, {2,3}, {0,0}, {8,8}, {8,8}, {3,3}, {8,8}, /* 88 - 95 */
	{1,6}, {1,0}, {2,0}, {3,0}, {4,0}, {5,0}, {6,0}, {7,0}, /* 96 - 103 */
	{0,1}, {1,1}, {2,1}, {3,1}, {4,1}, {5,1}, {6,1}, {7,1}, /* 104 - 111 */
	{0,2}, {1,2}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, /* 112 - 119 */
	{0,3}, {1,3}, {2,3}, {8,8}, {8,8}, {8,8}, {8,8}, {5,3}, /* 120 - 127 */
};
Keymap keymap;  /* active keymap */

/* These contain masks to be applied when the corresponding row/column is
 * held low.  eg, if row 1 is outputting a 0 , keyboard_column[1] will
 * be applied on column reads */
unsigned int keyboard_column[9];
unsigned int keyboard_row[9];

unsigned int keyboard_buffer[256];
unsigned int *keyboard_bufcur, *keyboard_buflast;

static void keyboard_poll(void *context);
static event_t *poll_event;

void keyboard_init(void) {
	unsigned int i;
	poll_event = event_new();
	poll_event->dispatch = keyboard_poll;
	keyboard_bufcur = keyboard_buflast = keyboard_buffer;
	for (i = 0; i < 8; i++) {
		keyboard_column[i] = ~0;
		keyboard_row[i] = ~0;
	}
	poll_event->at_cycle = current_cycle + 141050;
	event_queue(&xroar_ui_events, poll_event);
}

void keyboard_set_keymap(int map) {
	map %= NUM_KEYMAPS;
	running_config.keymap = map;
	switch (map) {
		default:
		case KEYMAP_DRAGON:
			memcpy(keymap, dragon_keymap, sizeof(keymap));
			break;
		case KEYMAP_COCO:
			memcpy(keymap, coco_keymap, sizeof(keymap));
			break;
	}
}

void keyboard_column_update(void) {
	unsigned int mask = PIA0.b.port_output;
	unsigned int i, row = 0x7f;
	for (i = 0; i < 8; i++) {
		if (!(mask & (1 << i))) {
			row &= keyboard_column[i];
		}
	}
	PIA0.a.port_input = (PIA0.a.port_input & 0x80) | row;
}

void keyboard_row_update(void) {
	unsigned int mask = PIA0.a.port_output;
	unsigned int i, col = 0xff;
	for (i = 0; i < 7; i++) {
		if (!(mask & (1 << i))) {
			col &= keyboard_row[i];
		}
	}
	PIA0.b.port_input = col;
}

void keyboard_queue_string(const char *s) {
	uint_least16_t c;
	while ( (c = *(s++)) ) {
		*(keyboard_buflast++) = (~c)&0x80; /* shift/unshift */
		*(keyboard_buflast++) = c & 0x7f;
		*(keyboard_buflast++) = (c & 0x7f) | 0x80;
	}
	*(keyboard_buflast++) = 0x80; /* unshift */
}

void keyboard_queue(uint_least16_t c) {
	int shift_state = keyboard_column[keymap[0].col] & (1<<keymap[0].row);
	switch (c>>8) {
		case 1:
			*(keyboard_buflast++) = 0;  /* shift */
			break;
		case 2:
			*(keyboard_buflast++) = 0x80;  /* unshift */
			break;
		case 3:
			*(keyboard_buflast++) = 0;     /* shift */
			*(keyboard_buflast++) = 0x0c;  /* clear */
			break;
		default:
			break;
	}
	*(keyboard_buflast++) = c & 0x7f;
	*(keyboard_buflast++) = (c & 0x7f) | 0x80;
	if ((c>>8) == 3) *(keyboard_buflast++) = 0x8c;  /* unclear */
	*(keyboard_buflast++) = shift_state ? 0x80 : 0; /* last shift state */
}

static void keyboard_poll(void *context) {
	(void)context;
	if (KEYBOARD_HASQUEUE) {
		unsigned int k;
		KEYBOARD_DEQUEUE(k);
		if (k & 0x80) {
			KEYBOARD_RELEASE(k & 0x7f);
		} else {
			KEYBOARD_PRESS(k);
		}
	}
	if (KEYBOARD_HASQUEUE) {
		poll_event->at_cycle += OSCILLATOR_RATE / 50;
		event_queue(&xroar_ui_events, poll_event);
	}
}
