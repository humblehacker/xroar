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

// For strsep()
#define _DEFAULT_SOURCE
#define _BSD_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <SDL.h>

#include "array.h"
#include "c-strcase.h"
#include "pl-string.h"
#include "xalloc.h"

#include "dkbd.h"
#include "joystick.h"
#include "keyboard.h"
#include "logging.h"
#include "module.h"
#include "printer.h"
#include "xroar.h"

#include "sdl/common.h"

struct sym_dkey_mapping {
	SDLKey sym;
	int8_t dkey;
	_Bool priority;  // key overrides unicode translation
};

struct keymap {
	const char *name;
	const char *description;
	int num_mappings;
	struct sym_dkey_mapping *mappings;
};

#include "keyboard_sdl_mappings.c"

static _Bool control = 0, shift = 0;
static _Bool noratelimit_latch = 0;

static int8_t sym_to_dkey[SDLK_LAST];
static _Bool sym_priority[SDLK_LAST];

/* Track which unicode value was last generated by key presses (SDL only
 * guarantees to fill in the unicode field on key presses, not releases). */
static unsigned unicode_last_keysym[SDLK_LAST];

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static struct joystick_axis *configure_axis(char *, unsigned);
static struct joystick_button *configure_button(char *, unsigned);
static void unmap_axis(struct joystick_axis *axis);
static void unmap_button(struct joystick_button *button);

struct joystick_interface sdl_js_if_keyboard = {
	.name = "keyboard",
	.configure_axis = configure_axis,
	.configure_button = configure_button,
	.unmap_axis = unmap_axis,
	.unmap_button = unmap_button,
};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

struct axis {
	SDLKey key0, key1;
	unsigned value;
};

struct button {
	SDLKey key;
	_Bool value;
};

#define MAX_AXES (4)
#define MAX_BUTTONS (4)

static struct axis *enabled_axis[MAX_AXES];
static struct button *enabled_button[MAX_BUTTONS];

/* Default host key mappings likely to be common across all keyboard types. */

static struct sym_dkey_mapping sym_dkey_default[] = {
	// Common
	{ SDLK_ESCAPE, DSCAN_BREAK, 1 },
	{ SDLK_RETURN, DSCAN_ENTER, 0 },
	{ SDLK_HOME, DSCAN_CLEAR, 1 },
	{ SDLK_LSHIFT, DSCAN_SHIFT, 1 },
	{ SDLK_RSHIFT, DSCAN_SHIFT, 1 },
	{ SDLK_SPACE, DSCAN_SPACE, 0 },
	{ SDLK_F1, DSCAN_F1, 1 },
	{ SDLK_F2, DSCAN_F2, 1 },

	// Not so common
	{ SDLK_BREAK, DSCAN_BREAK, 1 },
	{ SDLK_CLEAR, DSCAN_CLEAR, 1 },

	// Cursor keys
	{ SDLK_UP, DSCAN_UP, 1 },
	{ SDLK_DOWN, DSCAN_DOWN, 1 },
	{ SDLK_LEFT, DSCAN_LEFT, 1 },
	{ SDLK_RIGHT, DSCAN_RIGHT, 1 },
	{ SDLK_BACKSPACE, DSCAN_LEFT, 1 },
	{ SDLK_DELETE, DSCAN_LEFT, 1 },
	{ SDLK_TAB, DSCAN_RIGHT, 1 },

	// Keypad
	{ SDLK_KP_MULTIPLY, DSCAN_COLON, 1 },
	{ SDLK_KP_MINUS, DSCAN_MINUS, 1 },
	{ SDLK_KP_PLUS, DSCAN_SEMICOLON, 1 },
	{ SDLK_KP_PERIOD, DSCAN_FULL_STOP, 1 },
	{ SDLK_KP_DIVIDE, DSCAN_SLASH, 1 },
	{ SDLK_KP_ENTER, DSCAN_ENTER, 0 },
};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static void map_keyboard(struct keymap *keymap) {
	/* First clear the table and map obvious keys */
	for (int i = 0; i < SDLK_LAST; i++) {
		sym_to_dkey[i] = DSCAN_INVALID;
		sym_priority[i] = 0;
	}
	for (unsigned i = 0; i < ARRAY_N_ELEMENTS(sym_dkey_default); i++) {
		sym_to_dkey[sym_dkey_default[i].sym] = sym_dkey_default[i].dkey;
		sym_priority[sym_dkey_default[i].sym] = sym_dkey_default[i].priority;
	}
	for (int i = 0; i <= 9; i++) {
		sym_to_dkey[SDLK_0 + i] = DSCAN_0 + i;
		sym_to_dkey[SDLK_KP0 + i] = DSCAN_0 + i;
	}
	for (int i = 0; i <= 25; i++)
		sym_to_dkey[SDLK_a + i] = DSCAN_A + i;

	for (int i = 0; i < SDLK_LAST; i++)
		unicode_last_keysym[i] = 0;
	if (keymap == NULL)
		return;
	int num_mappings = keymap->num_mappings;
	struct sym_dkey_mapping *mappings = keymap->mappings;
	if (!mappings)
		return;
	for (int i = 0; i < num_mappings; i++) {
		sym_to_dkey[mappings[i].sym] = mappings[i].dkey;
		sym_priority[mappings[i].sym] = mappings[i].priority;
	}
}

void sdl_keyboard_init(void) {
	const char *keymap_option = xroar_cfg.keymap;
	struct keymap *selected_keymap = &keymaps[0];
	if (keymap_option) {
		if (0 == strcmp(keymap_option, "help")) {
			for (unsigned i = 0; i < ARRAY_N_ELEMENTS(keymaps); i++) {
				if (keymaps[i].description)
					printf("\t%-10s %s\n", keymaps[i].name, keymaps[i].description);
			}
			exit(EXIT_SUCCESS);
		}
		for (unsigned i = 0; i < ARRAY_N_ELEMENTS(keymaps); i++) {
			if (0 == strcmp(keymap_option, keymaps[i].name)) {
				selected_keymap = &keymaps[i];
				LOG_DEBUG(1, "\tSelecting '%s' keymap\n",keymap_option);
			}
		}
	}
	map_keyboard(selected_keymap);
	SDL_EnableUNICODE(xroar_cfg.kbd_translate);

	for (unsigned i = 0; i < MAX_AXES; i++)
		enabled_axis[i] = NULL;
	for (unsigned i = 0; i < MAX_BUTTONS; i++)
		enabled_button[i] = NULL;
}

void sdl_keyboard_set_translate(_Bool enabled) {
	SDL_EnableUNICODE(enabled ? SDL_TRUE : SDL_FALSE);
}

static void emulator_command(SDLKey sym) {
	switch (sym) {
	case SDLK_1: case SDLK_2: case SDLK_3: case SDLK_4:
		if (shift) {
			xroar_new_disk(sym - SDLK_1);
		} else {
			xroar_insert_disk(sym - SDLK_1);
		}
		break;
	case SDLK_5: case SDLK_6: case SDLK_7: case SDLK_8:
		if (shift) {
			xroar_set_write_back(1, sym - SDLK_5, XROAR_NEXT);
		} else {
			xroar_set_write_enable(1, sym - SDLK_5, XROAR_NEXT);
		}
		break;
	case SDLK_a:
		xroar_set_cross_colour(1, XROAR_NEXT);
		break;
	case SDLK_q:
		xroar_quit();
		break;
	case SDLK_e:
		xroar_toggle_cart();
		break;
	case SDLK_f:
		xroar_set_fullscreen(1, XROAR_NEXT);
		break;
	case SDLK_h:
		if (shift)
			xroar_set_pause(1, XROAR_NEXT);
		break;
	case SDLK_i:
		if (shift)
			xroar_set_vdg_inverted_text(1, XROAR_NEXT);
		else
			xroar_run_file(NULL);
		break;
	case SDLK_j:
		if (shift) {
			xroar_swap_joysticks(1);
		} else {
			xroar_cycle_joysticks(1);
		}
		break;
	case SDLK_k:
		xroar_set_keymap(1, XROAR_NEXT);
		break;
	case SDLK_l:
		if (shift) {
			xroar_run_file(NULL);
		} else {
			xroar_load_file(NULL);
		}
		break;
	case SDLK_m:
		xroar_set_machine(1, XROAR_NEXT);
		break;
	case SDLK_p:
		if (shift)
			printer_flush(printer_interface);
		break;
	case SDLK_r:
		if (shift)
			xroar_hard_reset();
		else
			xroar_soft_reset();
		break;
	case SDLK_s:
		xroar_save_snapshot();
		break;
	case SDLK_w:
		xroar_select_tape_output();
		break;
#ifdef TRACE
	case SDLK_v:
		xroar_set_trace(XROAR_NEXT);
		break;
#endif
	case SDLK_z: /* running out of letters... */
		xroar_set_kbd_translate(1, XROAR_NEXT);
		break;
	case SDLK_MINUS:
		sdl_zoom_out();
		break;
	case SDLK_EQUALS:
		sdl_zoom_in();
		break;
	default:
		break;
	}
	return;
}

void sdl_keypress(SDL_keysym *keysym) {
	SDLKey sym = keysym->sym;
	if (sym == SDLK_UNKNOWN)
		return;
	if (sym >= SDLK_LAST)
		return;

	for (unsigned i = 0; i < MAX_AXES; i++) {
		if (enabled_axis[i]) {
			if (sym == enabled_axis[i]->key0) {
				enabled_axis[i]->value = 0;
				return;
			}
			if (sym == enabled_axis[i]->key1) {
				enabled_axis[i]->value = 255;
				return;
			}
		}
	}
	for (unsigned i = 0; i < MAX_BUTTONS; i++) {
		if (enabled_button[i]) {
			if (sym == enabled_button[i]->key) {
				enabled_button[i]->value = 1;
				return;
			}
		}
	}

	if (sym == SDLK_LSHIFT || sym == SDLK_RSHIFT) {
		shift = 1;
		KEYBOARD_PRESS_SHIFT(keyboard_interface);
		return;
	}
	if (sym == SDLK_LCTRL || sym == SDLK_RCTRL) {
		control = 1;
		return;
	}
	if (sym == SDLK_F11) {
		xroar_set_fullscreen(1, XROAR_NEXT);
		return;
	}
	if (sym == SDLK_F12) {
		if (shift) {
			noratelimit_latch = !noratelimit_latch;
			if (noratelimit_latch) {
				xroar_noratelimit = 1;
				xroar_frameskip = 10;
			} else {
				xroar_noratelimit = 0;
				xroar_frameskip = xroar_cfg.frameskip;
			}
		} else if (!noratelimit_latch) {
			xroar_noratelimit = 1;
			xroar_frameskip = 10;
		}
	}
	if (sym == SDLK_PAUSE) {
		xroar_set_pause(1, XROAR_NEXT);
		return;
	}
	if (control) {
		emulator_command(sym);
		return;
	}

	if (sym_priority[sym]) {
		if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
			printf("sdl press   code %6d   sym %6d   %s\n", keysym->scancode, sym, SDL_GetKeyName(sym));
		keyboard_press(keyboard_interface, sym_to_dkey[sym]);
		return;
	}

	if (xroar_cfg.kbd_translate) {
		unsigned unicode;
		unicode = keysym->unicode;
		if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
			printf("sdl press   code %6d   sym %6d   unicode %08x   %s\n", keysym->scancode, sym, unicode, SDL_GetKeyName(sym));
		/* shift + backspace -> erase line */
		if (shift && (unicode == 0x08 || unicode == 0x7f))
			unicode = DKBD_U_ERASE_LINE;
		/* shift + enter -> caps lock */
		if (sym_to_dkey[sym] == DSCAN_ENTER)
			unicode = shift ? DKBD_U_CAPS_LOCK : 0x0d;
		/* shift + clear -> pause output */
		if (sym_to_dkey[sym] == DSCAN_SPACE)
			unicode = shift ? DKBD_U_PAUSE_OUTPUT : 0x20;
		unicode_last_keysym[sym] = unicode;
		keyboard_unicode_press(keyboard_interface, unicode);
		return;
	}

	if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
		printf("sdl press   code %6d   sym %6d   %s\n", keysym->scancode, sym, SDL_GetKeyName(sym));
	int8_t dkey = sym_to_dkey[sym];
	keyboard_press(keyboard_interface, dkey);
}

void sdl_keyrelease(SDL_keysym *keysym) {
	SDLKey sym = keysym->sym;
	if (sym == SDLK_UNKNOWN)
		return;
	if (sym >= SDLK_LAST)
		return;

	for (unsigned i = 0; i < MAX_AXES; i++) {
		if (enabled_axis[i]) {
			if (sym == enabled_axis[i]->key0) {
				if (enabled_axis[i]->value < 129)
					enabled_axis[i]->value = 129;
				return;
			}
			if (sym == enabled_axis[i]->key1) {
				if (enabled_axis[i]->value > 130)
					enabled_axis[i]->value = 130;
				return;
			}
		}
	}
	for (unsigned i = 0; i < MAX_BUTTONS; i++) {
		if (enabled_button[i]) {
			if (sym == enabled_button[i]->key) {
				enabled_button[i]->value = 0;
				return;
			}
		}
	}

	if (sym == SDLK_LSHIFT || sym == SDLK_RSHIFT) {
		shift = 0;
		KEYBOARD_RELEASE_SHIFT(keyboard_interface);
		return;
	}
	if (sym == SDLK_LCTRL || sym == SDLK_RCTRL) { control = 0; return; }
	if (sym == SDLK_F12) {
		if (!noratelimit_latch) {
			xroar_noratelimit = 0;
			xroar_frameskip = xroar_cfg.frameskip;
		}
	}

	if (sym_priority[sym]) {
		if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
			printf("sdl release code %6d   sym %6d   %s\n", keysym->scancode, sym, SDL_GetKeyName(sym));
		keyboard_release(keyboard_interface, sym_to_dkey[sym]);
		return;
	}

	if (xroar_cfg.kbd_translate) {
		unsigned unicode;
		if (sym >= SDLK_LAST)
			return;
		unicode = unicode_last_keysym[sym];
		if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
			printf("sdl release code %6d   sym %6d   unicode %08x   %s\n", keysym->scancode, sym, unicode, SDL_GetKeyName(sym));
		keyboard_unicode_release(keyboard_interface, unicode);
		/* Put shift back the way it should be */
		if (shift)
			KEYBOARD_PRESS_SHIFT(keyboard_interface);
		else
			KEYBOARD_RELEASE_SHIFT(keyboard_interface);
		return;
	}

	if (xroar_cfg.debug_ui & XROAR_DEBUG_UI_KBD_EVENT)
		printf("sdl release code %6d   sym %6d   %s\n", keysym->scancode, sym, SDL_GetKeyName(sym));
	int8_t dkey = sym_to_dkey[sym];
	keyboard_release(keyboard_interface, dkey);
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static unsigned read_axis(struct axis *a) {
	return a->value;
}

static _Bool read_button(struct button *b) {
	return b->value;
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static SDLKey get_key_by_name(const char *name) {
	if (isdigit(name[0]))
		return strtol(name, NULL, 0);
	for (SDLKey i = SDLK_FIRST; i < SDLK_LAST; i++) {
		if (0 == c_strcasecmp(name, SDL_GetKeyName(i)))
			return i;
	}
	return SDLK_UNKNOWN;
}

static struct joystick_axis *configure_axis(char *spec, unsigned jaxis) {
	SDLKey key0, key1;
	// sensible defaults
	if (jaxis == 0) {
		key0 = SDLK_LEFT;
		key1 = SDLK_RIGHT;
	} else {
		key0 = SDLK_UP;
		key1 = SDLK_DOWN;
	}
	char *a0 = NULL;
	char *a1 = NULL;
	if (spec) {
		a0 = strsep(&spec, ",");
		a1 = spec;
	}
	if (a0 && *a0)
		key0 = get_key_by_name(a0);
	if (a1 && *a1)
		key1 = get_key_by_name(a1);
	struct axis *axis_data = xmalloc(sizeof(*axis_data));
	axis_data->key0 = key0;
	axis_data->key1 = key1;
	axis_data->value = 127;
	struct joystick_axis *axis = xmalloc(sizeof(*axis));
	axis->read = (js_read_axis_func)read_axis;
	axis->data = axis_data;
	for (unsigned i = 0; i < MAX_AXES; i++) {
		if (!enabled_axis[i]) {
			enabled_axis[i] = axis_data;
			break;
		}
	}
	return axis;
}

static struct joystick_button *configure_button(char *spec, unsigned jbutton) {
	SDLKey key = (jbutton == 0) ? SDLK_LALT : SDLK_UNKNOWN;
	if (spec && *spec)
		key = get_key_by_name(spec);
	struct button *button_data = xmalloc(sizeof(*button_data));
	button_data->key = key;
	button_data->value = 0;
	struct joystick_button *button = xmalloc(sizeof(*button));
	button->read = (js_read_button_func)read_button;
	button->data = button_data;
	for (unsigned i = 0; i < MAX_BUTTONS; i++) {
		if (!enabled_button[i]) {
			enabled_button[i] = button_data;
			break;
		}
	}
	return button;
}

static void unmap_axis(struct joystick_axis *axis) {
	if (!axis)
		return;
	for (unsigned i = 0; i < MAX_AXES; i++) {
		if (axis->data == enabled_axis[i]) {
			enabled_axis[i] = NULL;
		}
	}
	free(axis->data);
	free(axis);
}

static void unmap_button(struct joystick_button *button) {
	if (!button)
		return;
	for (unsigned i = 0; i < MAX_BUTTONS; i++) {
		if (button->data == enabled_button[i]) {
			enabled_button[i] = NULL;
		}
	}
	free(button->data);
	free(button);
}
