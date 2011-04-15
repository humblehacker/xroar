/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2011  Ciaran Anscomb
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

#include <stdlib.h>

#include "types.h"
#include "module.h"

extern VideoModule video_null_module;
static VideoModule *null_video_module_list[] = {
	&video_null_module,
	NULL
};

static KeyboardModule keyboard_null_module;
static KeyboardModule *null_keyboard_module_list[] = {
	&keyboard_null_module,
	NULL
};

UIModule ui_null_module = {
	.common = { .name = "null", .description = "No UI" },
	.video_module_list = null_video_module_list,
	.keyboard_module_list = null_keyboard_module_list,
};

static KeyboardModule keyboard_null_module = {
	.common = { .name = "null", .description = "No keyboard" },
};