/*  Copyright 2003-2017 Ciaran Anscomb
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

#include "vo.h"

static void no_op(struct vo_module *vo);
static void no_op_render(struct vo_module *vo, uint8_t const *scanline_data,
			 struct ntsc_burst *burst, unsigned phase);

struct vo_module vo_null_module = {
	.common = { .name = "null", .description = "No video" },
	.vsync = no_op,
	.render_scanline = no_op_render,
};

static void no_op(struct vo_module *vo) {
	(void)vo;
}

static void no_op_render(struct vo_module *vo, uint8_t const *scanline_data,
			 struct ntsc_burst *burst, unsigned phase) {
	(void)vo;
	(void)scanline_data;
	(void)burst;
	(void)phase;
}
