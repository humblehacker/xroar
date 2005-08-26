/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2005  Ciaran Anscomb
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

#include <gpstdlib.h>

#include "xroar.h"
#include "video.h"
#include "types.h"

extern Sprite copyright_bin;

void GpMain(void *arg) {
	(void)arg;  /* unused */
	SPEED_FAST;

	xroar_getargs(1, NULL);
	xroar_init();
	video_module->blit(198, 204, &copyright_bin);
	//xroar_reset(RESET_HARD);
	xroar_mainloop();
}
