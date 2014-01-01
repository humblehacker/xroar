/*  Copyright 2003-2014 Ciaran Anscomb
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

#include <stdio.h>
#include <stdlib.h>

#ifdef HAVE_SDL
# include <SDL.h>
#endif

#include "module.h"
#include "xroar.h"
#include "logging.h"

int main(int argc, char **argv) {
	atexit(xroar_shutdown);
	if (!xroar_init(argc, argv))
		exit(EXIT_FAILURE);
	if (ui_module->run) {
		ui_module->run();
	} else {
		while (xroar_run())
			;
	}
	return 0;
}
