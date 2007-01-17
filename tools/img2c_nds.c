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

#include <stdio.h>
#include <stdlib.h>
#include <SDL.h>
#include <SDL_image.h>

# define MAPCOLOUR(r,g,b) ((1<<15)|((r)>>3)|(((g)>>3)<<5)|(((b)>>3)<<10))

Uint32 getpixel(SDL_Surface *surface, int x, int y);

int main(int argc, char **argv) {
	Uint32 p;
	Uint8 r,g,b;
	int x, y, xres, yres;
	SDL_Surface *in;
	int multiple, ino;
	if (argc < 3) {
		printf("Usage: %s name infile ...\n", argv[0]);
		exit(1);
	}
	multiple = (argc > 3);
	in = IMG_Load(argv[2]);
	xres = in->w; yres = in->h;
	printf("/* This file is automatically generated by img2c. */\n\n");
	printf("#include \"nds/ndsgfx.h\"\n#include \"types.h\"\n\n");
	printf("static uint16_t /*__attribute__ ((aligned (4)))*/ data[%d][%d] = {\n{\n", argc-2, xres*yres);
	for (ino = 3; ino <= argc; ino++) {
		for (y = 0; y < yres; y++) {
			printf("\t");
			for (x = 0; x < xres; x++) {
				SDL_LockSurface(in);
				p = getpixel(in, x, y);
				SDL_UnlockSurface(in);
				SDL_GetRGB(getpixel(in, x, y), in->format, &r, &g, &b);
				printf("0x%04x, ", MAPCOLOUR(r,g,b));
			}
			printf("\n");
		}
		SDL_FreeSurface(in);
		printf("}");
		if (ino < argc) {
			printf(",\n{\n");
			in = IMG_Load(argv[ino]);
		}
	}
	printf("\n};\n\n");
	if (multiple) {
		printf("Sprite %s[%d] = {\n", argv[1], argc-2);
		for (ino = 3; ino <= argc; ino++) {
			printf("\t{ %d, %d, data[%d] },\n",
					xres, yres, ino-3);
		}
		printf("};\n");
	} else {
		printf("Sprite %s = { %d, %d, data[0] };\n",
				argv[1], xres, yres);
	}
	return 0;
}

Uint32 getpixel(SDL_Surface *surface, int x, int y) {
	int bpp = surface->format->BytesPerPixel;
	Uint8 *p = (Uint8 *)surface->pixels + y * surface->pitch + x * bpp;

	switch(bpp) {
		case 1: return *p;
		case 2: return *(Uint16 *)p;
		case 3:
			if (SDL_BYTEORDER == SDL_BIG_ENDIAN)
				return p[0] << 16 | p[1] << 8 | p[2];
			else
				return p[0] | p[1] << 8 | p[2] << 16;
		case 4: return *(Uint32 *)p;
		default: return 0;
	}
}
