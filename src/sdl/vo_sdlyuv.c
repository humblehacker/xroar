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

#include <SDL.h>

#include "logging.h"
#include "mc6847.h"
#include "vo.h"
#include "xroar.h"

#include "sdl/common.h"

static _Bool init(void);
static void shutdown(void);
static void alloc_colours(void);
static void vsync(void);
static void render_scanline(uint8_t const *scanline_data);
static void resize(unsigned int w, unsigned int h);
static int set_fullscreen(_Bool fullscreen);
static void update_cross_colour_phase(void);

struct vo_module vo_sdlyuv_module = {
	.common = { .name = "sdlyuv", .description = "SDL YUV overlay video",
	            .init = init, .shutdown = shutdown },
	.update_palette = alloc_colours,
	.vsync = vsync,
	.render_scanline = render_scanline,
	.resize = resize, .set_fullscreen = set_fullscreen,
	.update_cross_colour_phase = update_cross_colour_phase,
};

typedef Uint32 Pixel;
#define MAPCOLOUR(r,g,b) map_colour((r), (g), (b))
#define VIDEO_SCREENBASE ((Pixel *)overlay->pixels[0])
#define XSTEP 1
#define NEXTLINE 0
#define VIDEO_TOPLEFT (VIDEO_SCREENBASE)
#define VIDEO_VIEWPORT_YOFFSET (0)
#define LOCK_SURFACE SDL_LockYUVOverlay(overlay)
#define UNLOCK_SURFACE SDL_UnlockYUVOverlay(overlay)
#define VIDEO_MODULE_NAME vo_sdlyuv_module

static SDL_Surface *screen;
static SDL_Overlay *overlay;
static unsigned int screen_width, screen_height;
static unsigned int window_width, window_height;
static SDL_Rect dstrect;

static Uint32 map_colour(int r, int g, int b);

#include "vo_generic_ops.c"

/* The packed modes supported by SDL: */
static const Uint32 try_overlay_format[] = {
	SDL_YUY2_OVERLAY,
	SDL_UYVY_OVERLAY,
	SDL_YVYU_OVERLAY,
};
#define NUM_OVERLAY_FORMATS ((int)(sizeof(try_overlay_format)/sizeof(Uint32)))
static Uint32 overlay_format;

static _Bool init(void) {
	const SDL_VideoInfo *video_info;

	video_info = SDL_GetVideoInfo();
	screen_width = video_info->current_w;
	screen_height = video_info->current_h;
	window_width = 640;
	window_height = 480;
	vo_sdlyuv_module.is_fullscreen = !xroar_ui_cfg.fullscreen;

	if (set_fullscreen(xroar_ui_cfg.fullscreen))
		return 0;

	overlay = NULL;
	Uint32 first_successful_format = 0;
	for (int i = 0; i < NUM_OVERLAY_FORMATS; i++) {
		overlay_format = try_overlay_format[i];
		overlay = SDL_CreateYUVOverlay(1280, 240, overlay_format, screen);
		if (!overlay) {
			continue;
		}
		if (first_successful_format == 0) {
			first_successful_format = overlay_format;
		}
		if (overlay->hw_overlay == 1) {
			break;
		}
		SDL_FreeYUVOverlay(overlay);
		overlay = NULL;
	}
	if (!overlay && first_successful_format != 0) {
		/* Fall back to the first successful one, unaccelerated */
		overlay_format = first_successful_format;
		overlay = SDL_CreateYUVOverlay(1280, 240, overlay_format, screen);
	}
	if (!overlay) {
		LOG_ERROR("Failed to create SDL overlay for display: %s\n", SDL_GetError());
		return 0;
	}
	if (overlay->hw_overlay != 1) {
		LOG_WARN("Warning: SDL overlay is not hardware accelerated\n");
	}

	alloc_colours();
	vo_module->scanline = 0;
	vo_module->window_x = VDG_ACTIVE_LINE_START - 64;
	vo_module->window_y = VDG_TOP_BORDER_START + 1;
	vo_module->window_w = 640;
	vo_module->window_h = 240;

	vsync();
	return 1;
}

static void shutdown(void) {
	set_fullscreen(0);
	SDL_FreeYUVOverlay(overlay);
	/* Should not be freed by caller: SDL_FreeSurface(screen); */
}

static Uint32 map_colour(int r, int g, int b) {
	Uint32 colour;
	uint8_t *d = (uint8_t *)&colour;
	uint8_t y = 0.299*r + 0.587*g + 0.114*b;
	uint8_t u = (b-y)*0.565 + 128;
	uint8_t v = (r-y)*0.713 + 128;
	switch (overlay_format) {
	default:
	case SDL_YUY2_OVERLAY:
		d[0] = d[2] = y;
		d[1] = u;
		d[3] = v;
		break;
	case SDL_UYVY_OVERLAY:
		d[1] = d[3] = y;
		d[0] = u;
		d[2] = v;
		break;
	case SDL_YVYU_OVERLAY:
		d[0] = d[2] = y;
		d[3] = u;
		d[1] = v;
		break;
	}
	return colour;
}

static void resize(unsigned int w, unsigned int h) {
	window_width = w;
	window_height = h;
	set_fullscreen(vo_sdlyuv_module.is_fullscreen);
}

static int set_fullscreen(_Bool fullscreen) {
	unsigned int want_width, want_height;

#ifdef WINDOWS32
	/* Remove menubar if transitioning from windowed to fullscreen. */

	if (screen && !vo_sdlyuv_module.is_fullscreen && fullscreen) {
		sdl_windows32_remove_menu(screen);
	}
#endif

	if (fullscreen) {
		want_width = screen_width;
		want_height = screen_height;
	} else {
		want_width = window_width;
		want_height = window_height;
	}
	if (want_width < 320) want_width = 320;
	if (want_height < 240) want_height = 240;

	screen = SDL_SetVideoMode(want_width, want_height, 0, SDL_HWSURFACE|SDL_ANYFORMAT|(fullscreen?SDL_FULLSCREEN:SDL_RESIZABLE));
	if (screen == NULL) {
		LOG_ERROR("Failed to allocate SDL surface for display\n");
		return 1;
	}

#ifdef WINDOWS32
	sdl_windows32_set_events_window(screen);

	/* Add menubar if transitioning from fullscreen to windowed. */

	if (vo_sdlyuv_module.is_fullscreen && !fullscreen) {
		sdl_windows32_add_menu(screen);

		/* Adding the menubar will resize the *client area*, i.e., the
		 * bit SDL wants to render into. A specified geometry in this
		 * case should apply to the client area, so we need to resize
		 * again to account for this. */

		screen = SDL_SetVideoMode(want_width, want_height, 0, SDL_HWSURFACE|SDL_ANYFORMAT|SDL_RESIZABLE);

		/* Now purge any resize events this all generated from the
		 * event queue. Don't want to end up in a resize loop! */

		SDL_PumpEvents();
		SDL_Event dummy;
		while (SDL_PeepEvents(&dummy, 1, SDL_GETEVENT, SDL_EVENTMASK(SDL_VIDEORESIZE)) > 0);
	}
#endif

	SDL_WM_SetCaption("XRoar", "XRoar");

	if (fullscreen)
		SDL_ShowCursor(SDL_DISABLE);
	else
		SDL_ShowCursor(SDL_ENABLE);

	vo_sdlyuv_module.is_fullscreen = fullscreen;

	memcpy(&dstrect, &screen->clip_rect, sizeof(SDL_Rect));
	if (((float)screen->w/(float)screen->h)>(4.0/3.0)) {
		dstrect.w = (((float)screen->h/3.0)*4.0) + 0.5;
		dstrect.h = screen->h;
		dstrect.x = (screen->w - dstrect.w)/2;
		dstrect.y = 0;
	} else {
		dstrect.w = screen->w;
		dstrect.h = (((float)screen->w/4.0)*3.0) + 0.5;
		dstrect.x = 0;
		dstrect.y = (screen->h - dstrect.h)/2;
	}
	sdl_window_x = dstrect.x;
	sdl_window_y = dstrect.y;
	sdl_window_w = dstrect.w;
	sdl_window_h = dstrect.h;

	return 0;
}

static void vsync(void) {
	SDL_DisplayYUVOverlay(overlay, &dstrect);
	pixel = VIDEO_TOPLEFT + VIDEO_VIEWPORT_YOFFSET;
	vo_module->scanline = 0;
}
