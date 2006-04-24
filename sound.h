/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2006  Ciaran Anscomb
 *
 *  See COPYING for redistribution conditions. */

#ifndef __SOUND_H__
#define __SOUND_H__

#include "types.h"

typedef struct SoundModule SoundModule;
struct SoundModule {
	const char *name;
	const char *help;
	int (*init)(void);
	void (*shutdown)(void);
	void (*update)(void);
};

extern SoundModule *sound_module;

void sound_helptext(void);
void sound_getargs(int argc, char **argv);
int sound_init(void);
void sound_shutdown(void);
void sound_next(void);

#endif  /* __SOUND_H__ */
