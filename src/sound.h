/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2015  Ciaran Anscomb
 *
 *  See COPYING.GPL for redistribution conditions. */

#ifndef XROAR_SOUND_H_
#define XROAR_SOUND_H_

#include "delegate.h"

enum sound_fmt {
	SOUND_FMT_NULL,
	SOUND_FMT_U8,
	SOUND_FMT_S8,
	SOUND_FMT_S16_BE,
	SOUND_FMT_S16_LE,
	SOUND_FMT_S16_HE,  // host-endian
	SOUND_FMT_S16_SE,  // swapped-endian
	SOUND_FMT_FLOAT,
};

extern DELEGATE_T1(void, bool) sound_sbs_feedback;

void sound_init(void *buf, enum sound_fmt fmt, unsigned rate, unsigned nchannels, unsigned nframes);
void sound_set_volume(int v);

void sound_update(void);
void sound_enable_external(void);
void sound_disable_external(void);

void sound_set_sbs(_Bool enabled, _Bool level);
void sound_set_mux_enabled(_Bool enabled);
void sound_set_mux_source(unsigned source);
void sound_set_dac_level(float level);
void sound_set_tape_level(float level);
void sound_set_cart_level(float level);
void sound_set_external_left(float level);
void sound_set_external_right(float level);

#endif  /* XROAR_SOUND_H_ */
