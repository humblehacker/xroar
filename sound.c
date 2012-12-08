/*  Copyright 2003-2012 Ciaran Anscomb
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

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include "portalib/glib.h"

#include "events.h"
#include "logging.h"
#include "machine.h"
#include "mc6821.h"
#include "module.h"
#include "sound.h"
#include "tape.h"
#include "xroar.h"

union sample_t {
	uint8_t as_int8;
	uint16_t as_int16;
	float as_float;
};

static int format;
static int num_channels;
static void *buffer[2] = { NULL, NULL };
static int num_buffers;
static int buffer_num;
static int buffer_size;
static int sample_num;

static union sample_t last_sample;
static event_ticks last_cycle;
static int cycles_per_sample;
static int cycles_per_frame;
static int volume;

static void flush_frame(void *);
static struct event flush_event;

void *sound_init(int sample_rate, int channels, int fmt, int frame_size) {
	uint16_t test = 0x0123;
	int size;
	int big_endian = (*(uint8_t *)(&test) == 0x01);
	int fmt_big_endian = 1;

	if (fmt == SOUND_FMT_S16_BE) {
		fmt_big_endian = 1;
		if (big_endian) {
			fmt = SOUND_FMT_S16_HE;
		} else {
			fmt = SOUND_FMT_S16_SE;
		}
	} else if (fmt == SOUND_FMT_S16_LE) {
		fmt_big_endian = 0;
		if (big_endian) {
			fmt = SOUND_FMT_S16_SE;
		} else {
			fmt = SOUND_FMT_S16_HE;
		}
	} else if (fmt == SOUND_FMT_S16_HE) {
		fmt_big_endian = big_endian;
	} else if (fmt == SOUND_FMT_S16_SE) {
		fmt_big_endian = !big_endian;
	}

	LOG_DEBUG(2, "\t");
	switch (fmt) {
	case SOUND_FMT_U8:
		size = 1;
		last_sample.as_int8 = 0x80;
		LOG_DEBUG(2, "8-bit unsigned, ");
		break;
	case SOUND_FMT_S8:
		size = 1;
		last_sample.as_int8 = 0x00;
		LOG_DEBUG(2, "8-bit signed, ");
		break;
	case SOUND_FMT_S16_HE:
	case SOUND_FMT_S16_SE:
		size = 2;
		last_sample.as_int16 = 0x00;
		LOG_DEBUG(2, "16-bit signed %s-endian, ", fmt_big_endian ? "big" : "little" );
		break;
	case SOUND_FMT_FLOAT:
		size = sizeof(float);
		last_sample.as_float = (float)(-64 * volume) / 65536.;
		LOG_DEBUG(2, "Floating point, ");
		break;
	case SOUND_FMT_NULL:
		LOG_DEBUG(2, "No audio\n");
		break;
	default:
		return NULL;
	}
	if (fmt != SOUND_FMT_NULL) {
		switch (channels) {
		case 1: LOG_DEBUG(2, "mono, "); break;
		case 2: LOG_DEBUG(2, "stereo, "); break;
		default: LOG_DEBUG(2, "%d channel, ", channels); break;
		}
		LOG_DEBUG(2, "%dHz\n", sample_rate);
		buffer[0] = g_realloc(buffer[0], frame_size * channels * size);
	}

	buffer_size = frame_size * channels;
	num_buffers = 1;
	buffer_num = 0;
	format = fmt;
	num_channels = channels;
	cycles_per_sample = OSCILLATOR_RATE / sample_rate;
	cycles_per_frame = cycles_per_sample * frame_size;
	last_cycle = event_current_tick;

	sound_silence();

	event_init(&flush_event, flush_frame, NULL);
	flush_event.at_tick = event_current_tick + cycles_per_frame;
	event_queue(&MACHINE_EVENT_LIST, &flush_event);

	return buffer[0];
}

void sound_set_volume(int v) {
	if (v < 0) v = 0;
	if (v > 100) v = 100;
	volume = (256 * v) / 100;
}

/* within sound_update(), this loop is included for each sample format */
#define fill_buffer(type,member) do { \
		while ((int)(event_current_tick - last_cycle) > 0) { \
			for (i = num_channels; i; i--) \
				((type *)buffer[buffer_num])[sample_num++] = last_sample.member; \
			last_cycle += cycles_per_sample; \
			if (sample_num >= buffer_size) { \
				sound_module->flush_frame(buffer[buffer_num]); \
				sample_num = 0; \
				buffer_num = (buffer_num + 1) % num_buffers; \
			} \
		} \
	} while (0)

/* Fill sound buffer to current point in time, call sound modules
 * update() function if buffer is full. */
void sound_update(void) {
	int i;
	switch (format) {
		case SOUND_FMT_U8:
		case SOUND_FMT_S8:
			fill_buffer(uint8_t,as_int8);
			break;
		case SOUND_FMT_S16_HE:
		case SOUND_FMT_S16_SE:
			fill_buffer(uint16_t,as_int16);
			break;
		case SOUND_FMT_FLOAT:
			fill_buffer(float,as_float);
			break;
		case SOUND_FMT_NULL:
			while ((int)(event_current_tick - last_cycle) <= 0) {
				last_cycle += cycles_per_frame;
				sound_module->flush_frame(buffer[buffer_num]);
			}
			break;
		default:
			break;
	}

	int value;
	if (!(PIA1.b.control_register & 0x08)) {
		/* Single-bit sound */
		value = (PIA_VALUE_B(PIA1) & (1<<1)) ? 0x3f : 0;
	} else {
		int source = ((PIA0.b.control_register & (1<<3)) >> 2)
		             | ((PIA0.a.control_register & (1<<3)) >> 3);
		switch (source) {
			case 0:
				/* DAC output */
				value = (PIA_VALUE_A(PIA1) & 0xfc) >> 1;
				break;
			case 1:
				/* Tape input */
				value = tape_audio;
				break;
			default:
				/* CART input or disabled */
				value = 0;
				break;
		}
	}
#ifndef FAST_SOUND
	if (value >= 0x4c) {
		PIA1.b.in_source |= (1<<1);
		PIA1.b.in_sink |= (1<<1);
	} else {
		PIA1.b.in_source &= ~(1<<1);
		PIA1.b.in_sink &= ~(1<<1);
	}
#endif


	switch (format) {
	case SOUND_FMT_U8:
		last_sample.as_int8 = ((value * volume) >> 8) ^ 0x80;
		break;
	case SOUND_FMT_S8:
		last_sample.as_int8 = (value * volume) >> 8;
		break;
	case SOUND_FMT_S16_HE:
		last_sample.as_int16 = value * volume;
		break;
	case SOUND_FMT_S16_SE:
		value *= volume;
		last_sample.as_int16 = (value & 0xff) << 8 | ((value >> 8) & 0xff);
		break;
	case SOUND_FMT_FLOAT:
		last_sample.as_float = (float)((value-64) * volume) / 65536.;
		break;
	default:
		break;
	}
}

void sound_silence(void) {
	sound_render_silence(buffer[0], buffer_size);
	if (num_buffers > 1)
		sound_render_silence(buffer[1], buffer_size);
}

void sound_render_silence(void *buf, int samples) {
	int i;
	for (i = 0; i < samples; i++) {
		switch (format) {
		case SOUND_FMT_U8:
		case SOUND_FMT_S8:
			((uint8_t *)buf)[i] = last_sample.as_int8;
			break;
		case SOUND_FMT_S16_HE:
		case SOUND_FMT_S16_SE:
			((uint16_t *)buf)[i] = last_sample.as_int16;
			break;
		case SOUND_FMT_FLOAT:
			((float *)buf)[i] = last_sample.as_float;
			break;
		default:
			break;
		}
	}
}

static void flush_frame(void *data) {
	(void)data;
	sound_update();
	flush_event.at_tick += cycles_per_frame;
	event_queue(&MACHINE_EVENT_LIST, &flush_event);
}
