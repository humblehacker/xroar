/*  Copyright 2003-2013 Ciaran Anscomb
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

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <alsa/asoundlib.h>

#include "pl_glib.h"

#include "events.h"
#include "logging.h"
#include "machine.h"
#include "module.h"
#include "sound.h"
#include "xroar.h"

static _Bool init(void);
static void shutdown(void);
static void *write_buffer(void *buffer);

SoundModule sound_alsa_module = {
	.common = { .name = "alsa", .description = "ALSA audio",
		    .init = init, .shutdown = shutdown },
	.write_buffer = write_buffer,
};

static unsigned int sample_rate;
static snd_pcm_t *pcm_handle;
static snd_pcm_uframes_t period_nframes;
static void *audio_buffer;

static _Bool init(void) {
	const char *device = xroar_cfg.ao_device ? xroar_cfg.ao_device : "default";
	int err;
	snd_pcm_hw_params_t *hw_params;
	snd_pcm_format_t format = SND_PCM_FORMAT_S16;
	unsigned nchannels = 2;

	sample_rate = (xroar_cfg.ao_rate > 0) ? xroar_cfg.ao_rate : 44100;

	if ((err = snd_pcm_open(&pcm_handle, device, SND_PCM_STREAM_PLAYBACK, 0)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_malloc(&hw_params)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_any(pcm_handle, hw_params)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_set_access(pcm_handle, hw_params, SND_PCM_ACCESS_RW_INTERLEAVED)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_set_format(pcm_handle, hw_params, format)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_set_rate_near(pcm_handle, hw_params, &sample_rate, 0)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_set_channels_near(pcm_handle, hw_params, &nchannels)) < 0)
		goto failed;

	if ((err = snd_pcm_hw_params_get_period_size(hw_params, &period_nframes, NULL)) < 0)
		goto failed;

	snd_pcm_uframes_t buffer_nframes;
	if (xroar_cfg.ao_buffer_ms > 0) {
		buffer_nframes = (sample_rate * xroar_cfg.ao_buffer_ms) / 1000;
	} else if (xroar_cfg.ao_buffer_samples > 0) {
		buffer_nframes = xroar_cfg.ao_buffer_samples;
	} else {
		buffer_nframes = period_nframes * 2;
	}

	snd_pcm_hw_params_set_buffer_size_near(pcm_handle, hw_params, &buffer_nframes);

	if ((err = snd_pcm_hw_params(pcm_handle, hw_params)) < 0)
		goto failed;

	snd_pcm_hw_params_free(hw_params);

	if ((err = snd_pcm_prepare(pcm_handle)) < 0)
		goto failed;

	enum sound_fmt buffer_fmt;
	unsigned sample_size;
	switch (format) {
		case SND_PCM_FORMAT_S8:
			buffer_fmt = SOUND_FMT_S8;
			sample_size = 1;
			break;
		case SND_PCM_FORMAT_U8:
			buffer_fmt = SOUND_FMT_U8;
			sample_size = 1;
			break;
		case SND_PCM_FORMAT_S16_LE:
			buffer_fmt = SOUND_FMT_S16_LE;
			sample_size = 2;
			break;
		case SND_PCM_FORMAT_S16_BE:
			buffer_fmt = SOUND_FMT_S16_BE;
			sample_size = 2;
			break;
		default:
			LOG_WARN("Unhandled audio format.");
			goto failed;
	}
	unsigned buffer_size = period_nframes * nchannels * sample_size;
	audio_buffer = g_malloc(buffer_size);
	sound_init(audio_buffer, buffer_fmt, sample_rate, nchannels, period_nframes);
	LOG_DEBUG(2, "\t%ldms (%ld samples) buffer\n", (buffer_nframes * 1000) / sample_rate, buffer_nframes);

	/* snd_pcm_writei(pcm_handle, buffer, period_nframes); */
	return 1;
failed:
	LOG_ERROR("Failed to initialise ALSA: %s\n", snd_strerror(err));
	return 0;
}

static void shutdown(void) {
	snd_pcm_close(pcm_handle);
	g_free(audio_buffer);
}

static void *write_buffer(void *buffer) {
	if (xroar_noratelimit)
		return buffer;
	if (snd_pcm_writei(pcm_handle, buffer, period_nframes) < 0) {
		snd_pcm_prepare(pcm_handle);
		snd_pcm_writei(pcm_handle, buffer, period_nframes);
	}
	return buffer;
}
