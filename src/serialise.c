/** \file
 *
 *  \brief Serialisation and deserialisation helpers.
 *
 *  \copyright Copyright 2015-2021 Ciaran Anscomb
 *
 *  \licenseblock This file is part of XRoar, a Dragon/Tandy CoCo emulator.
 *
 *  XRoar is free software; you can redistribute it and/or modify it under the
 *  terms of the GNU General Public License as published by the Free Software
 *  Foundation, either version 3 of the License, or (at your option) any later
 *  version.
 *
 *  See COPYING.GPL for redistribution conditions.
 *
 *  \endlicenseblock
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

// Comment this out for debugging
#define SER_DEBUG(...)

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sds.h"
#include "slist.h"
#include "xalloc.h"

#include "events.h"
#include "fs.h"
#include "logging.h"
#include "serialise.h"

#ifndef SER_DEBUG
#define SER_DEBUG(...) LOG_PRINT(__VA_ARGS__)
#endif

struct ser_handle {
	FILE *fd;
	int error;

	// After reading a (TAG,LENGTH), this will contain LENGTH.  Attempts to
	// read more than this many bytes as data will cause an error.  Any
	// remaining data will be skipped when asked to read the next tag.
	size_t length;

	// Flag open tag.
	int tag_open;

	// Open tags increase, close tags (zero byte) decrease.
	int depth;
};

static void s_write_uint8(struct ser_handle *sh, int v);
static void s_write_uint16(struct ser_handle *sh, int v);
static void s_write_vuint32(struct ser_handle *sh, uint32_t v);
static void s_write_vint32(struct ser_handle *sh, int32_t v);
static void s_write(struct ser_handle *sh, const void *ptr, size_t size);
static int s_read_uint8(struct ser_handle *sh);
static int s_read_uint16(struct ser_handle *sh);
static uint32_t s_read_vuint32(struct ser_handle *sh);
static void s_read(struct ser_handle *sh, void *ptr, size_t size);
static void *s_read_new(struct ser_handle *sh, size_t size);

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

struct ser_handle *ser_open(const char *filename, enum ser_mode mode) {
	FILE *fd;
	if (mode == ser_mode_read) {
		fd = fopen(filename, "rb");
	} else if (mode == ser_mode_write) {
		fd = fopen(filename, "wb");
	} else {
		return NULL;
	}
	struct ser_handle *sh = xmalloc(sizeof(*sh));
	*sh = (struct ser_handle){0};
	sh->fd = fd;
	return sh;
}

int ser_close(struct ser_handle *sh) {
	if (!sh)
		return ser_error_bad_handle;
	int err = sh->error;
	free(sh);
	return err;
}

void ser_write_tag(struct ser_handle *sh, int tag, size_t length) {
	if (!sh)
		return;
	if (tag < 0) {
		ser_set_error(sh, ser_error_bad_tag);
		return;
	}
	SER_DEBUG("ser_write_tag(%d, %zd)\n", tag, length);
	s_write_vuint32(sh, tag);
	s_write_vuint32(sh, length);
	sh->length = length;
}

void ser_write_close_tag(struct ser_handle *sh) {
	if (!sh)
		return;
	// XXX handle this case more gracefully (e.g. write padding bytes)
	assert(sh->length == 0);
	SER_DEBUG("ser_write_close_tag()\n");
	s_write_vint32(sh, 0);
}

int ser_read_tag(struct ser_handle *sh) {
	if (!sh || sh->error)
		return -1;

	// Skip any data remaining from previous read
	if (sh->length) {
		SER_DEBUG("ser_read_tag(): skipping %zd bytes\n", sh->length);
		if (fseek(sh->fd, sh->length, SEEK_CUR) < 0) {
			ser_set_error(sh, ser_error_file_io);
			return -1;
		}
		sh->length = 0;
	}

	int tag = s_read_vuint32(sh);
	SER_DEBUG("ser_read_tag(): %d\n", tag);

	if (tag == 0) {
		// Closing tag (special value zero).
		if (sh->tag_open) {
			// Open tag = not nested, don't reduce depth, return
			// next tag instead.
			sh->tag_open = 0;
			return ser_read_tag(sh);
		}
		sh->depth--;
		return 0;
	}

	if (sh->tag_open) {
		sh->depth++;
	}
	sh->tag_open = 1;

	sh->length = s_read_vuint32(sh);
	if (sh->error) {
		return -1;
	}

	return tag;
}

size_t ser_data_length(struct ser_handle *sh) {
	assert(sh != NULL);
	return sh->length;
}

int ser_eof(struct ser_handle *sh) {
	assert(sh != NULL);
	return feof(sh->fd);
}

int ser_error(struct ser_handle *sh) {
	if (!sh)
		return ser_error_bad_handle;
	return sh->error;
}

void ser_set_error(struct ser_handle *sh, int error) {
	assert(sh != NULL);
	// Don't hide earlier errors:
	if (sh->error)
		return;
	sh->error = error;
}

const char *ser_errstr(struct ser_handle *sh) {
	if (!sh)
		return "bad handle";
	switch (sh->error) {
	case ser_error_file_io: return "i/o error";
	case ser_error_bad_tag: return "bad tag";
	case ser_error_format: return "format error";
	case ser_error_bad_handle: return "bad handle";
	case ser_error_system: return "internal error";
	case ser_error_type: return "type error";
	default: return "unknown error";
	}
}


// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

// Helpers for the helpers.  Wrap filesystem functions while handling error
// codes.

static void s_write_uint8(struct ser_handle *sh, int v) {
	if (sh->error)
		return;
	if (fs_write_uint8(sh->fd, v) != 1)
		ser_set_error(sh, ser_error_file_io);
}

static void s_write_uint16(struct ser_handle *sh, int v) {
	if (sh->error)
		return;
	if (fs_write_uint16(sh->fd, v) != 2)
		ser_set_error(sh, ser_error_file_io);
}

static void s_write_vuint32(struct ser_handle *sh, uint32_t v) {
	if (sh->error)
		return;
	if (fs_write_vuint32(sh->fd, v) <= 0)
		ser_set_error(sh, ser_error_file_io);
}

static void s_write_vint32(struct ser_handle *sh, int32_t v) {
	if (sh->error)
		return;
	if (fs_write_vint32(sh->fd, v) <= 0)
		ser_set_error(sh, ser_error_file_io);
}

static void s_write(struct ser_handle *sh, const void *ptr, size_t size) {
	if (sh->error)
		return;
	if (fwrite(ptr, 1, size, sh->fd) != size)
		ser_set_error(sh, ser_error_file_io);
}

static int s_read_uint8(struct ser_handle *sh) {
	if (sh->error)
		return 0;
	int r = fs_read_uint8(sh->fd);
	if (r < 0)
		ser_set_error(sh, ser_error_file_io);
	return r;
}

static int s_read_uint16(struct ser_handle *sh) {
	if (sh->error)
		return 0;
	int r = fs_read_uint16(sh->fd);
	if (r < 0)
		ser_set_error(sh, ser_error_file_io);
	return r;
}

static uint32_t s_read_vuint32(struct ser_handle *sh) {
	if (sh->error)
		return 0;
	int nread = 0;
	uint32_t r = fs_read_vuint32(sh->fd, &nread);
	if (nread < 0)
		ser_set_error(sh, ser_error_file_io);
	return r;
}

static void s_read(struct ser_handle *sh, void *ptr, size_t size) {
	if (sh->error)
		return;
	if (fread(ptr, 1, size, sh->fd) != size)
		ser_set_error(sh, ser_error_file_io);
}

static void *s_read_new(struct ser_handle *sh, size_t size) {
	if (sh->error)
		return NULL;
	void *ptr = xmalloc(size);
	s_read(sh, ptr, size);
	return ptr;
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

// Write helpers.  Writes out TAG,LENGTH,DATA followed by a closing tag.

void ser_write_int8(struct ser_handle *sh, int tag, int8_t v) {
	ser_write_uint8(sh, tag, (uint8_t)v);
}

void ser_write_uint8(struct ser_handle *sh, int tag, uint8_t v) {
	if (!sh)
		return;
	ser_write_tag(sh, tag, 1);
	s_write_uint8(sh, v);
	sh->length--;
	ser_write_close_tag(sh);
}

void ser_write_int16(struct ser_handle *sh, int tag, int16_t v) {
	ser_write_uint16(sh, tag, (uint16_t)v);
}

void ser_write_uint16(struct ser_handle *sh, int tag, uint16_t v) {
	if (!sh)
		return;
	ser_write_tag(sh, tag, 2);
	s_write_uint16(sh, v);
	sh->length -= 2;
	ser_write_close_tag(sh);
}

void ser_write_vint32(struct ser_handle *sh, int tag, int v) {
	if (!sh)
		return;

	size_t length = fs_sizeof_vint32(v);
	ser_write_tag(sh, tag, length);
	s_write_vint32(sh, v);
	sh->length -= length;
	ser_write_close_tag(sh);
}

void ser_write_vuint32(struct ser_handle *sh, int tag, uint32_t v) {
	if (!sh)
		return;

	size_t length = fs_sizeof_vuint32(v);
	ser_write_tag(sh, tag, length);
	s_write_vuint32(sh, v);
	sh->length -= length;
	ser_write_close_tag(sh);
}

void ser_write_string(struct ser_handle *sh, int tag, const char *s) {
	size_t length = s ? strlen(s) : 0;
	ser_write(sh, tag, s, length);
}

void ser_write_sds(struct ser_handle *sh, int tag, const sds s) {
	size_t length = s ? sdslen(s) : 0;
	ser_write(sh, tag, s, length);
}

void ser_write(struct ser_handle *sh, int tag, const void *ptr, size_t size) {
	if (!sh)
		return;
	ser_write_tag(sh, tag, size);
	s_write(sh, ptr, size);
	sh->length -= size;
	ser_write_close_tag(sh);
}

// Open tag write helpers.  As above, but without the closing tag, indicating
// nested data.

void ser_write_open_vuint32(struct ser_handle *sh, int tag, uint32_t v) {
	size_t length = fs_sizeof_vuint32(v);
	ser_write_tag(sh, tag, length);
	s_write_vuint32(sh, v);
	sh->length -= length;
}

void ser_write_open_string(struct ser_handle *sh, int tag, const char *s) {
	size_t length = s ? strlen(s) : 0;
	ser_write_tag(sh, tag, length);
	ser_write_untagged(sh, s, length);
}

void ser_write_open_sds(struct ser_handle *sh, int tag, const sds s) {
	size_t length = s ? sdslen(s) : 0;
	ser_write_tag(sh, tag, length);
	ser_write_untagged(sh, s, length);
}

// Untagged write helpers.  For manually writing tag DATA.

void ser_write_uint8_untagged(struct ser_handle *sh, uint8_t v) {
	if (!sh)
		return;
	if (sh->length < 1) {
		ser_set_error(sh, ser_error_format);
		return;
	}
	s_write_uint8(sh, v);
	sh->length--;
}

void ser_write_uint16_untagged(struct ser_handle *sh, uint16_t v) {
	if (!sh)
		return;
	if (sh->length < 2) {
		ser_set_error(sh, ser_error_format);
		return;
	}
	s_write_uint16(sh, v);
	sh->length -= 2;
}

void ser_write_untagged(struct ser_handle *sh, const void *ptr, size_t size) {
	if (!sh)
		return;
	if (size > sh->length) {
		ser_set_error(sh, ser_error_format);
		return;
	}
	s_write(sh, ptr, size);
	sh->length -= size;
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

// Read helpers.

int8_t ser_read_int8(struct ser_handle *sh) {
	return (int8_t)ser_read_uint8(sh);
}

uint8_t ser_read_uint8(struct ser_handle *sh) {
	if (!sh || sh->error)
		return 0;
	if (sh->length < 1) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	sh->length--;
	return s_read_uint8(sh);
}

int16_t ser_read_int16(struct ser_handle *sh) {
	return (int16_t)ser_read_uint16(sh);
}

uint16_t ser_read_uint16(struct ser_handle *sh) {
	if (!sh || sh->error)
		return 0;
	if (sh->length < 2) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	sh->length -= 2;
	return s_read_uint16(sh);
}

int32_t ser_read_vint32(struct ser_handle *sh) {
	if (!sh || sh->error)
		return 0;
	if (sh->length < 1) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	int nread;
	int32_t v = fs_read_vint32(sh->fd, &nread);
	if (nread <= 0) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	if ((unsigned)nread > sh->length) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	sh->length -= nread;
	return v;
}

uint32_t ser_read_vuint32(struct ser_handle *sh) {
	if (!sh || sh->error)
		return 0;
	if (sh->length < 1) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	int nread;
	uint32_t v = fs_read_vuint32(sh->fd, &nread);
	if (nread <= 0) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	if ((unsigned)nread > sh->length) {
		ser_set_error(sh, ser_error_format);
		return 0;
	}
	sh->length -= nread;
	return v;
}

void ser_read(struct ser_handle *sh, void *ptr, size_t size) {
	if (!sh || sh->error)
		return;
	if (sh->length < size) {
		ser_set_error(sh, ser_error_format);
		return;
	}
	sh->length -= size;
	s_read(sh, ptr, size);
}

// These allocate their own storage:

char *ser_read_string(struct ser_handle *sh) {
	if (!sh || sh->error)
		return NULL;
	char *s = xmalloc(sh->length+1);
	s_read(sh, s, sh->length);
	s[sh->length] = 0;
	sh->length = 0;
	return s;
}

sds ser_read_sds(struct ser_handle *sh) {
	if (!sh || sh->error)
		return NULL;
	sds s = sdsMakeRoomFor(sdsempty(), sh->length);
	s_read(sh, s, sh->length);
	sdsIncrLen(s, sh->length);
	sh->length = 0;
	return s;
}

void *ser_read_new(struct ser_handle *sh, size_t size) {
	if (!sh || sh->error)
		return NULL;
	if (sh->length < size) {
		ser_set_error(sh, ser_error_format);
		return NULL;
	}
	sh->length -= size;
	return s_read_new(sh, size);
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

int ser_write_struct(struct ser_handle *sh, const struct ser_struct *ss, int nss, int tag, void *s) {
	for (; tag <= nss && !sh->error; tag++) {
		enum ser_type type = ss[tag-1].type;
		SER_DEBUG("ser_write_struct(): tag=%d type=%d\n", tag, type);
		if (type == ser_type_unhandled)
			return tag;
		if (type == ser_type_skip)
			continue;
		void *ptr = s + ss[tag-1].data.offset;
		switch (type) {
		case ser_type_bool:
			ser_write_vuint32(sh, tag, *(_Bool *)ptr);
			break;
		case ser_type_int:
			ser_write_vint32(sh, tag, *(int *)ptr);
			break;
		case ser_type_unsigned:
			ser_write_vuint32(sh, tag, *(unsigned *)ptr);
			break;
		case ser_type_int8:
			ser_write_vint32(sh, tag, *(int8_t *)ptr);
			break;
		case ser_type_uint8:
			ser_write_vuint32(sh, tag, *(uint8_t *)ptr);
			break;
		case ser_type_int16:
			ser_write_vint32(sh, tag, *(int16_t *)ptr);
			break;
		case ser_type_uint16:
			ser_write_vuint32(sh, tag, *(uint16_t *)ptr);
			break;
		case ser_type_int32:
			ser_write_vint32(sh, tag, *(int32_t *)ptr);
			break;
		case ser_type_uint32:
			ser_write_vuint32(sh, tag, *(uint32_t *)ptr);
			break;
		case ser_type_tick:
			ser_write_vint32(sh, tag, *(event_ticks *)ptr - event_current_tick);
			break;
		case ser_type_event:
			{
				struct event *e = ptr;
				if (e->queued) {
					ser_write_vuint32(sh, tag, e->at_tick - event_current_tick);
				}
			}
			break;
		case ser_type_eventp:
			{
				struct event *e = *(struct event **)ptr;
				if (e && e->queued) {
					ser_write_vuint32(sh, tag, e->at_tick - event_current_tick);
				}
			}
			break;
		case ser_type_string:
			{
				char *str = *(char **)ptr;
				if (str) {
					ser_write_string(sh, tag, str);
				}
			}
			break;
		case ser_type_sds:
			{
				sds str = *(sds *)ptr;
				if (str) {
					ser_write_sds(sh, tag, str);
				}
			}
			break;
		case ser_type_nest:
			{
				const struct ser_struct_data *nssd = ss[tag-1].data.ser_struct_data;
				ser_write_open_string(sh, tag, "");
				ser_write_struct_data(sh, nssd, s);
			}
			break;

		default:
			ser_set_error(sh, ser_error_type);
			break;
		}
	}
	if (sh->error)
		return -1;
	return 0;
}

int ser_read_struct(struct ser_handle *sh, const struct ser_struct *ss, int nss, void *s) {
	int tag = -1;
	while (!sh->error && (tag = ser_read_tag(sh)) > 0) {
		if (tag > nss) {
			SER_DEBUG("ser_read_struct(): tag=%d invalid\n", tag);
			ser_set_error(sh, ser_error_bad_tag);
			return -1;
		}
		enum ser_type type = ss[tag-1].type;
		void *ptr = s + ss[tag-1].data.offset;
		SER_DEBUG("ser_read_struct(): tag=%d type=%d\n", tag, type);
		switch (type) {
		case ser_type_bool:
			*(_Bool *)ptr = ser_read_vuint32(sh);
			break;
		case ser_type_int:
			*(int *)ptr = ser_read_vint32(sh);
			break;
		case ser_type_unsigned:
			*(unsigned *)ptr = ser_read_vuint32(sh);
			break;
		case ser_type_int8:
			*(int8_t *)ptr = ser_read_vint32(sh);
			break;
		case ser_type_uint8:
			*(uint8_t *)ptr = ser_read_vuint32(sh);
			break;
		case ser_type_int16:
			*(int16_t *)ptr = ser_read_vint32(sh);
			break;
		case ser_type_uint16:
			*(uint16_t *)ptr = ser_read_vuint32(sh);
			break;
		case ser_type_int32:
			*(int32_t *)ptr = ser_read_vint32(sh);
			break;
		case ser_type_uint32:
			*(uint32_t *)ptr = ser_read_vuint32(sh);
			break;
		case ser_type_tick:
			*(event_ticks *)ptr = event_current_tick + ser_read_vint32(sh);
			break;
		case ser_type_event:
			{
				struct event *e = ptr;
				e->at_tick = event_current_tick + ser_read_vuint32(sh);
				e->next = e;  // flag reader to queue
			}
			break;
		case ser_type_eventp:
			{
				struct event *e = *(struct event **)ptr;
				if (e) {
					e->at_tick = event_current_tick + ser_read_vuint32(sh);
					e->next = e;  // flag reader to queue
				}
			}
			break;
		case ser_type_string:
			{
				if (*(char **)ptr != NULL)
					free(*(char **)ptr);
				*(char **)ptr = ser_read_string(sh);
			}
			break;
		case ser_type_sds:
			{
				if (*(sds *)ptr != NULL)
					sdsfree(*(sds *)ptr);
				*(sds *)ptr = ser_read_sds(sh);
			}
			break;
		case ser_type_nest:
			{
				const struct ser_struct_data *nssd = ss[tag-1].data.ser_struct_data;
				ser_read_struct_data(sh, nssd, s);
			}
			break;

		case ser_type_unhandled:
			return tag;
		case ser_type_skip:
			continue;
		default:
			ser_set_error(sh, ser_error_type);
			break;
		}
	}
	if (sh->error)
		return -1;
	return tag;
}

void ser_write_struct_data(struct ser_handle *sh, const struct ser_struct_data *ss, void *s) {
	SER_DEBUG("ser_write_struct_data(%p)\n", ss);
	for (int tag = 1; !ser_error(sh) && (tag = ser_write_struct(sh, ss->elems, ss->num_elems, tag, s)) > 0; tag++) {
		assert(ss->write_elem != NULL);
		if (!ss->write_elem(s, sh, tag)) {
			ser_set_error(sh, ser_error_bad_tag);
			SER_DEBUG("ser_write_struct_data(%p) FAILED\n", ss);
			return;
		}
	}
	ser_write_close_tag(sh);
	SER_DEBUG("ser_write_struct_data(%p) finished\n", ss);
}

void ser_read_struct_data(struct ser_handle *sh, const struct ser_struct_data *ss, void *s) {
	SER_DEBUG("ser_read_struct_data(%p)\n", ss);
	int tag;
	while (!ser_error(sh) && (tag = ser_read_struct(sh, ss->elems, ss->num_elems, s)) > 0) {
		if (!ss->read_elem || !ss->read_elem(s, sh, tag)) {
			ser_set_error(sh, ser_error_bad_tag);
			SER_DEBUG("ser_read_struct_data(%p) FAILED\n", ss);
			return;
		}
	}
	SER_DEBUG("ser_read_struct_data(%p) finished\n", ss);
}
