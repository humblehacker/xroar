/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2007  Ciaran Anscomb
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

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

#include "types.h"
#include "crc16.h"
#include "fs.h"
#include "logging.h"
#include "vdisk.h"
#include "vdrive.h"

#define MAX_SIDES (2)
#define MAX_TRACKS (256)

static struct {
	const char *ext;
	struct vdisk *(*load_func)(const char *);
} dispatch[] = {
	{ "VDK", vdisk_load_vdk },
	{ "JVC", vdisk_load_jvc },
	{ "DSK", vdisk_load_jvc },
	{ "DMK", vdisk_load_dmk },
	{ NULL,  vdisk_load_jvc }
};

struct vdisk *vdisk_blank_disk(int num_sides, int num_tracks,
		int track_length) {
	struct vdisk *new;
	uint8_t *new_track_data;
	unsigned int data_size;
	/* Ensure multiples of track_length will stay 16-bit aligned */
	if ((track_length % 2) != 0)
		track_length++;
	if (num_sides < 1 || num_sides > MAX_SIDES
			|| num_tracks < 1 || num_tracks > MAX_TRACKS
			|| track_length < 129 || track_length > 0x2940) {
		return NULL;
	}
	new = malloc(sizeof(struct vdisk));
	if (new == NULL)
		return NULL;
	data_size = num_tracks * num_sides * track_length;
	new_track_data = malloc(data_size);
	if (new_track_data == NULL) {
		free(new);
		return NULL;
	}
	memset(new_track_data, 0, data_size);
	new->write_protect = 0;
	new->num_sides = num_sides;
	new->num_tracks = num_tracks;
	new->track_length = track_length;
	new->track_data = new_track_data;
	return new;
}

void vdisk_destroy(struct vdisk *disk) {
	if (disk == NULL) return;
	free(disk->track_data);
	free(disk);
}

struct vdisk *vdisk_load(const char *filename) {
	char ext[4];
	int len = strlen(filename);
	int i;
	if (len < 4)
		return vdisk_load_vdk(filename);
	for (i = 0; i < 3; i++)
		ext[i] = toupper(filename[i+len-3]);
	ext[3] = 0;
	i = 0;
	do {
		if (strcmp(ext, dispatch[i].ext) == 0)
			break;
		i++;
	} while (dispatch[i].ext != NULL);
	return dispatch[i].load_func(filename);
}

struct vdisk *vdisk_load_vdk(const char *filename) {
	struct vdisk *disk;
	ssize_t file_size;
	unsigned int header_size;
	unsigned int num_tracks;
	unsigned int num_sides = 1;
	unsigned int num_sectors = 18;
	unsigned int ssize_code = 1, ssize;
	unsigned int track, sector, side;
	uint8_t buf[1024];
	int fd;
	if ((file_size = fs_size(filename)) < 0)
		return NULL;
	if ((fd = fs_open(filename, FS_READ)) < 0)
		return NULL;
	fs_read(fd, buf, 12);
	file_size -= 12;
	if (buf[0] != 'd' || buf[1] != 'k') {
		fs_close(fd);
		return NULL;
	}
	header_size = (buf[2] | (buf[3]<<8)) - 12;
	num_tracks = buf[8];
	num_sides = buf[9];
	if (header_size > 0)
		fs_read(fd, buf, header_size);
	ssize = 128 << ssize_code;
	disk = vdisk_blank_disk(num_sides, num_tracks, VDISK_LENGTH_5_25);
	if (disk == NULL) {
		fs_close(fd);
		return NULL;
	}
	if (vdisk_format_disk(disk, VDISK_DOUBLE_DENSITY, num_sectors, 1, ssize_code) < 0) {
		fs_close(fd);
		vdisk_destroy(disk);
		return NULL;
	}
	LOG_DEBUG(2,"Loading VDK virtual disk: %dT %dH %dS (%d-byte)\n", num_tracks, num_sides, num_sectors, ssize);
	for (track = 0; track < num_tracks; track++) {
		for (side = 0; side < num_sides; side++) {
			for (sector = 0; sector < num_sectors; sector++) {
				fs_read(fd, buf, ssize);
				vdisk_update_sector(disk, side, track, sector + 1, ssize, buf);
			}
		}
	}
	fs_close(fd);
	return disk;
}

struct vdisk *vdisk_load_jvc(const char *filename) {
	struct vdisk *disk;
	ssize_t file_size = fs_size(filename);
	unsigned int header_size;
	unsigned int num_tracks;
	unsigned int num_sides = 1;
	unsigned int num_sectors = 18;
	unsigned int ssize_code = 1, ssize;
	unsigned int first_sector = 1;
	unsigned int sector_attr = 0;
	unsigned int track, sector, side;
	uint8_t buf[1024];
	int fd;
	if (file_size < 0)
		return NULL;
	header_size = file_size % 256;
	file_size -= header_size;
	/* Supposedly, we are supposed to default to single sided if there's
	 * no header information overriding, but I found double sided
	 * headerless DSK files. */
	if (file_size > 198144) num_sides = 2;
	fd = fs_open(filename, FS_READ);
	if (fd < 0)
		return NULL;
	if (header_size > 0) {
		fs_read(fd, buf, header_size);
		num_sectors = buf[0];
	}
	if (header_size > 1) num_sides = buf[1];
	if (header_size > 2) ssize_code = buf[2] & 3;
	ssize = 128 << ssize_code;
	if (header_size > 3) first_sector = buf[3];
	if (header_size > 4) sector_attr = buf[4] ? 1 : 0;
	if (sector_attr == 0)
		num_tracks = file_size / (num_sectors * ssize) / num_sides;
	else
		num_tracks = file_size / (num_sectors * (ssize+1)) / num_sides;
	disk = vdisk_blank_disk(num_sides, num_tracks, VDISK_LENGTH_5_25);
	if (disk == NULL) {
		fs_close(fd);
		return NULL;
	}
	if (vdisk_format_disk(disk, VDISK_DOUBLE_DENSITY, num_sectors, first_sector, ssize_code) < 0) {
		fs_close(fd);
		vdisk_destroy(disk);
		return NULL;
	}
	LOG_DEBUG(2,"Loading JVC virtual disk: %dT %dH %dS (%d-byte)\n", num_tracks, num_sides, num_sectors, ssize);
	for (track = 0; track < num_tracks; track++) {
		for (side = 0; side < num_sides; side++) {
			for (sector = 0; sector < num_sectors; sector++) {
				uint8_t attr;
				if (sector_attr) fs_read_byte(fd, &attr);
				fs_read(fd, buf, ssize);
				vdisk_update_sector(disk, side, track, sector + first_sector, ssize, buf);
			}
		}
	}
	fs_close(fd);
	return disk;
}

struct vdisk *vdisk_load_dmk(const char *filename) {
	struct vdisk *disk;
	uint8_t header[16];
	ssize_t file_size = fs_size(filename);
	int write_protect = 0;
	unsigned int num_sides;
	unsigned int num_tracks;
	unsigned int track_length;
	unsigned int track, side;
	int fd;
	if (file_size < 0)
		return NULL;
	fd = fs_open(filename, FS_READ);
	if (fd < 0)
		return NULL;
	fs_read(fd, header, 16);
	write_protect = header[0] ? VDISK_WRITE_PROTECT : VDISK_WRITE_ENABLE;
	num_tracks = header[1];
	track_length = (header[3] << 8) | header[2];  /* yes, little-endian! */
	num_sides = (header[4] & 0x10) ? 1 : 2;
	if (header[4] & 0x40)
		LOG_WARN("DMK is flagged single-density only\n");
	if (header[4] & 0x80)
		LOG_WARN("DMK is flagged density-agnostic\n");
	file_size -= 16;
	disk = vdisk_blank_disk(num_sides, num_tracks, VDISK_LENGTH_5_25);
	if (disk == NULL) {
		fs_close(fd);
		return NULL;
	}
	LOG_DEBUG(2,"Loading DMK virtual disk: %dT %dH (%d-byte)\n", num_tracks, num_sides, track_length);
	for (track = 0; track < num_tracks; track++) {
		for (side = 0; track < num_tracks; track++) {
			uint16_t *idams = vdisk_track_base(disk, side, track);
			uint8_t *buf = (uint8_t *)idams;
			int i;
			if (buf == NULL) continue;
			fs_read(fd, buf, 128);
			for (i = 0; i < 64; i++) {
				/* ensure correct endianness */
				uint16_t tmp = (buf[1] << 8) | buf[0];
				idams[i] = tmp;
				buf += 2;
			}
			fs_read(fd, buf, track_length - 128);
			buf += track_length - 128;
		}
	}
	fs_close(fd);
	return disk;
}

/* Returns void because track data is manipulated in 8-bit and 16-bit
 * chunks. */
void *vdisk_track_base(struct vdisk *disk, int side, int track) {
	if (disk == NULL
			|| side < 0 || (unsigned)side >= disk->num_sides
			|| track < 0 || (unsigned)track >= disk->num_tracks) {
		return NULL;
	}
	return disk->track_data
		+ ((track * disk->num_sides) + side) * disk->track_length;
}

static unsigned int sect_interleave[18] =
	{ 0, 9, 1, 10, 2, 11, 3, 12, 4, 13, 5, 14, 6, 15, 7, 16, 8, 17 };

#define WRITE_BYTE(v) data[offset++] = (v)

#define WRITE_BYTE_CRC(v) do { \
		WRITE_BYTE(v); \
		crc16_byte(v); \
	} while (0)

#define WRITE_CRC() do { \
		uint16_t tmpcrc = crc16_value(); \
		data[offset++] = (tmpcrc & 0xff00) >> 8; \
		data[offset++] = tmpcrc & 0xff; \
	} while (0)

int vdisk_format_disk(struct vdisk *disk, int density,
		int num_sectors, int first_sector, int ssize_code) {
	int ssize = 128 << ssize_code;
	int side, track, sector, i;
	if (disk == NULL) return -1;
	if (density != VDISK_DOUBLE_DENSITY) return -1;
	for (side = 0; (unsigned)side < disk->num_sides; side++) {
		for (track = 0; (unsigned)track < disk->num_tracks; track++) {
			uint16_t *idams = vdisk_track_base(disk, side, track);
			uint8_t *data = (uint8_t *)idams;
			unsigned int offset = 128;
			unsigned int idam = 0;
			for (i = 0; i < 54; i++) WRITE_BYTE(0x4e);
			for (i = 0; i < 9; i++) WRITE_BYTE(0x00);
			for (i = 0; i < 3; i++) WRITE_BYTE(0xc2);
			WRITE_BYTE(0xfc);
			for (i = 0; i < 32; i++) data[offset++] = 0x4e;
			for (sector = 0; sector < num_sectors; sector++) {
				for (i = 0; i < 8; i++) data[offset++] = 0x00;
				crc16_reset();
				for (i = 0; i < 3; i++) WRITE_BYTE_CRC(0xa1);
				idams[idam++] = offset | density;
				WRITE_BYTE_CRC(0xfe);
				WRITE_BYTE_CRC(track);
				WRITE_BYTE_CRC(side);
				WRITE_BYTE_CRC(sect_interleave[sector] + first_sector);
				WRITE_BYTE_CRC(ssize_code);
				WRITE_CRC();
				for (i = 0; i < 22; i++) WRITE_BYTE(0x4e);
				for (i = 0; i < 12; i++) WRITE_BYTE(0x00);
				crc16_reset();
				for (i = 0; i < 3; i++) WRITE_BYTE_CRC(0xa1);
				WRITE_BYTE_CRC(0xfb);
				for (i = 0; i < ssize; i++)
					WRITE_BYTE_CRC(0xe5);
				WRITE_CRC();
				for (i = 0; i < 24; i++) WRITE_BYTE(0x4e);
			}
			while (offset < disk->track_length) {
				WRITE_BYTE(0x4e);
			}
		}
	}
	return 0;
}

int vdisk_update_sector(struct vdisk *disk, int side, int track,
		int sector, int sector_length, uint8_t *buf) {
	uint8_t *data;
	uint16_t *idams;
	unsigned int offset;
	int ssize, i;
	if (disk == NULL) return -1;
	idams = vdisk_track_base(disk, side, track);
	if (idams == NULL) return -1;
	data = (uint8_t *)idams;
	for (i = 0; i < 64; i++) {
		offset = idams[i] & 0x3fff;
		if (data[offset + 1] == track && data[offset + 2] == side
				&& data[offset + 3] == sector)
			break;
	}
	if (i >= 64) return -1;
	ssize = 128 << data[offset + 4];
	offset += 7;
	offset += 22;
	for (i = 0; i < 12; i++) WRITE_BYTE(0x00);
	crc16_reset();
	for (i = 0; i < 3; i++) WRITE_BYTE_CRC(0xa1);
	WRITE_BYTE_CRC(0xfb);
	for (i = 0; i < sector_length; i++) {
		if (i < ssize)
			WRITE_BYTE_CRC(buf[i]);
	}
	for ( ; i < ssize; i++)
		WRITE_BYTE_CRC(0x00);
	WRITE_CRC();
	WRITE_BYTE(0xfe);
	return 0;
}
