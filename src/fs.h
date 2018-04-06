/*

File operations

Copyright 2003-2017 Ciaran Anscomb

This file is part of XRoar.

XRoar is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation, either version 2 of the License, or (at your option)
any later version.

See COPYING.GPL for redistribution conditions.

*/

#ifndef XROAR_FS_H_
#define XROAR_FS_H_

#include <stdio.h>
#include <sys/types.h>

off_t fs_file_size(FILE *fd);

// unlike ftruncate(), this leaves file position at new EOF
int fs_truncate(FILE *fd, off_t length);

int fs_write_uint8(FILE *fd, int value);
int fs_write_uint16(FILE *fd, int value);
int fs_write_uint16_le(FILE *fd, int value);
int fs_write_uint31(FILE *fd, int value);
int fs_read_uint8(FILE *fd);
int fs_read_uint16(FILE *fd);
int fs_read_uint16_le(FILE *fd);
int fs_read_uint31(FILE *fd);
int fs_read_vl_uint31(FILE *fd);  // variable-length uint31

/* Variable-length uint31 defined as:
 * 7-bit        0nnnnnnn
 * 14-bit       10nnnnnn nnnnnnnn
 * 21-bit       110nnnnn nnnnnnnn nnnnnnnn
 * 28-bit       1110nnnn nnnnnnnn nnnnnnnn nnnnnnnn
 * 31-bit       11110XXX Xnnnnnnn nnnnnnnn nnnnnnnn nnnnnnnn
 */

#endif
