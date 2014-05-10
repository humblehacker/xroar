/*  XRoar - a Dragon/Tandy Coco emulator
 *  Copyright (C) 2003-2014  Ciaran Anscomb
 *
 *  See COPYING.GPL for redistribution conditions. */

#ifndef XROAR_SAM_H_
#define XROAR_SAM_H_

#include <stdint.h>

#define EVENT_SAM_CYCLES(c) (c)

#define sam_init()
void sam_reset(void);
_Bool sam_run(uint16_t A, _Bool RnW, int *S, uint16_t *Z, int *ncycles);
void sam_vdg_hsync(_Bool level);
void sam_vdg_fsync(_Bool level);
int sam_vdg_bytes(int nbytes, uint16_t *V, _Bool *valid);
void sam_set_register(unsigned int value);
unsigned int sam_get_register(void);

#endif  /* XROAR_SAM_H_ */
