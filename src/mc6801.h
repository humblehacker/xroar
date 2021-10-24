/** \file
 *
 *  \brief Motorola MC6801/6803 CPUs.
 *
 *  \copyright Copyright 2021 Ciaran Anscomb
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

#ifndef XROAR_MC6801_H_
#define XROAR_MC6801_H_

#include <stdint.h>

#include "delegate.h"
#include "pl-endian.h"

#include "debug_cpu.h"
#include "part.h"

#ifdef TRACE
struct mc6801_trace;
#endif

#define MC6801_INT_VEC_RESET (0xfffe)
#define MC6801_INT_VEC_NMI (0xfffc)
#define MC6801_INT_VEC_SWI (0xfffa)
#define MC6801_INT_VEC_IRQ1 (0xfff8)
#define MC6801_INT_VEC_ICF (0xfff6)
#define MC6801_INT_VEC_OCF (0xfff4)
#define MC6801_INT_VEC_TOF (0xfff2)
#define MC6801_INT_VEC_SCI (0xfff0)

#define MC6801_REG_P1DDR (0)
#define MC6801_REG_P2DDR (1)
#define MC6801_REG_P1DR  (2)
#define MC6801_REG_P2DR  (3)
#define MC6801_REG_P3DDR (4)
#define MC6801_REG_P4DDR (5)
#define MC6801_REG_P3DR  (6)
#define MC6801_REG_P4DR  (7)
#define MC6801_REG_TCSR  (8)
#define MC6801_REG_CRMSB (9)
#define MC6801_REG_CRLSB (10)
#define MC6801_REG_OCMSB (11)
#define MC6801_REG_OCLSB (12)
#define MC6801_REG_ICMSB (13)
#define MC6801_REG_ICLSB (14)
#define MC6801_REG_P3CSR (15)
#define MC6801_REG_RMCR  (16)
#define MC6801_REG_TRCSR (17)
#define MC6801_REG_SCIRX (18)
#define MC6801_REG_SCITX (19)
#define MC6801_REG_RAMC  (20)

#define MC6801_VALUE_PORT1(c) (((c)->reg[MC6801_REG_P1DR] & (c)->reg[MC6801_REG_P1DDR]) | ((c)->port1_in & ~(c)->reg[MC6801_REG_P1DDR]))
#define MC6801_VALUE_PORT2(c) ((((c)->reg[MC6801_REG_P2DR] & (c)->reg[MC6801_REG_P2DDR]) | ((c)->port2_in & ~(c)->reg[MC6801_REG_P2DDR])) & 0x3f)

// MPU state.  Represents current position in the high-level flow chart from
// the data sheet.

enum mc6801_state {
	mc6801_state_reset = 0,
	mc6801_state_label_a,
	mc6801_state_sync,
	mc6801_state_dispatch_irq,
	mc6801_state_label_b,
	mc6801_state_next_instruction,
	mc6801_state_wai_check_halt,
	mc6801_state_sync_check_halt,
	mc6801_state_done_instruction,
	mc6801_state_hcf
};

struct MC6801 {
	// Is a debuggable CPU, which is a part
	struct debug_cpu debug_cpu;

	// Interrupt lines
	_Bool nmi, irq1;

	// Data bus (in real hardware, shared with port 3)
	uint8_t D;

	// Ports.  These should probably be full in/out source/sink sets as per
	// PIA code, but bodging for now.
	uint8_t port1_in;
	uint8_t port2_in;
	DELEGATE_T0(void) port2_preread;

	// 2048 bytes allocated for MC6801 ONLY.  Populate externally.
	size_t rom_size;
	uint8_t *rom;

	// Methods

	void (*reset)(struct MC6801 *cpu);
	void (*run)(struct MC6801 *cpu);
	void (*jump)(struct MC6801 *cpu, uint16_t pc);

	// External handlers

	// Memory access cycle
	DELEGATE_T2(void, bool, uint16) mem_cycle;
	// Called just before instruction fetch if non-NULL
	DELEGATE_T0(void) instruction_hook;
	// Called after instruction is executed
	DELEGATE_T0(void) instruction_posthook;

	// Internal state

	unsigned state;
	_Bool running;
#ifdef TRACE
	struct mc6801_trace *tracer;
#endif

	// Registers
	uint8_t reg_cc;
	uint16_t reg_d;
	uint16_t reg_x, reg_sp, reg_pc;

	uint8_t reg[32];
	uint8_t ICF;
	uint8_t OCF;
	uint8_t TOF;
	uint16_t counter;
	uint16_t output_compare;
	_Bool output_compare_inhibit;

	// Internal RAM
	uint8_t ram[128];

	// Interrupts
	uint8_t itmp;
	_Bool nmi_latch, nmi_active;
	_Bool irq1_latch, irq1_active;
	_Bool irq2_latch, irq2_active;
};

#if __BYTE_ORDER == __BIG_ENDIAN
# define MC6801_REG_HI (0)
# define MC6801_REG_LO (1)
#else
# define MC6801_REG_HI (1)
# define MC6801_REG_LO (0)
#endif

#define MC6801_REG_A(cpu) (*((uint8_t *)&cpu->reg_d + MC6801_REG_HI))
#define MC6801_REG_B(cpu) (*((uint8_t *)&cpu->reg_d + MC6801_REG_LO))

inline void MC6801_NMI_SET(struct MC6801 *cpu, _Bool val) {
	cpu->nmi = val;
}

inline void MC6801_IRQ1_SET(struct MC6801 *cpu, _Bool val) {
	cpu->irq1 = val;
}

struct MC6801 *mc6801_new(void);
struct MC6801 *mc6803_new(void);

#endif