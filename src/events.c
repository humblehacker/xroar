/*  Copyright 2003-2017 Ciaran Anscomb
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

#include <stdlib.h>

#include "xalloc.h"

#include "events.h"
#include "logging.h"

extern inline _Bool event_pending(struct event **list);
extern inline void event_dispatch_next(struct event **list);
extern inline void event_run_queue(struct event **list);

event_ticks event_current_tick = 0;

struct event *event_new(DELEGATE_T0(void) delegate) {
	struct event *new = xmalloc(sizeof(*new));
	event_init(new, delegate);
	return new;
}

void event_init(struct event *event, DELEGATE_T0(void) delegate) {
	if (event == NULL) return;
	event->at_tick = event_current_tick;
	event->delegate = delegate;
	event->queued = 0;
	event->list = NULL;
	event->next = NULL;
}

void event_free(struct event *event) {
	event_dequeue(event);
	free(event);
}

void event_queue(struct event **list, struct event *event) {
	struct event **entry;
	if (event->queued)
		event_dequeue(event);
	event->list = list;
	event->queued = 1;
	for (entry = list; *entry; entry = &((*entry)->next)) {
		if ((event->at_tick - (*entry)->at_tick) > (EVENT_TICK_MAX/2)) {
			event->next = *entry;
			*entry = event;
			return;
		}
	}
	*entry = event;
	event->next = NULL;
}

void event_dequeue(struct event *event) {
	struct event **list = event->list;
	struct event **entry;
	event->queued = 0;
	if (list == NULL)
		return;
	if (*list == event) {
		*list = event->next;
		return;
	}
	for (entry = list; *entry; entry = &((*entry)->next)) {
		if ((*entry)->next == event) {
			(*entry)->next = event->next;
			return;
		}
	}
}
