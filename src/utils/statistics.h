/*
Copyright (c) 2009, INRIA, Université de Nancy 2 and Universidade
Federal do Rio Grande do Norte.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
   * Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   * Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
   * Neither the name of the Université de Nancy 2 or the Universidade Federal
     do Rio Grande do Norte nor the names of its contributors may be used
     to endorse or promote products derived from this software without
     specific prior written permission.

THIS SOFTWARE IS PROVIDED BY INRIA, Université de Nancy 2 and
Universidade Federal do Rio Grande do Norte ''AS IS'' AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA, Université de Nancy 2 and
Universidade Federal do Rio Grande do Norte BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

/*
  --------------------------------------------------------------
  Generic module for handling statistics
  --------------------------------------------------------------
*/

#ifndef STATISTICS_H
#define STATISTICS_H

#include <stdio.h>

#include "table.h"

#define STATS_TIMER_SELF 1
#define STATS_TIMER_CHILDREN 2
#define STATS_TIMER_ALL 3

void      stats_init(void);
void      stats_done(void);

/* PF/DD creates a new counter (integer) stat, with name and description */
unsigned  stats_counter_new(char *name, char *desc, char *form);
/* PF/DD set value to counter */
void      stats_counter_set(unsigned stat_nb, int value);
/* PF/DD get value of counter */
int       stats_counter_get(unsigned stat_nb);
/* PF/DD adds value to counter */
void      stats_counter_add(unsigned stat_nb, int value);
/* PF/DD increments counter */
void      stats_counter_inc(unsigned stat_nb);
/* PF/DD decrements counter */
void      stats_counter_dec(unsigned stat_nb);

/* PF/DD creates a new timer stat, with name and description */
unsigned  stats_timer_new(char *name, char *desc, char *form, int who);
/* PF/DD start timer */
void      stats_timer_start(unsigned stat_time_nb);
/* PF/DD stop timer */
void      stats_timer_stop(unsigned stat_time_nb);
/* PF get timer time in second */
double    stats_timer_get(unsigned stat_timer_nb);

/* PF/DD prints statistics to file */
void      stats_fprint(FILE * file);
/* PF prints formats of statistics to file */
void      stats_fprint_formats(FILE * file);
/* DD prints short-form statistics to file */
void      stats_fprint_short(FILE * file);

#endif
