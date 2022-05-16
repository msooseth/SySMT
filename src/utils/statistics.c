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
  Generic module for handling options
  --------------------------------------------------------------
*/

#include <sys/time.h>
#ifndef WIN32
#include <sys/resource.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"
#include "statistics.h"
#include "table.h"

/*
  --------------------------------------------------------------
  timeval help functions
  --------------------------------------------------------------
*/

static void
timeval_init(struct timeval *x)
{
  x->tv_sec = 0;
  x->tv_usec = 0;
}

/*--------------------------------------------------------------*/

static void
timeval_diff(struct timeval *x, struct timeval *y)
{
  x->tv_sec -= y->tv_sec;
  x->tv_usec -= y->tv_usec;

  if (x->tv_usec < 0)
    {
      long int nsec = x->tv_usec / 1000000;
      x->tv_usec -= 1000000 * nsec;
      x->tv_sec += nsec;
    }
}

/*--------------------------------------------------------------*/

static void
timeval_add(struct timeval *x, struct timeval *y)
{
  x->tv_sec += y->tv_sec;
  x->tv_usec += y->tv_usec;

  if (x->tv_usec > 1000000)
    {
      long int nsec = x->tv_usec / 1000000;
      x->tv_usec -= 1000000 * nsec;
      x->tv_sec += nsec;
    }
}

/*
  --------------------------------------------------------------
  time_adder
  --------------------------------------------------------------
*/

struct TStime_adder
{
  int who;
  struct timeval last_time;
  struct timeval total_time;
};
typedef struct TStime_adder *Ttime_adder;

static Ttime_adder
time_adder_new(int who)
{
  Ttime_adder result;
  MY_MALLOC(result, sizeof(struct TStime_adder));
  timeval_init(&result->total_time);
  result->who = who;
  return result;
}

/*--------------------------------------------------------------*/
static void
time_adder_free(Ttime_adder * Ptime_adder)
{
  free(*Ptime_adder);
  *Ptime_adder = NULL;
}

/*--------------------------------------------------------------*/

static void
time_adder_start(Ttime_adder time_adder)
{
#ifndef WIN32
  struct rusage usage;
  if (!time_adder)
    my_error("time_adder_start: NULL pointer\n");
  timeval_init(&time_adder->last_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&time_adder->last_time, &usage.ru_utime);
      timeval_add(&time_adder->last_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&time_adder->last_time, &usage.ru_utime);
      timeval_add(&time_adder->last_time, &usage.ru_stime);
    }
#endif
}

/*--------------------------------------------------------------*/

static void
time_adder_stop(Ttime_adder time_adder)
{
#ifndef WIN32
  struct rusage usage;
  struct timeval actual_time;
  if (!time_adder)
    my_error("time_adder_stop: NULL pointer\n");
  timeval_init(&actual_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  timeval_diff(&actual_time, &time_adder->last_time);
  timeval_add(&time_adder->total_time, &actual_time);
#endif
}

/*--------------------------------------------------------------*/

static double
time_adder_get(Ttime_adder time_adder)
{
  double result;
  if (!time_adder)
    my_error("time_adder_get: NULL pointer\n");
  result = (double) time_adder->total_time.tv_sec;
  result += (double) time_adder->total_time.tv_usec / 1000000.0;
  return result;
}


/*--------------------------------------------------------------*/

static double
time_adder_intermediate_get(Ttime_adder time_adder)
{
#ifndef WIN32
  double result;
  struct rusage usage;
  struct timeval actual_time;
  if (!time_adder)
    my_error("time_adder_intermediate_get: NULL pointer\n");
  result = (double) time_adder->total_time.tv_sec;
  result += (double) time_adder->total_time.tv_usec / 1000000.0;
  timeval_init(&actual_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  timeval_diff(&actual_time, &time_adder->last_time);
  result += (double) actual_time.tv_sec;
  result += (double) actual_time.tv_usec / 1000000.0;
  return result;
#else
  return 1.0;		/* fake value for Windows */
#endif
}

/*
  --------------------------------------------------------------
  Statistics
  --------------------------------------------------------------
*/

static struct TSstats
{
  Ttable table_counter;
  Ttable table_timer;
} stats;

struct Tstat_counter
{
  char *name, *desc, *form;
  int value;
};
typedef struct Tstat_counter Tstat_counter;

struct Tstat_timer
{
  char *name, *desc, *form;
  Ttime_adder time_adder;
};
typedef struct Tstat_timer Tstat_timer;

/*--------------------------------------------------------------*/

unsigned
stats_counter_new(char *name, char *desc, char *form)
{
  Tstat_counter *Pstat_counter;
  MY_MALLOC(Pstat_counter, sizeof(Tstat_counter));
  Pstat_counter->name = name;
  Pstat_counter->desc = desc;
  Pstat_counter->form = form;
  Pstat_counter->value = 0;
  table_push(stats.table_counter, Pstat_counter);
  return table_length(stats.table_counter) - 1;
}

/*--------------------------------------------------------------*/

void
stats_counter_set(unsigned stat_nb, int value)
{
  Tstat_counter *Pstat_counter;
  if (stat_nb >= table_length(stats.table_counter))
    my_error("stats_counter_set : unknown statistic\n");
  Pstat_counter = (Tstat_counter *) table_get(stats.table_counter, stat_nb);
  Pstat_counter->value = value;
}

/*--------------------------------------------------------------*/

int
stats_counter_get(unsigned stat_nb)
{
  Tstat_counter *Pstat_counter;
  if (stat_nb >= table_length(stats.table_counter))
    my_error("stats_counter_get : unknown statistic\n");
  Pstat_counter = (Tstat_counter *) table_get(stats.table_counter, stat_nb);
  return Pstat_counter->value;
}

/*--------------------------------------------------------------*/

void
stats_counter_add(unsigned stat_nb, int value)
{
  Tstat_counter *Pstat_counter;
  if (stat_nb >= table_length(stats.table_counter))
    my_error("stats_counter_add : unknown statistic\n");
  Pstat_counter = (Tstat_counter *) table_get(stats.table_counter, stat_nb);
  Pstat_counter->value += value;
}

/*--------------------------------------------------------------*/

void
stats_counter_inc(unsigned stat_nb)
{
  stats_counter_add(stat_nb, 1);
}

/*--------------------------------------------------------------*/

void
stats_counter_dec(unsigned stat_nb)
{
  stats_counter_add(stat_nb, -1);
}

/*--------------------------------------------------------------*/

unsigned
stats_timer_new(char *name, char *desc, char *form, int who)
{
  Tstat_timer *Pstat_timer;
  if ((who & STATS_TIMER_SELF) == 0 && (who & STATS_TIMER_CHILDREN) == 0)
    my_error("stats_timer_new: no process specified");
  MY_MALLOC(Pstat_timer, sizeof(Tstat_timer));
  Pstat_timer->name = name;
  Pstat_timer->desc = desc;
  Pstat_timer->form = form;
  Pstat_timer->time_adder = time_adder_new(who);
  table_push(stats.table_timer, Pstat_timer);
  return table_length(stats.table_timer) - 1;
}

/*--------------------------------------------------------------*/

void
stats_timer_start(unsigned stat_timer_nb)
{
  Tstat_timer *Pstat_timer;
  if (stat_timer_nb >= table_length(stats.table_timer))
    my_error("stats_timer_start : unknown statistic\n");
  Pstat_timer = (Tstat_timer *) table_get(stats.table_timer, stat_timer_nb);
  time_adder_start(Pstat_timer->time_adder);
}

/*--------------------------------------------------------------*/

void
stats_timer_stop(unsigned stat_timer_nb)
{
  Tstat_timer *Pstat_timer;
  if (stat_timer_nb >= table_length(stats.table_timer))
    my_error("stats_timer_stop : unknown statistic\n");
  Pstat_timer = (Tstat_timer *) table_get(stats.table_timer, stat_timer_nb);
  time_adder_stop(Pstat_timer->time_adder);
}

/*--------------------------------------------------------------*/

double
stats_timer_get(unsigned stat_timer_nb)
{
  Tstat_timer *Pstat_timer;
  if (stat_timer_nb >= table_length(stats.table_timer))
    my_error("stats_timer_get : unknown statistic\n");
  Pstat_timer = (Tstat_timer *) table_get(stats.table_timer, stat_timer_nb);
  return time_adder_intermediate_get(Pstat_timer->time_adder);
}

/*--------------------------------------------------------------*/

void
stats_fprint_formats(FILE * file)
{
  unsigned i;
  /* DD print the glossary */
  for (i = 0; i < table_length(stats.table_counter); i++)
    {
      Tstat_counter *Pstat =
	(Tstat_counter *) table_get(stats.table_counter, i);
      if (Pstat->name)
	fprintf(file, "STAT_FORM: %s: %s\n", Pstat->name, Pstat->form);
      else
	fprintf(file, "STAT_FORM: SC%.2u: %s\n", (unsigned int) i + 1, Pstat->form);
    }
  for (i = 0; i < table_length(stats.table_timer); i++)
    {
      Tstat_timer *Pstat = (Tstat_timer *) table_get(stats.table_timer, i);
      if (Pstat->name)
	fprintf(file, "STAT_FORM: %s: %s\n", Pstat->name, Pstat->form);
      else
	fprintf(file, "STAT_FORM: ST%.2u: %s\n", (unsigned int) i + 1, Pstat->form);
    }
}

/*--------------------------------------------------------------*/

void
stats_fprint_short(FILE * file)
{
  unsigned i;
  /* DD print the value of each counter/timer */
  for (i = 0; i < table_length(stats.table_counter); ++i)
    {
      Tstat_counter *Pstat =
	(Tstat_counter *) table_get(stats.table_counter, i);
      if (Pstat->name)
	fprintf(file, "%s=%d ", Pstat->name, (int) Pstat->value);
      else
	fprintf(file, "SC%.2u=%d ", (unsigned int) i + 1, (int) Pstat->value);
    }
  for (i = 0; i < table_length(stats.table_timer); ++i)
    {
      Tstat_timer *Pstat = (Tstat_timer *) table_get(stats.table_timer, i);
      if (Pstat->name)
	fprintf(file, "%s=%.3f ", Pstat->name,
		 time_adder_get(Pstat->time_adder));
      else
	fprintf(file, "ST%.2u=%.3f ", (unsigned int) i + 1,
		 time_adder_get(Pstat->time_adder));
    }
  fprintf(file, "\n");
}

/*--------------------------------------------------------------*/

void
stats_fprint(FILE * file)
{
  unsigned i;
  /* DD print the glossary */
  for (i = 0; i < table_length(stats.table_counter); i++)
    {
      Tstat_counter *Pstat =
	(Tstat_counter *) table_get(stats.table_counter, i);
      if (Pstat->name)
	fprintf(file, "STAT_DESC: %s: %s\n", Pstat->name, Pstat->desc);
      else
	fprintf(file, "STAT_DESC: SC%.2u: %s\n", (unsigned int) i + 1, Pstat->desc);
    }
  for (i = 0; i < table_length(stats.table_timer); i++)
    {
      Tstat_timer *Pstat = (Tstat_timer *) table_get(stats.table_timer, i);
      if (Pstat->name)
	fprintf(file, "STAT_DESC: %s: %s\n", Pstat->name, Pstat->desc);
      else
	fprintf(file, "STAT_DESC: ST%.2u: %s\n", (unsigned int) i + 1, Pstat->desc);
    }
  /* DD print value of each counter / timer */
  for (i = 0; i < table_length(stats.table_counter); i++)
    {
      Tstat_counter *Pstat =
	(Tstat_counter *) table_get(stats.table_counter, i);
      if (Pstat->name)
	fprintf(file, "STAT: %s=%d\n", Pstat->name, (int) Pstat->value);
      else
	fprintf(file, "STAT: SC%.2u=%d\n", (unsigned int) i + 1, (int) Pstat->value);
    }
  for (i = 0; i < table_length(stats.table_timer); i++)
    {
      Tstat_timer *Pstat = (Tstat_timer *) table_get(stats.table_timer, i);
      if (Pstat->name)
	fprintf(file, "STAT: %s=%.3f\n", Pstat->name,
		 time_adder_get(Pstat->time_adder));
      else
	fprintf(file, "STAT: ST%.2u=%.3f\n", (unsigned int) i + 1,
		 time_adder_get(Pstat->time_adder));
    }
}

/*--------------------------------------------------------------*/

void
stats_init(void)
{
  stats.table_counter = table_new(5, 1);
  stats.table_timer = table_new(5, 1);
}

/*--------------------------------------------------------------*/

void
stats_done(void)
{
  unsigned i;
  for (i = 0; i < table_length(stats.table_counter); i++)
    {
      Tstat_counter *Pstat =
	(Tstat_counter *) table_get(stats.table_counter, i);
      free(Pstat);
    }
  table_free(&stats.table_counter);
  for (i = 0; i < table_length(stats.table_timer); i++)
    {
      Tstat_timer *Pstat_timer =
	(Tstat_timer *) table_get(stats.table_timer, i);
      time_adder_free(&Pstat_timer->time_adder);
      free(Pstat_timer);
    }
  table_free(&stats.table_timer);
}
