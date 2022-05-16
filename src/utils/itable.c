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
  Table data structure
  --------------------------------------------------------------
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"
#include "itable.h"

#ifndef ITABLE_MACRO
struct TSitable
{
  int last;
  int size;
  int increment;
  int *P;
};
#endif

/*--------------------------------------------------------------*/

Titable
itable_new (int size, int increment)
{
  Titable table;
  MY_MALLOC (table, sizeof (struct TSitable));
  table->last = 0;
  table->size = size;
  table->increment = increment;
  MY_MALLOC (table->P, (unsigned) size * sizeof (int ));
  return table;
}

/*--------------------------------------------------------------*/

void
itable_free (Titable * Ptable)
{
  if (!*Ptable)
    return;
  free ((*Ptable)->P);
  free (*Ptable);
  (*Ptable) = NULL;
}

/*--------------------------------------------------------------*/

void
itable_init (Titable table, int length)
{
  assert (table);
  if (length > table->size)
    {
      table->size = length;
      MY_REALLOC (table->P, (unsigned) table->size * sizeof (int ));
    }
  table->last = table->size;
  memset (table->P, 0, (unsigned) table->size * sizeof (int ));
}

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
int
itable_length (Titable table)
{
  assert (table);
  return table->last;
}
#endif

/*--------------------------------------------------------------*/

int
itable_increment (Titable table)
{
  assert (table);
  return table->increment;
}

/*--------------------------------------------------------------*/

void
itable_push (Titable table, int P)
{
  assert (table);
  if (table->last == table->size)
    {
      table->size = table->size + table->increment;
      MY_REALLOC (table->P, (unsigned) table->size * sizeof (int ));
    }
  table->P[table->last++] = P;
}

/*--------------------------------------------------------------*/

int 
itable_pop (Titable table)
{
  assert (table);
  if (table->last > 0)
    {
      table->last--;
      return table->P[table->last];
    }
  my_error ("itable_pop: empty table\n");
  return 0;
}

/*--------------------------------------------------------------*/

int 
itable_top (Titable table)
{
  assert (table);
  if (table->last > 0)
    return table->P[table->last - 1];
  my_error ("itable_top: empty table\n");
  return 0;
}

/*--------------------------------------------------------------*/

int
itable_empty (Titable table)
{
  assert (table);
  return table->last == 0;
}

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
int 
itable_get (Titable table, int i)
{
  assert (table);
  if (i >= table->last)
    my_error ("itable: access out of bounds\n");
  return table->P[i];
}
#endif

/*--------------------------------------------------------------*/

void
itable_set (Titable table, int i, int P)
{
  assert (table);
  assert (i >= 0);
  assert (i < table->size);
  table->P[i] = P;
}

/*--------------------------------------------------------------*/

void
itable_insert (Titable table, int i, int P)
{
  int j;
  assert (table);
  assert (i >= 0);
  assert (i < table->size);
  if (table->last == table->size)
    {
      table->size = table->size + table->increment;
      MY_REALLOC (table->P, (unsigned) table->size * sizeof (int ));
    }
  for (j = table->last; j > i; j--)
    table->P[j] = table->P[j - 1];
  table->P[i] = P;
  table->last++;
}

/*--------------------------------------------------------------*/

int 
itable_del (Titable table, int i)
{
  int j;
  int P;
  assert (table);
  assert (i >= 0);
  assert (i < table->size);
  P = table->P[i];
  for (j = i; j < table->last - 1; j++)
    table->P[j] = table->P[j + 1];
  table->P[j] = 0;
  table->last--;
  return P;
}

/*--------------------------------------------------------------*/

void
itable_erase (Titable table)
{
  assert (table);
  table->last = 0;
}

/*--------------------------------------------------------------*/

void
itable_apply (Titable table, void (*f) (int ))
{
  register int i;
  assert (table);
  for (i = 0; i < table->last; i++)
    f (table->P[i]);
}

/*--------------------------------------------------------------*/

void
itable_shrink (Titable table)
{
  assert (table);
  if (table->last < table->size)
    {
      table->size = table->last;
      MY_REALLOC (table->P, (unsigned) table->size * sizeof (int ));
    }
}

/*--------------------------------------------------------------*/

int 
itable_lookup (Titable table, int (lookup_function) (int , int ),
	      int criteria)
{
  int i;
  assert (table);
  for (i = 0; i < table->last; i++)
    if (!lookup_function (table->P[i], criteria))
      return table->P[i];
  return 0;
}

/*--------------------------------------------------------------*/

int 
itable_lookup_sort (Titable table, int (lookup_function) (int , int ),
		   int criteria)
{
  int i, j, m, c;
  assert (table);
  if (table->last == 0)
    return 0;
  i = 0;
  j = table->last - 1;
  while (i < j)
    {
      m = (i + j) / 2;
      c = lookup_function (table->P[m], criteria);
      if (!c)
	return table->P[m];
      if (c > 0)
	i = m + 1;
      else
	j = m - 1;
    }
  if (!lookup_function (table->P[i], criteria))
    return table->P[i];
  return 0;
}

/*--------------------------------------------------------------*/

