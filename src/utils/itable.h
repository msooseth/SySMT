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
  table data structure
  --------------------------------------------------------------
*/

#ifndef ITABLE_H
#define ITABLE_H

/* A itable works like a table, but its elements are (int) instead of (void *) */

/* #define ITABLE_MACRO */

#ifdef ITABLE_MACRO
struct TSitable
{
  int       last;
  int       size;
  int       increment;
  int       *P;
};
#endif

typedef struct TSitable *Titable;

/* builds a table with initial size, and growing by adding increment */
Titable   itable_new (int size, int increment);
void      itable_free (Titable * Ptable);
/* initialize table such that it contains length elements, 0 initially */
void      itable_init (Titable table, int length);
/* returns number of elements in table */
#ifdef ITABLE_MACRO
#define   itable_length(T) T->last
#else
int       itable_length (Titable table);
#endif
/* returns the increment size of table */
int       itable_increment (Titable table);
/* adds P on top of table */
void      itable_push (Titable table, int P);
/* returns top of table, and remove element from table */
int       itable_pop (Titable table);
/* returns top of table, and let table unchanged */
int       itable_top (Titable table);
/* returns 1 iff table is empty, 0 else */
int       itable_empty (Titable table);
/* returns i-th element */
#ifdef ITABLE_MACRO
#define   itable_get(T, I) T->P[I]
#else
int       itable_get (Titable table, int i);
#endif
/* set i-th element */
void      itable_set (Titable table, int i, int P);
/* inserts P at position i */
void      itable_insert (Titable table, int i, int P);
/* delete i-th element */
int       itable_del (Titable table, int i);
/* table is set to have 0 elements */
void      itable_erase (Titable table);
/* applies f to every element in table */
void      itable_apply (Titable table, void (*f) (int ));
/* size of table is set to be exactly the number of elements,
   further adding only one element will imply a realloc */
void      itable_shrink (Titable table);

/* return element such that lookup_function(element, criteria) = 0
   Linear */
int       itable_lookup (Titable table,
			int (lookup_function) (int , int ),
			int criteria);
/* return element such that lookup_function(element, criteria) = 0.
   For sorted tables only! n ln n. */
int      itable_lookup_sort (Titable table,
			     int (lookup_function) (int , int ),
			     int criteria);

#endif /* __ITABLE_H */

