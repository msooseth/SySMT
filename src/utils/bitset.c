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

#ifdef DEBUG
#include <stdio.h>
#endif
#ifdef PEDANTIC
#include <stdio.h>
#endif
#include <strings.h>

#include "general.h"

#include "bitset.h"

#define COORD(i, w, p) ((w) = (i) >> 3, (p) = (i) & 7)

struct TSbs_mgr {
  unsigned size;                /**< how many bytes represent a set */
  unsigned (* index) (void *);  /**< yields the index of a set element */
#ifdef DEBUG
  unsigned count;               /**< sanity check: number of created sets */
#endif
};

/*
#ifdef DEBUG
static void bitset_print(Tbs_mgr mgr, Tbs set);
#endif
*/

Tbs_mgr
bitset_new_manager (unsigned card, unsigned (* f) (void *))
{
  Tbs_mgr result;
  assert (card > 0);
  MY_MALLOC(result, sizeof(struct TSbs_mgr));
  result->size = 1u + (card >> 3u);
  result->index = f;
#ifdef DEBUG
  result->count = 0;
#endif
  return result;
}

void
bitset_free_manager(Tbs_mgr * m)
{
#ifdef DEBUG
  assert((*m)->count == 0);
#endif
  free(*m);
  *m = NULL;
}

Tbs
bitset_new (Tbs_mgr m)
{
  Tbs result;
  MY_MALLOC(result, m->size * sizeof(char));
  bzero(result, m->size*sizeof(char));
#ifdef DEBUG
  m->count += 1;
#endif
  return result;
}

void
bitset_free (Tbs_mgr m, Tbs s)
{
#ifdef DEBUG
  m->count -= 1;
#else
#ifdef PEDANTIC
  /* PF to avoid warning for unused variable */
  printf("%p\n", (void *) m);
#endif
#endif
  free(s);
}

void
bitset_insert(Tbs_mgr m, Tbs s, void * val)
{						
  unsigned i = m->index(val);
  unsigned w, p;
  assert(i < (m->size << 3));
  COORD(i, w, p);
  s[w] |= (unsigned char) (1u << p);
}

void
bitset_remove(Tbs_mgr m, Tbs s, void * val)
{						
  unsigned i = m->index(val);
  unsigned w, p;
  assert(i < (m->size << 3));
  COORD(i, w, p);
  s[w] &= (0xff & 0 << p);
}

void
bitset_union(Tbs_mgr m, Tbs res, Tbs set1, Tbs set2)
{
  unsigned w;
  for (w = 0; w < m->size; ++w)
    res[w] = set1[w] | set2[w];
}


void
bitset_diff(Tbs_mgr m, Tbs res, Tbs set1, Tbs set2)
{
  unsigned w;
  for (w = 0; w < m->size; ++w)
    res[w] = set1[w] & (unsigned char) ~set2[w];
}

int
bitset_empty(Tbs_mgr m, Tbs set)
{
  unsigned w;
  for (w = 0; w < m->size; ++w)
    if (set[w]) return 0;
  return 1;
}

int
bitset_equal(Tbs_mgr m, Tbs set1, Tbs set2)
{
  unsigned w;
  for (w = 0; w < m->size; ++w)
    if (set1[w] != set2[w])
      return 0;
  return 1;
}

int
bitset_subseteq(Tbs_mgr m, Tbs set1, Tbs set2)
{
  unsigned w;
  for (w = 0; w < m->size; ++w)
    if ((set1[w] | set2[w]) != set2[w])
      return 0;
  return 1;
}

int     
bitset_in(Tbs_mgr m, Tbs s, void * val)
{
  unsigned i = m->index(val);
  unsigned w, p;
  assert(i < (m->size << 3));
  COORD(i, w, p);
  return s[w] & (1 << p);
}

unsigned
bitset_card(Tbs_mgr m, Tbs s)
{
  unsigned w;
  unsigned result = 0;
  for (w = 0; w < m->size; ++w)
    {
      unsigned i;
      for (i = 0; i < 8; ++i)
	if (s[w] & (1 << i))
	  ++result;
    }
  return result;
}

#ifdef DEBUG
void
bitset_fprint(FILE * file, Tbs_mgr m, Tbs set)
{
  int w;
  int first = 1;
  fprintf(file, "{");
  for (w = 0; w < m->size; ++w)
    {
      int i;
      for (i = 0; i < 8; ++i)
	if (set[w] & (1 << i))
	  {
	    if (!first)
	      fprintf(stdout, ", ");
	    fprintf(stdout, "%i", w*8+i);
	    first = 0;
	  }
    }
  fprintf(file, "}");
}
#endif

/*
int int_idx(intptr_t i)
{
  return (int) i;
}

int main (void)
{
  {
    Tbs_mgr mgr7 = bitset_new_manager(7, (int (*) (void *)) int_idx);
    Tbs s7a = bitset_new(mgr7);
    Tbs s7b = bitset_new(mgr7);
    Tbs s7c = bitset_new(mgr7);
    bitset_insert(mgr7, s7a, (void *) (intptr_t) 2);
    bitset_insert(mgr7, s7a, (void *) (intptr_t) 5);
    bitset_insert(mgr7, s7b, (void *) (intptr_t) 2);
    bitset_insert(mgr7, s7b, (void *) (intptr_t) 6);
    bitset_union(mgr7, s7c, s7a, s7b);
    bitset_print(mgr7, s7a);
    bitset_print(mgr7, s7b);
    bitset_print(mgr7, s7c);
    bitset_free(mgr7, s7a);
    bitset_free(mgr7, s7b);
    bitset_free(mgr7, s7c);
    bitset_free_manager(&mgr7);
  }
  {
    Tbs_mgr mgr13 = bitset_new_manager(13, (int (*) (void *))int_idx);
    Tbs s13a = bitset_new(mgr13);
    Tbs s13b = bitset_new(mgr13);
    Tbs s13c = bitset_new(mgr13);
    bitset_insert(mgr13, s13a, (void *) (intptr_t) 0);
    bitset_insert(mgr13, s13a, (void *) (intptr_t) 1);
    bitset_insert(mgr13, s13a, (void *) (intptr_t) 2);
    bitset_insert(mgr13, s13a, (void *) (intptr_t) 5);
    bitset_insert(mgr13, s13b, (void *) (intptr_t) 2);
    bitset_insert(mgr13, s13b, (void *) (intptr_t) 6);
    bitset_diff(mgr13, s13c, s13a, s13b);
    bitset_print(mgr13, s13a);
    bitset_print(mgr13, s13b);
    bitset_print(mgr13, s13c);
    bitset_free(mgr13, s13a);
    bitset_free(mgr13, s13b);
    bitset_free(mgr13, s13c);
    bitset_free_manager(&mgr13);
  }
  {
    Tbs_mgr mgr32 = bitset_new_manager(32, (int (*) (void *))int_idx);
    Tbs s32a = bitset_new(mgr32);
    Tbs s32b = bitset_new(mgr32);
    Tbs s32c = bitset_new(mgr32);
    bitset_insert(mgr32, s32a, (void *) (intptr_t) 0);
    bitset_insert(mgr32, s32a, (void *) (intptr_t) 1);
    bitset_insert(mgr32, s32a, (void *) (intptr_t) 2);
    bitset_insert(mgr32, s32a, (void *) (intptr_t) 5);
    bitset_insert(mgr32, s32b, (void *) (intptr_t) 2);
    bitset_insert(mgr32, s32b, (void *) (intptr_t) 6);
    bitset_diff(mgr32, s32c, s32a, s32b);
    bitset_print(mgr32, s32a);
    bitset_print(mgr32, s32b);
    bitset_print(mgr32, s32c);
    bitset_free(mgr32, s32a);
    bitset_free(mgr32, s32b);
    bitset_free(mgr32, s32c);
    bitset_free_manager(&mgr32);
  }
  return 0;
}
*/
