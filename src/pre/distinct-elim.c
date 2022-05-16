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
  distinct operator removing in terms and formulas
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"

#include "list.h"
#include "DAG.h"
#include "DAG-ptr.h"
#include "distinct-elim.h"
#include "simp-sym.h"
#include "recursion.h"

/* #define DEBUG_DISTINCT_ELIM */

/*--------------------------------------------------------------*/

static Tstack_DAG distinct_elim_stack;

/*--------------------------------------------------------------*/

static TDAG
distinct_elim_aux(TDAG src)
{
  static unsigned i, j;
  static TDAG DAG, *PDAG;
  if (DAG_symb(src) != PREDICATE_DISTINCT)
    return src;
  if (DAG_arity(src) < 2)
    return DAG_TRUE;
  else if (DAG_arity(src) == 2)
    return DAG_neq(DAG_arg0(src), DAG_arg1(src));
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  memcpy(PDAG, DAG_args(src), DAG_arity(src) * sizeof(TDAG));
  simp_sym_notify(DAG_arity(src), PDAG);
  assert(stack_size(distinct_elim_stack) == 0);
  for (i = 0; i < DAG_arity(src); i++)
    for (j = i + 1; j < DAG_arity(src); j++)
      stack_push(distinct_elim_stack, 
		 DAG_neq(DAG_arg(src, i), DAG_arg(src, j)));
  DAG = DAG_new_stack(CONNECTOR_AND, distinct_elim_stack);
  stack_reset(distinct_elim_stack);
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
distinct_elim(TDAG src)
{
  TDAG dest;
#ifdef DEBUG_DISTINCT_ELIM
  fprintf(stderr, "Before distinct elimination\n");
  DAG_fprint(stderr, src);
#endif
  assert(distinct_elim_stack);
  dest = structural_recursion(src, distinct_elim_aux);
#ifdef DEBUG_DISTINCT_ELIM
  fprintf(stderr, "\n After distinct elimination\n");
  DAG_fprint(stderr, dest);
  fprintf(stderr, "\n");
#endif
  return dest;
}

/*--------------------------------------------------------------*/

void
distinct_elim_init(void)
{
  stack_INIT(distinct_elim_stack);
}

/*--------------------------------------------------------------*/

void
distinct_elim_done(void)
{
  stack_free(distinct_elim_stack);
}

