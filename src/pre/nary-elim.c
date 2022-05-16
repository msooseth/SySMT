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
  removing n-ary operators in terms and formulas
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>

#include "general.h"

#include "list.h"
#include "DAG.h"
#include "nary-elim.h"
#include "recursion.h"

/* #define DEBUG_NARY_ELIM */

/*--------------------------------------------------------------*/

/* (f t1 · · · tn ) --> (f · · · (f (f t1 t2 ) t3 ) · · · tn ) */

static TDAG
left_assoc_elim(TDAG src)
{
  unsigned i;
  TDAG tmp;

  if (DAG_arity(src) <= 2)
    return src;

  tmp = DAG_new_args(DAG_symb(src), DAG_arg0(src), DAG_arg1(src), DAG_NULL);
  for (i = 2; i < DAG_arity(src); i++)
    tmp = DAG_new_args(DAG_symb(src), tmp, DAG_arg(src, i), DAG_NULL);
  return tmp;
}

/*--------------------------------------------------------------*/

/* (f t1 · · · tn ) --> (f t1 (f t2 · · · (f tn−1 tn ) · · · ) */

static TDAG
right_assoc_elim(TDAG src)
{
  unsigned i;
  TDAG tmp;

  if (DAG_arity(src) <= 2)
    return src;

  tmp = DAG_new_args(DAG_symb(src), DAG_arg(src, DAG_arity(src) - 2),
		     DAG_arg(src, DAG_arity(src) - 1), DAG_NULL);
  for (i = DAG_arity(src) - 2; i-- != 0; )
    tmp = DAG_new_args(DAG_symb(src), DAG_arg(src, i), tmp, DAG_NULL);
  return tmp;
}

/*--------------------------------------------------------------*/

/* (f t1 · · · tn ) --> (and (f t1 t2 ) (f t2 t3 )· · · (f tn−1 tn )) */

static TDAG
chainable_elim(TDAG src)
{
  unsigned i;
  TDAG * tmp;

  if (DAG_arity(src) <= 2)
    return src;

  MY_MALLOC(tmp, (DAG_arity(src) - 1u) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src) - 1u; i++)
    tmp[i] = DAG_new_args(DAG_symb(src), DAG_arg(src, i), DAG_arg(src,i + 1), DAG_NULL);
  return DAG_new(CONNECTOR_AND, DAG_arity(src) - 1u, tmp);
}

/*--------------------------------------------------------------*/

/* (f t1 · · · tn ) --> (and (f t1 t2 ) (f t2 t3 )· · · (f tn−1 tn )) */

static TDAG
nary_elim_node(TDAG src)
{
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    return right_assoc_elim(src);
  if ( (DAG_symb(src) == CONNECTOR_XOR) ||
       (DAG_symb(src) == FUNCTION_MINUS))
    return left_assoc_elim(src);
  if ( (DAG_symb(src) == PREDICATE_LESS) ||
       (DAG_symb(src) == PREDICATE_LEQ) ||
       (DAG_symb(src) == PREDICATE_GREATER) ||
       (DAG_symb(src) == PREDICATE_GREATEREQ) ||
       (DAG_symb(src) == CONNECTOR_EQUIV)  ||
       (DAG_symb(src) == PREDICATE_EQ))
    return chainable_elim(src);
  return src;
}

/*--------------------------------------------------------------*/

TDAG
nary_elim(TDAG src)
{
  TDAG dest;
#ifdef DEBUG_NARY_ELIM
  fprintf(stderr, "Before nary elimination\n");
  DAG_fprint(stderr, src);
#endif
  dest = structural_recursion(src, nary_elim_node);
#ifdef DEBUG_NARY_ELIM
  fprintf(stderr, "\n After nary elimination\n");
  DAG_fprint(stderr, dest);
  fprintf(stderr, "\n");
#endif
  return dest;
}
