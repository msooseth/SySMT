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
  ite (functions) removing in formulas
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>

#include "general.h"
#include "types.h"

#include "DAG.h"
#include "ite-elim.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "statistics.h"

/* #define DEBUG_ITE_ELIM */
/* #define ITE_STAT */

#ifdef ITE_STAT
static int stat_ite = 0;
#endif

static Tstack_DAG ite_terms;
static int ite_term_id = 0;

static Thash hash_ite = NULL;
struct TDAG_assoc
{
  TDAG DAG_ite, DAG_const;
};

/*
  --------------------------------------------------------------
  Inspecting formulas for ite terms
  --------------------------------------------------------------
*/

static Tunsigned
ite_hash_function(void * Pvoid)
{
  struct TDAG_assoc * PDAG_assoc = Pvoid;
  return DAG_hash(PDAG_assoc->DAG_ite);
}

/*--------------------------------------------------------------*/

static Tsigned 
ite_equal(void * Pvoid1, void * Pvoid2)
{
  return ((struct TDAG_assoc *)Pvoid1)->DAG_ite ==
    ((struct TDAG_assoc *)Pvoid2)->DAG_ite;
}

/*--------------------------------------------------------------*/

static void
ite_free_function(void * Pvoid)
{
  DAG_free(((struct TDAG_assoc *)Pvoid)->DAG_ite);
  DAG_free(((struct TDAG_assoc *)Pvoid)->DAG_const);
  free((struct TDAG_assoc *)Pvoid);
}

/*--------------------------------------------------------------*/

static TDAG
register_ite(TDAG DAG)
{
  char name[13];
  struct TDAG_assoc * PDAG_assoc, * PDAG_assoc2;
  if (ite_term_id >= 100000)
    my_error("get_ite_new_term: too many terms\n");
  MY_MALLOC(PDAG_assoc, sizeof(struct TDAG_assoc));
  PDAG_assoc->DAG_ite = DAG;
  PDAG_assoc2 = hash_lookup(hash_ite, PDAG_assoc);
  if (PDAG_assoc2)
    {
      free(PDAG_assoc);
      return PDAG_assoc2->DAG_const;
    }
#ifdef ITE_STAT
  stat_inc(Pstats, stat_ite);
#endif
  PDAG_assoc->DAG_ite = DAG_dup(DAG);
  sprintf(name, "iteterm%d", ite_term_id++);
  PDAG_assoc->DAG_const =
    DAG_dup(DAG_new_args(DAG_symb_new(name, SYMB_ITE, DAG_sort(DAG)), NULL));
  hash_insert(hash_ite, PDAG_assoc);
  return PDAG_assoc->DAG_const;
}

/*
  --------------------------------------------------------------
  Inspecting formulas for ite terms
  --------------------------------------------------------------
*/

static void
get_ite_terms(TDAG src)
     /* PF adds ite terms of DAG to ite_terms (different)
        ite-terms used in DAG */
{
  unsigned i;
  if (DAG_flag(src))
    return;
  if (binder(DAG_symb(src)) || DAG_symb(src) == APPLY_LAMBDA)
    return;
  for (i = 0; i < DAG_arity(src); i++)
    get_ite_terms(DAG_arg(src, i));
  if (DAG_symb(src) == FUNCTION_ITE)
    stack_push(ite_terms, src);
  DAG_flag_set(src, 1);
}

/*--------------------------------------------------------------*/

static int
get_ite_free(TDAG DAG)
     /* PF Takes a Boolean formula, 
        Associate to a ite-free formula to DAG in Pflag
        returns 0 if formula this last formula is DAG, 1 otherwise.
        In fact, returns 0 iff DAG is ite free. */
{
  unsigned i;
  bool changed = false;
  if (DAG_Pflag(DAG))
    return DAG_of_ptr(DAG_Pflag(DAG)) != DAG;
  if (binder(DAG_symb(DAG)) || DAG_symb(DAG) == APPLY_LAMBDA)
    {
      DAG_Pflag_set(DAG, DAG_ptr_of(DAG));
      return 0;
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    changed |= get_ite_free(DAG_arg(DAG, i));
  if (changed)
    {
      TDAG *Psub = NULL, tmp;
      MY_MALLOC(Psub, DAG_arity(DAG) * sizeof(TDAG *));
      for (i = 0; i < DAG_arity(DAG); i++)
	Psub[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG, i)));
      tmp = DAG_new(DAG_symb(DAG), DAG_arity(DAG), Psub);
      DAG_Pflag_set(DAG, DAG_ptr_of(tmp));
      return 1;
    }
  DAG_Pflag_set(DAG, DAG_ptr_of(DAG));
  return 0;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
ite_elim_init(void)
{
#ifdef ITE_STAT
  stat_ite = stat_new(Pstats, "ite", "Introduced ite terms", "%4d");
#endif
  hash_ite = hash_new(1024, 
		      (TFhash) ite_hash_function, 
		      (TFequal) ite_equal,
		      (TFfree) ite_free_function);
  stack_INIT(ite_terms);
}

/*--------------------------------------------------------------*/

void
ite_elim_done(void)
{
  stack_free(ite_terms);
  hash_free(&hash_ite);
}

/*--------------------------------------------------------------*/

TDAG
ite_elim(TDAG DAG)
{
  TDAG result;
  Tstack_DAG args;
  unsigned i;
  /* Get ite-term list */
  assert(stack_size(ite_terms) == 0);
  get_ite_terms(DAG);
  DAG_reset_flag(DAG);
  if (stack_size(ite_terms) == 0)
    {
#ifdef DEBUG_ITE_ELIM
      fprintf(stderr, "No ite found\n");
#endif
      return DAG_dup(DAG);
    }
  /* Get a substitute term for each of these ite */
  for (i = 0; i < stack_size(ite_terms); ++i)
    {
      TDAG DAG_ite = stack_get(ite_terms, i);
      TDAG tmp = register_ite(DAG_ite);
      DAG_Pflag_set(DAG_ite, DAG_ptr_of(tmp));
    }
  /* Get formula with substitute terms */
  if (!get_ite_free(DAG))
    my_error("ite_eliminate: internal error\n");

  /* Build defining formula for substitute terms */
  stack_INIT_s(args, 1 + stack_size(ite_terms));
  stack_push(args, DAG_of_ptr(DAG_Pflag(DAG)));
  for (i = 0; i < stack_size(ite_terms); ++i)
    {
      TDAG DAG_ite = stack_get(ite_terms, i);
      TDAG condition, then_case, else_case;
      get_ite_free(DAG_arg(DAG_ite, 0));
      condition = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG_ite, 0)));
      get_ite_free(DAG_arg(DAG_ite, 1));
      then_case = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG_ite, 1)));
      get_ite_free(DAG_arg(DAG_ite, 2));
      else_case = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG_ite, 2)));
      DAG_ite = DAG_of_ptr(DAG_Pflag(DAG_ite));
      DAG_ite = DAG_ite(condition, DAG_eq(DAG_ite, then_case),
			DAG_eq(DAG_ite, else_case));
      stack_push(args, DAG_ite);
    }
  result = DAG_dup(DAG_new_stack(CONNECTOR_AND, args));

  /* Clean */
  DAG_reset_Pflag(DAG);
  stack_free(args);
  stack_reset(ite_terms);
#ifdef DEBUG_ITE_ELIM
  fprintf(stderr, "Before ite elimination\n");
  DAG_fprint_smt2_bench(stderr, DAG, 0);
  fprintf(stderr, "\n After ite elimination\n");
  DAG_fprint_smt2_bench(stderr, result, 0);
  fprintf(stderr, "\n");
#endif
  return result;
}

/*--------------------------------------------------------------*/
