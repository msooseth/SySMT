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
  Module for simplification of formulas using unit clauses
  --------------------------------------------------------------
*/

#include "config.h"
#include "general.h"

/* #define DEBUG_US */

#ifdef DEBUG_US
#include "DAG-print.h"
#endif
#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "NO.h"
#include "polarities.h"
#include "simp-unit.h"
#include "veriT-status.h"
#include "options.h"


/*
  misc & (1 << 0) : DAG has been visited
  misc & (1 << 1) : DAG is unit with positive polarity
  misc & (1 << 2) : DAG is unit with negative polarity
  misc & (1 << 3) : atom (term) is clean
                    (quantifier-, apply-, ite-, var-free)
  misc & (1 << 4) : checked
*/

#define DAG_visited(DAG)  (DAG_misc(DAG) & (1 << 0))
#define DAG_unit_pos(DAG) (DAG_misc(DAG) & (1 << 1))
#define DAG_unit_neg(DAG) (DAG_misc(DAG) & (1 << 2))
#define DAG_clean(DAG)    (DAG_misc(DAG) & (1 << 3))
#define DAG_checked(DAG)  (DAG_misc(DAG) & (1 << 4))

#define DAG_set_visited(DAG)  DAG_misc(DAG) |= 1 << 0;
#define DAG_set_unit_pos(DAG) DAG_misc(DAG) |= 1 << 1;
#define DAG_set_unit_neg(DAG) DAG_misc(DAG) |= 1 << 2;
#define DAG_set_clean(DAG)    DAG_misc(DAG) |= 1 << 3;
#define DAG_set_checked(DAG)  DAG_misc(DAG) |= 1 << 4;

static int us_conflict = 0;

/*
  --------------------------------------------------------------
  Finding unit clauses
  --------------------------------------------------------------
*/

/* PF
   A clean literal is ite, lamba, apply, and quantifier-free.
   It can then been fully handled by the NO module.
   This sub-module is responsible to compute
   - the number of clean unit literals (us_nb_units)
   - the number of clean non-unit literals (us_nb_non_units)
   - the number of clauses (us_nb_clauses), i.e. a indication of
     the importance of the Boolean structure

   All literals are marked such that
   DAG_unit_pos, DAG_unit_neg, DAG_clean are accurate

   Also, it adds all clean unit literals to NO, and
   corresponding DAGs to us_units.
*/

static int us_nb_units = 0;
static int us_nb_non_units = 0;
static int us_nb_clauses = 0;
static Tstack_DAG us_units;

/*--------------------------------------------------------------*/

static bool
DAG_is_clean(TDAG src)
/* PF src is an atom or term without
   quantifier, lambda, apply, ite and variable */
{
  unsigned i;
  if (DAG_visited(src))
    return DAG_clean(src);
  DAG_set_visited(src);
  if (quantifier(DAG_symb(src)) ||
      DAG_symb(src) == FUNCTION_ITE ||
      DAG_symb(src) == LAMBDA ||
      DAG_symb(src) == APPLY_LAMBDA ||
      DAG_symb_type(DAG_symb(src)) == SYMB_VARIABLE)
    return false;
  for (i = 0; i < DAG_arity(src); i++)
    if (!DAG_is_clean(DAG_arg(src, i)))
      return false;
  DAG_set_clean(src);
  return true;
}

/*--------------------------------------------------------------*/

static void
us_count_non_units(TDAG src)
{
  unsigned i;
  if (DAG_visited(src))
    return;
  if (boolean_connector(DAG_symb(src)))
    for (i = 0; i < DAG_arity(src); i++)
      us_count_non_units(DAG_arg(src, i));
  else if (quantifier(DAG_symb(src)))
    us_count_non_units(DAG_argn(src));
  else if (DAG_is_clean(src))
    us_nb_non_units++;
  DAG_set_visited(src);
}

/*--------------------------------------------------------------*/

static void
us_identify_units_aux(TDAG src, int pol)
/* PF identify unit literals, add them in NO
   returns 1 if and only if it is useful to continue the process
   - there is some Boolean structure
   - there are some unit literals */
{
  unsigned i;
  if (DAG_visited(src) &&
      ((pol==POL_POS)?DAG_unit_pos(src):DAG_unit_neg(src)))
    return;
  if (pol==POL_POS)
    DAG_set_unit_pos(src)
  else
    DAG_set_unit_neg(src);
  if (DAG_unit_neg(src) && DAG_unit_pos(src))
    {
      us_conflict = 1;
      return;
    }
  if (!boolean_connector(DAG_symb(src)))
    {
      Tlit literal;
#ifdef DEBUG_US
      my_DAG_message("Unit check: %D\n", src);
#endif
      if (quantifier(DAG_symb(src)))
	{
	  us_count_non_units(src);
	  return;
	}
      /* PF do not push because it contains
	 quantifier, lambda, apply, and ite, not well handled by CC */
      if (!DAG_is_clean(src))
	return;
      literal = DAG_to_lit(src);
      if (pol == POL_NEG)
	literal = lit_neg(literal);
      if (NO_push(literal) == UNSAT)
	us_conflict = 1;
      us_nb_units++;
#ifdef DEBUG_US
      my_DAG_message("Unit found: %D\n", src);
#endif
      stack_push(us_units, DAG_dup((pol==POL_POS)?src:DAG_not(src)));
      DAG_Pflag_set(src, DAG_ptr_of((pol==POL_POS)?DAG_TRUE:DAG_FALSE));
      return;
    }
  /* PF examine Boolean structure */
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      us_identify_units_aux(DAG_arg0(src), INV_POL(pol));
      DAG_set_visited(src);
      return;
    }
  if (pol == POL_POS && DAG_symb(src) == CONNECTOR_AND)
    {
      for (i = 0; i < DAG_arity(src); i++)
	us_identify_units_aux(DAG_arg(src, i), POL_POS);
      DAG_set_visited(src);
      return;
    }
  if (pol == POL_NEG && DAG_symb(src) == CONNECTOR_OR)
    {
      for (i = 0; i < DAG_arity(src); i++)
	us_identify_units_aux(DAG_arg(src, i), POL_NEG);
      DAG_set_visited(src);
      return;
    }
  if (pol == POL_NEG && DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      us_identify_units_aux(DAG_arg0(src), POL_POS);
      us_identify_units_aux(DAG_arg1(src), POL_NEG);      
      DAG_set_visited(src);
      return;
    }
  us_nb_clauses++;
  us_count_non_units(src);
}

/*--------------------------------------------------------------*/

static int
us_identify_units(TDAG src)
/* PF identify unit literals, add them in NO
   returns 1 if and only if it is useful to continue the process
   - there is some Boolean structure
   - there are some unit literals */
{
  us_nb_units = 0;
  us_nb_clauses = 0;
  us_nb_non_units = 0;
  us_identify_units_aux(src, POL_POS);
#ifdef DEBUG_US
  my_message("us_nb_units %d\n", us_nb_units);
  my_message("us_nb_clauses %d\n", us_nb_clauses);
  my_message("us_nb_non_units %d\n", us_nb_non_units);
#endif
  if (us_conflict)
    return 1;
  if (us_nb_units == 0)
    return 0;
  if (us_nb_clauses < 2)
    return 0;
  if (us_nb_non_units < 3)
    return 0;
  return 1;
}

/*
  --------------------------------------------------------------
  Checking consistency of unit clauses
  --------------------------------------------------------------
*/

static int
us_check_consistency(void)
/* PF returns 1 if the unit literals are consistent */
{
  return !us_conflict;
}

/*
  --------------------------------------------------------------
  Replacing deduced literals
  --------------------------------------------------------------
*/

static bool
us_check_atoms_rewrite_aux(TDAG src)
/* PF check if the value of any literal within src is implied by
   unit literals.  Populates Pflag with the rewritten formula.
   returns 1 if rewritten formula is different from original. */
{
  Tlit lit;
  if (DAG_Pflag(src))
    return src != DAG_of_ptr(DAG_Pflag(src));
  if (boolean_connector(DAG_symb(src)))
    {
      unsigned i;
      bool changed = false;
      for (i = 0; i < DAG_arity(src); i++)
	changed |= us_check_atoms_rewrite_aux(DAG_arg(src, i));
      if (changed)
	{
	  TDAG * PDAG, tmp;
	  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
	  for (i = 0; i < DAG_arity(src); i++)
	    PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(src, i)));
	  tmp = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
	  DAG_Pflag_set(src, DAG_ptr_of(tmp));
	  return true;
	}
      DAG_Pflag_set(src, DAG_ptr_of(src));
      return false;
    }
  if (quantifier(DAG_symb(src)))
    {
      unsigned i;
      bool changed = false;
      changed |= us_check_atoms_rewrite_aux(DAG_argn(src));
      if (changed)
	{
	  TDAG * PDAG, tmp;
	  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
	  for (i = 0; i < DAG_arity(src) - 1u; i++)
	    PDAG[i] = DAG_arg(src, i);
	  PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(src, i)));
	  tmp = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
	  DAG_Pflag_set(src, DAG_ptr_of(tmp));
	  return true;
	}
      DAG_Pflag_set(src, DAG_ptr_of(src));
      return false;
    }
  if (!DAG_clean(src))
    {
      DAG_Pflag_set(src, DAG_ptr_of(src));
      return false;
    }
  lit = DAG_to_lit(src);
  if (NO_push(lit) == UNSAT)
    {
#ifdef DEBUG_US
      my_DAG_message("Replacing %D with FALSE\n", src);
#endif
      DAG_Pflag_set(src, DAG_ptr_of(DAG_FALSE));
      NO_pop();
      return true;
    }
  NO_pop();
  lit = lit_neg(lit);
  if (NO_push(lit) == UNSAT)
    {
#ifdef DEBUG_US
      my_DAG_message("Replacing %D with TRUE\n", src);
#endif
      DAG_Pflag_set(src, DAG_ptr_of(DAG_TRUE));
      NO_pop();
      return true;
    }

  /* HERE INTEGRATE REWRITING */

  DAG_Pflag_set(src, DAG_ptr_of(src));
  NO_pop();
  return false;
}

/*--------------------------------------------------------------*/

static TDAG
us_check_atoms_rewrite(TDAG src)
/* PF check for every atom if it should be true or false */
{
  us_check_atoms_rewrite_aux(src);
  stack_push(us_units, DAG_dup(DAG_of_ptr(DAG_Pflag(src))));
  return DAG_dup(DAG_new_stack(CONNECTOR_AND, us_units));
}

/*
  --------------------------------------------------------------
  Cleaning
  --------------------------------------------------------------
*/

static void
us_clean(TDAG src)
/* PF empty NO queue and clean bits on the DAG */
{
  unsigned i;
  if (!DAG_misc(src) && !DAG_Pflag(src))
    return;
  if ((DAG_unit_pos(src) || DAG_unit_neg(src)) && DAG_clean(src))
    NO_pop();
  DAG_misc_set(src, 0);
  DAG_Pflag_set(src, NULL);
  for (i = 0; i < DAG_arity(src); i++)
    us_clean(DAG_arg(src, i));
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

TDAG
simplify_unit(TDAG src)
{
  TDAG dest;
  int stop = 0;
  unsigned i;
  us_conflict = 0;
#ifdef DEBUG_US
  my_DAG_message("SRC: %D\n", src);
#endif
  /* PF this is only useful for formulas that
     have some boolean structure */
  if (!us_identify_units(src))
    {
      dest = DAG_dup(src);
      stop = 1;
    }
  if (!stop && !us_check_consistency())
    {
      dest = DAG_dup(DAG_FALSE);
      stop = 1;
    }
  if (!stop)
    dest = us_check_atoms_rewrite(src);
  us_clean(src);
  for (i = 0; i < stack_size(us_units); ++i)
    DAG_free(stack_get(us_units, i));
  stack_reset(us_units);
  literal_reset();
#ifdef DEBUG_US
  my_DAG_message("DEST: %D\n", dest);
#endif
  return dest;
}

/*--------------------------------------------------------------*/

void
simplify_unit_init(void)
{
  stack_INIT(us_units);
}

/*--------------------------------------------------------------*/

void
simplify_unit_done(void)
{
  stack_free(us_units);
}
