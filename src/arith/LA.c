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

#include <stdbool.h>

#include "stack.h"

#include "DAG.h"
#include "DAG-tmp.h"
#include "literal.h"
#include "veriT-status.h"

#include "numbers.h"
#include "simplex.h"

#include "LA.h"

/*
  --------------------------------------------------------------
  linking DAGs and LA variables
  --------------------------------------------------------------
*/

TSstack(_LAvar,TLAvar);

#define DAG_VAR_BLOCKED 0

static Tstack_LAvar DAG_var_table;

static TLAvar
LA_DAG_var(TDAG DAG)
{
  if (DAG + 1 > stack_size(DAG_var_table))
    stack_resize(DAG_var_table, DAG + 1);
  if (!DAG_var_table->data[DAG])
    DAG_var_table->data[DAG] = LAvar_new();
  return DAG_var_table->data[DAG];
}

/*--------------------------------------------------------------*/

static void
LA_DAG_var_replace(TDAG DAG1, TDAG DAG2)
{
  assert(DAG1 < DAG_var_table->size && DAG_var_table->data[DAG1]);
  stack_resize(DAG_var_table, DAG2);
  assert(!DAG_var_table->data[DAG2]);
  DAG_var_table->data[DAG2] = DAG_var_table->data[DAG1];
  DAG_var_table->data[DAG1] = DAG_VAR_BLOCKED;
}

/*--------------------------------------------------------------*/

/**
   \brief check if DAG is an arithmetic constant or not
   \param DAG a DAG
   \return true if DAG is an arithmetic constant */
static inline bool
LA_DAG_is_number(TDAG DAG)
{
  Tsymb_type symb_type = DAG_symb_type(DAG_symb(DAG));
  return (symb_type == SYMB_INTEGER ||
	  symb_type == SYMB_BINARY ||
	  symb_type == SYMB_HEX ||
	  symb_type == SYMB_RATIONAL) ||
    (DAG_symb(DAG) == FUNCTION_UNARY_MINUS &&
     LA_DAG_is_number(DAG_arg0(DAG))) ||
    (DAG_symb(DAG) == FUNCTION_DIV &&
     DAG_arity(DAG) == 2 &&
     LA_DAG_is_number(DAG_arg0(DAG)) &&
     LA_DAG_is_number(DAG_arg1(DAG)));
}

/*--------------------------------------------------------------*/

static void
LA_DAG_number(TDAG DAG, TLArational *Prat)
{
  Tsymb_type symb_type = DAG_symb_type(DAG_symb(DAG));
  if (symb_type == SYMB_INTEGER ||
      symb_type == SYMB_BINARY ||
      symb_type == SYMB_HEX ||
      symb_type == SYMB_RATIONAL)
    LArational_str(Prat, DAG_symb_name(DAG_symb(DAG)));
  else if (DAG_symb(DAG) == FUNCTION_UNARY_MINUS &&
	   LA_DAG_is_number(DAG_arg0(DAG)))
    {
      LArational_str(Prat, DAG_symb_name(DAG_symb(DAG_arg0(DAG))));
      LArational_neg(Prat);
    }
  else if (DAG_symb(DAG) == FUNCTION_DIV &&
	   DAG_arity(DAG) == 2 &&
	   LA_DAG_is_number(DAG_arg0(DAG)) &&
	   LA_DAG_is_number(DAG_arg1(DAG)))
    {
      TLArational rat2;
      LArational_str(Prat, DAG_symb_name(DAG_symb(DAG_arg0(DAG))));
      LArational_str(&rat2, DAG_symb_name(DAG_symb(DAG_arg1(DAG))));
      LArational_div(Prat, &rat2);
    }
}

/*--------------------------------------------------------------*/

/**
   \brief check if DAG should be considered as a variable
   \param DAG a DAG
   \return true if DAG is not an arithmetic expression */
static inline bool
LA_DAG_is_var(TDAG DAG)
{
  Tsymb symb = DAG_symb(DAG);
  return symb != FUNCTION_SUM &&
    symb != FUNCTION_PROD &&
    symb != FUNCTION_UNARY_MINUS &&
    symb != FUNCTION_UNARY_MINUS_ALT &&
    symb != FUNCTION_MINUS &&
    symb != FUNCTION_DIV;
}

/*
  --------------------------------------------------------------
  Creating a linear expression
  --------------------------------------------------------------
*/

typedef struct TDAG_monom {
  TLArational coef;
  TDAG var;
} TDAG_monom;

TSstack(_DAG_monom, TDAG_monom);
static Tstack_DAG_monom DAG_monoms;

typedef struct Tvar_bound {
  TLAvar LAvar;
  bool active:1;
  bool upper:1;
  bool strict:1;
} Tvar_bound;

TSstack(_var_bound, Tvar_bound);
static Tstack_var_bound var_bounds;

/*--------------------------------------------------------------*/

static int
cmp_DAG_monom(const TDAG * PDAG1, const TDAG * PDAG2)
{
  return ((*(int *)PDAG1) - (*(int *)PDAG2));
}

/*--------------------------------------------------------------*/

static void
LA_constraint_push(void)
{
  unsigned i, j;
  TLAsigned ppcm;
  TLAsigned * coefs;
  TLAvar * vars;
  /* sort and remove monoms on same variable */
  qsort(DAG_monoms->data, stack_size(DAG_monoms),
	sizeof(TDAG_monom), (TFcmp)cmp_DAG_monom);
  for (i = 0, j = 1; j < stack_size(DAG_monoms); j++)
    if (DAG_monoms->data[j].var == DAG_monoms->data[i].var)
      LArational_add(&DAG_monoms->data[i].coef, &DAG_monoms->data[j].coef);
    else
      DAG_monoms->data[i++] = DAG_monoms->data[j];
  stack_resize(DAG_monoms, i + 1);
  LAsigned_set_one(&ppcm);
  for (i = 0; i < stack_size(DAG_monoms); i++)
    LArational_ppcm(&ppcm, &stack_get(DAG_monoms, i).coef);
  MY_MALLOC(coefs, stack_size(DAG_monoms) * sizeof(TLAsigned));
  MY_MALLOC(vars, stack_size(DAG_monoms) * sizeof(TLAvar));
  for (i = 0; i < stack_size(DAG_monoms); i++)
    {
      coefs[i] = ppcm;
      LArational_mult_to_signed(&coefs[i], &stack_get(DAG_monoms, i).coef);
      vars[i] = LA_DAG_var(stack_get(DAG_monoms, i).var);
    }
  simplex_constraint_push(stack_size(DAG_monoms), vars, coefs);
  stack_reset(DAG_monoms);
}

/*--------------------------------------------------------------*/

static void
LA_remember_constraint(TDAG DAG, bool upper, bool strict)
{
  Tvar var = DAG_to_var(DAG);
  if (var_max + 1 > stack_size(var_bounds))
    stack_resize(var_bounds, var_max + 1);
  if (var_bounds->data[var].active)
    {
      assert(var_bounds->data[var].LAvar == LA_DAG_var(DAG) &&
	     var_bounds->data[var].upper == upper &&
	     var_bounds->data[var].strict == strict);
      return;
    }
  var_bounds->data[var].active = true;
  var_bounds->data[var].LAvar = LA_DAG_var(DAG);
  var_bounds->data[var].upper = upper;
  var_bounds->data[var].strict = strict;
}

/*
  --------------------------------------------------------------
  Collecting terms in formulas
  --------------------------------------------------------------
*/

typedef bool Tpol;

#define POL_NEG false
#define POL_POS true
#define inv_pol(a) (!(a))

/**
   \brief accumulates rat * DAG with polarity pol
   \param rat a rational number
   \param DAG a DAG
   \param pol a polarity */
static inline void
LA_notify_monom(TLArational rat, TDAG DAG, Tpol pol)
{
  if (pol == POL_NEG)
    LArational_neg(&rat);
  stack_inc(DAG_monoms);
  stack_top(DAG_monoms).coef = rat;
  stack_top(DAG_monoms).var = DAG;
}

/*--------------------------------------------------------------*/

static Tstack_DAG DAG_todo;

/**
   \brief accumulates all monoms in DAG, with polarity pol
   \param DAG a DAG
   \param pol a polarity */
static void
LA_notify_term(TDAG DAG, Tpol pol)
{
  TLArational rat;
  unsigned i;
  if (DAG_symb(DAG) == FUNCTION_SUM)
    {
      for (i = 0; i < DAG_arity(DAG); i++)
	LA_notify_term(DAG_arg(DAG, i), pol);
      return;
    }
  if (DAG_symb(DAG) == FUNCTION_PROD)
    {
      if (DAG_arity(DAG) != 2)
	my_error("DAG2LA: not implemented\n");
      if (LA_DAG_is_number(DAG_arg0(DAG)))
	{
	  if (LA_DAG_is_number(DAG_arg1(DAG)))
	    {
	      TLArational rat2;
	      LA_DAG_number(DAG_arg0(DAG), &rat);
	      LA_DAG_number(DAG_arg1(DAG), &rat2);
	      LArational_mult(&rat, &rat2);
	      LA_notify_monom(rat, 0, pol);
	      return;
	    }
	  if (LA_DAG_is_var(DAG_arg0(DAG)))
	    {
	      LA_DAG_number(DAG_arg0(DAG), &rat);
	      LA_notify_monom(rat, DAG_arg1(DAG), pol);
	      return;
	    }
	}
      if (LA_DAG_is_number(DAG_arg1(DAG)) && LA_DAG_is_var(DAG_arg0(DAG)))
	{
	  LA_DAG_number(DAG_arg1(DAG), &rat);
	  LA_notify_monom(rat, DAG_arg0(DAG), pol);
	  return;
	}
      my_error("DAG2LA: not implemented\n");
    }
  if (DAG_symb(DAG) == FUNCTION_UNARY_MINUS || 
      DAG_symb(DAG) == FUNCTION_UNARY_MINUS_ALT)
    {
      assert(DAG_arity(DAG) == 1);
      LA_notify_term(DAG_arg0(DAG), inv_pol(pol));
    }
  if (DAG_symb(DAG) == FUNCTION_MINUS)
    {
      LA_notify_term(DAG_arg0(DAG), inv_pol(pol));
      for (i = 1; i < DAG_arity(DAG); i++)
	LA_notify_term(DAG_arg(DAG, i), inv_pol(pol)); 
      return;
    }
  if (DAG_symb(DAG) == FUNCTION_DIV
      /* ||
	 DAG_symb(DAG) == FUNCTION_ABS ||
	 DAG_symb(DAG) == FUNCTION_MOD */)
    my_error("DAG2LA: not implemented\n");
  if (!LA_DAG_is_var(DAG))
    my_error("DAG2LA: not implemented\n");
  if (LA_DAG_is_number(DAG))
    {
      LA_DAG_number(DAG, &rat);
      LA_notify_monom(rat, 0, pol);
    }
  if (DAG_arity(DAG))
    stack_push(DAG_todo, DAG);
}

/*--------------------------------------------------------------*/

/**
   \brief introduces arithmetic definition for all arithmetic terms in DAG
   \param DAG a DAG */
static void
LA_notify_deep_terms(TDAG DAG)
{
  unsigned i;
  Tsymb symb = DAG_symb(DAG);
  if (DAG_tmp_bool[DAG])
    return;
  DAG_tmp_bool[DAG] = 1;
  if (symb == FUNCTION_SUM ||
      symb == FUNCTION_PROD ||
      symb == FUNCTION_UNARY_MINUS ||
      symb == FUNCTION_UNARY_MINUS_ALT ||
      symb == FUNCTION_MINUS ||
      symb == FUNCTION_DIV)
    { 
      TLArational rat;
      LArational_set_one(&rat);
      LArational_neg(&rat);
      /* IMPROVE asserts DAG has never been introduced */
      LA_notify_monom(rat, DAG, POL_NEG);
      LA_constraint_push();
    }
  else
    for (i = 0; i < DAG_arity(DAG); i++)
      LA_notify_deep_terms(DAG_arg(DAG,i));
}

/*--------------------------------------------------------------*/

/**
   \brief stores arithmetic definition for the atom,
   and all arithmetic terms in DAG
   \param DAG a DAG */
static inline void
LA_notify_atom(TDAG DAG)
{
  TLAdelta delta;
  LAdelta_set_zero(&delta);
  if (DAG_symb(DAG) == PREDICATE_LESS ||
      DAG_symb(DAG) == PREDICATE_LEQ ||
      DAG_symb(DAG) == PREDICATE_GREATER ||
      DAG_symb(DAG) == PREDICATE_GREATEREQ)
    {
      TLArational rat;
      Tpol pol = (DAG_symb(DAG) == PREDICATE_LESS ||
		  DAG_symb(DAG) == PREDICATE_LEQ);
      bool strict = (DAG_symb(DAG) == PREDICATE_GREATER ||
		     DAG_symb(DAG) == PREDICATE_LESS);
      LA_notify_term(DAG_arg0(DAG), pol);
      LA_notify_term(DAG_arg1(DAG), inv_pol(pol));
      LArational_set_one(&rat);
      LArational_neg(&rat);
      /* IMPROVE
	 - do not introduce a slack if, e.g. x < c
	 - do not introduce a slack if there is already a slack for
	 the same linear combination of variables modulo a coeff +
	 independent term. */
      /* IMPROVE asserts DAG has never been introduced */
      LA_notify_monom(rat, DAG, POL_NEG);
      LA_constraint_push();
      LA_remember_constraint(DAG, pol, strict);
    }
  else if (DAG_symb(DAG) == PREDICATE_ISINT)
    my_error("DAG2LA: not implemented\n");
  else
    stack_push(DAG_todo, DAG);
  while (stack_size(DAG_todo))
    LA_notify_deep_terms(stack_pop(DAG_todo));
}

/*--------------------------------------------------------------*/

/**
   \brief stores arithmetic definition for arithmetic atoms,
   and all arithmetic terms in DAG
   \param DAG a DAG */
static void
LA_notify_formula_aux(TDAG DAG)
{
  unsigned i;
  Tsymb symb = DAG_symb(DAG);
  if (DAG_tmp_bool[DAG])
    return;
  DAG_tmp_bool[DAG] = 1;
  if (boolean_connector(symb))
    for (i = 0; i < DAG_arity(DAG); i++)
      LA_notify_formula_aux(DAG_arg(DAG, i));
  if (quantifier(symb))
    return;
  if (symb == LET ||
      symb == LAMBDA ||
      symb == APPLY_LAMBDA ||
      symb == FUNCTION_ITE)
    my_error("DAG2LA: not implemented\n");
  else
    LA_notify_atom(DAG);
}

/*--------------------------------------------------------------*/

/**
   \brief stores arithmetic definition for arithmetic atoms,
   and all arithmetic terms in DAG
   \param DAG a DAG */
void
LA_notify_formula(TDAG DAG)
{
  DAG_tmp_reserve();
  LA_notify_formula_aux(DAG);
  DAG_tmp_reset_bool(DAG);
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Theory combination
  --------------------------------------------------------------  
*/

/* PF
   pol   strict upper  eps  simplex_lower/upper
   0     0      0      -1   up
   0     0      1       1   low
   0     1      0       0   up
   0     1      1       0   low
   1     0      0       0   low
   1     0      1       0   up
   1     1      0       1   low
   1     1      1      -1   up
*/
Tstatus
LA_assert(Tlit lit)
{
  Tvar var = lit_var(lit);
  /* IMPROVE: what type is pol?  Maybe propagate to the rest */
  bool pol = lit_pol(lit);
  TLAdelta delta;
  LAdelta_rat_delta(&delta, 0, 0, (pol ^ var_bounds->data[var].strict)?0:
		    ((pol ^ var_bounds->data[var].upper)?1:-1));
  return ((pol ^ var_bounds->data[var].upper)?simplex_assert_lower_bound:
	  simplex_assert_upper_bound)
    (var_bounds->data[var].LAvar, delta, lit);
}

/*--------------------------------------------------------------*/

Tstack_lit
LA_conflict(void)
{
  return simplex_conflict();
}

/*--------------------------------------------------------------*/

void
LA_init(const unsigned id)
{
  stack_INIT(DAG_monoms);
  stack_INIT(DAG_todo);
}

/*--------------------------------------------------------------*/

void
LA_done(void)
{
  stack_free(DAG_monoms);
  stack_free(DAG_todo);
}
