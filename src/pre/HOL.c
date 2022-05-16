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
  Module for handling higher order constants, beta reduction,...
  --------------------------------------------------------------
*/

/* PF IMPROVE
   - rename bound variables, so that better sharing */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "config.h"

#include "assoc.h"
#include "general.h"
#include "list.h"
#include "table.h"

#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "DAG-print.h"
#include "DAG-symb-DAG.h"
#include "DAG-sort-pm.h"
#include "polarities.h"
#include "recursion.h"

#include "binder-rename.h"

#include "HOL.h"

/* #define DEBUG_HOL */
/* #define DEBUG_HOL_MACRO */

static void macro_free_Pflag(TDAG src);

/*
  --------------------------------------------------------------
  General functions
  --------------------------------------------------------------
*/

static int
is_FOL_node(TDAG src)
{
  return DAG_sort(src) && 
    (!DAG_sort_arity(DAG_sort(src)) || DAG_sort_instance(DAG_sort(src)));
  /* every node should be of non-functional sort */
}

/*--------------------------------------------------------------*/

int
is_FOL (TDAG src)
{
  return structural_recursion_pred(src, is_FOL_node);
}

/*--------------------------------------------------------------*/

static int
is_FOL_strict_node(TDAG src)
{
  unsigned i;
  if (DAG_symb(src) == LET ||
      DAG_symb(src) == LAMBDA ||
      DAG_symb(src) == APPLY_LAMBDA)
    return 0;
  if (quantifier(DAG_symb(src)))
    {
      assert(DAG_arity(src) > 0);
      for (i = 0; i < DAG_arity(src) - 1u; i++)
	if (DAG_sort(DAG_arg(src, i)) == SORT_BOOLEAN)
	  return 0;
      return 1;
    }
  if (DAG_arity(src) &&
      !(boolean_connector(DAG_symb(src)) || DAG_symb(src) == FUNCTION_ITE))
    for (i = 0; i < DAG_arity(src); i++)
      if (DAG_sort(DAG_arg(src, i)) == SORT_BOOLEAN)
	return (DAG_arg(src, i) == DAG_TRUE || DAG_arg(src, i) == DAG_FALSE);
  if (DAG_symb(src) == FUNCTION_ITE && DAG_sort(DAG_arg1(src)) == SORT_BOOLEAN)
    return 0;    
  return DAG_sort(src) && !DAG_sort_polymorphic(DAG_sort(src)) &&
    (!DAG_sort_arity(DAG_sort(src)) || DAG_sort_instance(DAG_sort(src)));
  /* every node should be of non-functional sort */
}

/*--------------------------------------------------------------*/

int
is_FOL_strict (TDAG src)
{
  return structural_recursion_pred(src, is_FOL_strict_node);
}

/*
  --------------------------------------------------------------
  General functions                                            
  --------------------------------------------------------------
*/

static int
is_binder_free_node(TDAG src)
{
  return !(binder(DAG_symb(src)) || DAG_symb(src) == LET);
}

/*--------------------------------------------------------------*/

int
is_binder_free(TDAG src)
{
  return structural_recursion_pred(src, is_binder_free_node);
}

/*--------------------------------------------------------------*/

static int
is_quantifier_free_node(TDAG src)
{
  return !quantifier(DAG_symb(src));
}

/*--------------------------------------------------------------*/

int
is_quantifier_free(TDAG src)
{
  return structural_recursion_pred(src, is_quantifier_free_node);
}

/*
  --------------------------------------------------------------
  DAG preparation (misc settings)
  --------------------------------------------------------------
*/

#if 0

/* PF
   misc is set like this
   BITS 0 & 1 are set to used polarity of the subformula inside formula
   BIT 2 is set to 1 iff formula contain quantifiers
   BIT 8 to 15 are used to count the number of binders inside formula
*/

#define GET_POL(F) (DAG_misc(F) & 3)
#define SET_POL(F, P) { DAG_misc(F) &= ~3; DAG_misc(F) |= P; }

#define GET_QUANTIFIED(F) ((DAG_misc(F) & 4) >> 2)
#define SET_QUANTIFIED(F) { DAG_misc(F) |= 4; }

#define GET_HIGH_BOUND(F) ((DAG_misc(F) & 0xFF00) >> 8)
#define SET_HIGH_BOUND(F,n)					\
  {								\
    if ((n) > 0xFF) my_error("too many imbricated binders\n");	\
    DAG_misc(F) &= ~0xFF00;					\
    DAG_misc(F) |= (n) << 8;					\
  }

/*--------------------------------------------------------------*/

static void
set_polarity (TDAG src, int pol)
{
  int i;
  if ((GET_POL (src) & pol) == pol)
    return;
  SET_POL (src, GET_POL (src) | pol);
  if (DAG_symb(src) == CONNECTOR_ITE)
    {
      set_polarity (DAG_arg0(src), POL_BOTH);
      set_polarity (DAG_arg1(src), pol);
      set_polarity (DAG_arg(src, 2), pol);
      return;
    }
  else if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      set_polarity (DAG_arg0(src), INV_POL (pol));
      set_polarity (DAG_arg1(src), pol);
      return;
    }
  else if (DAG_symb(src) == CONNECTOR_NOT)
    pol = INV_POL (pol);
  else if (DAG_symb(src) == CONNECTOR_EQUIV || DAG_symb(src) == CONNECTOR_XOR)
    pol = POL_BOTH;
  if (boolean_connector (DAG_symb(src)) || quantifier (DAG_symb(src)))
    for (i = 0; i < DAG_arity(src); i++)
      set_polarity (DAG_arg(src, i), pol);
}

/*--------------------------------------------------------------*/

static void
set_stats_aux (TDAG src)
{
  int i, n;
  if (DAG_flag(src))
    return;
  DAG_flag(src)++;
  if (quantifier (DAG_symb(src)))
    SET_QUANTIFIED (src);
  if (quantifier (DAG_symb(src)) || DAG_symb(src) == LAMBDA)
    {
      set_stats_aux (DAG_argn(src));
      SET_HIGH_BOUND (src, DAG_arity(src) - 1 +
		      GET_HIGH_BOUND (DAG_argn(src)));
      if (GET_QUANTIFIED (DAG_argn(src)))
	SET_QUANTIFIED (src);
      return;
    }
  for (i = 0, n = 0; i < DAG_arity(src); i++)
    {
      set_stats_aux (DAG_arg(src, i));
      if (n < GET_HIGH_BOUND (DAG_arg(src, i)))
	n = GET_HIGH_BOUND (DAG_arg(src, i));
      if (GET_QUANTIFIED (DAG_arg(src, i)))
	SET_QUANTIFIED (src);
    }
  SET_HIGH_BOUND (src, n);
}

/*--------------------------------------------------------------*/

static void
set_stats (TDAG src)
{
  set_polarity (src, POL_POS);
  set_stats_aux (src);
  DAG_reset_flag (src);
}

/*--------------------------------------------------------------*/

static void
reset_stats_aux (TDAG src)
{
  int i;
  if (DAG_flag(src))
    return;
  DAG_flag_set(src, 1);
  DAG_misc_set(src, 0);
  for (i = 0; i < DAG_arity(src); i++)
    reset_stats_aux (DAG_arg(src, i));
}

/*--------------------------------------------------------------*/

static void
reset_stats (TDAG src)
{
  reset_stats_aux (src);
  DAG_reset_flag (src);
}

#endif

/*
  --------------------------------------------------------------
  Beta reduction
  --------------------------------------------------------------
*/

/* PF This submodule applies lambda expressions exhaustively
   DAG_symb_(set or get)_bind are used to link variables and their values
   The code here is complicated also because of the fact that functions 
   are not handled as normal terms within DAG module */

static TDAG
beta_reduce_subst (TDAG src)
{
  unsigned i;
  TDAG *PDAG, *PDAG2, dest, tmp;
  if (binder(DAG_symb(src)))
    {
      /* PF within the scope of a binder,
	 the variables do not have a substitution value */
      MY_MALLOC (PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src) - 1u; i++)
	{
	  PDAG[i] = DAG_arg(src, i);
	  assert(!DAG_symb_DAG[DAG_symb(PDAG[i])]);
	}
      tmp = PDAG[i] = beta_reduce_subst(DAG_arg(src, i));
      dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
      DAG_free(tmp);
      return dest;
    }
  if (!DAG_arity(src))
    {
      if (DAG_symb_DAG[DAG_symb(src)])
	return DAG_dup(DAG_symb_DAG[DAG_symb(src)]);
      return DAG_dup(src);
    }
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof (TDAG));
  if (DAG_symb_DAG[DAG_symb(src)])
    {
      /* (f X1 ... Xn) where f is bound with some term */
      if (DAG_symb(DAG_symb_DAG[DAG_symb(src)]) == LAMBDA)
	{
	  /* f is a LAMBDA */
	  MY_MALLOC(PDAG2, (DAG_arity(src) + 1u) * sizeof(TDAG));
	  PDAG2[0] = DAG_symb_DAG[DAG_symb(src)];
	  for (i = 0; i < DAG_arity(src); i++)
	    PDAG[i] = PDAG2[i + 1u] = beta_reduce_subst(DAG_arg(src, i));
	  dest = DAG_dup(DAG_new(APPLY_LAMBDA, DAG_arity(src) + 1u, PDAG2));
	}
      else
	{
	  /* f is another function */
	  assert(DAG_arity(DAG_symb_DAG[DAG_symb(src)]) == 0);
	  MY_MALLOC(PDAG2, DAG_arity(src) * sizeof(TDAG));
	  for (i = 0; i < DAG_arity(src); i++)
	    PDAG[i] = PDAG2[i] = beta_reduce_subst(DAG_arg(src, i));
	  dest = DAG_dup(DAG_new(DAG_symb(DAG_symb_DAG[DAG_symb(src)]),
				 DAG_arity(src), PDAG2));
	}
    }
  else
    {
      /* (f X1 ... Xn) where f is not bound with some term */      
      MY_MALLOC(PDAG2, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
	PDAG[i] = PDAG2[i] = beta_reduce_subst(DAG_arg(src, i));
      dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG2));
    }
  for (i = 0; i < DAG_arity(src); i++)
    DAG_free(PDAG[i]);
  free (PDAG);
  return dest;
}

/*--------------------------------------------------------------*/

static TDAG
beta_reduce_aux2 (TDAG src);

static TDAG
beta_reduce_apply(TDAG src)
/* PF src should be an apply.  Returns the simplified term
   Non-destructive, DAG_dup included */
{
  unsigned i;
  TDAG lambda, * PDAG, dest;

  assert (DAG_symb(src) == APPLY_LAMBDA);
  lambda = beta_reduce_aux2(DAG_arg0(src));
  /* PDAG will store the apply-free arguments */
  MY_MALLOC(PDAG, (DAG_arity(src) - 1u) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src) - 1u; i++)
    PDAG[i] = beta_reduce_aux2(DAG_arg(src, i + 1));

  if (!DAG_arity(lambda)) /* lambda is a named function */
    {
      dest = DAG_dup(DAG_new(DAG_symb(lambda), DAG_arity(src) - 1u, PDAG));
      for (i = 0; i < DAG_arity(dest); i++)
	DAG_free(DAG_arg(dest, i));
      DAG_free(lambda);
      return dest;
    }
  if (DAG_symb(lambda) != LAMBDA)
    my_error ("beta_reduce : strange apply\n");
  if (DAG_arity(lambda) < 2 && DAG_arity(lambda) != DAG_arity(src))
    my_error ("beta_reduce : strange apply\n");
  for (i = 0; i < DAG_arity(lambda) - 1u; i++)
    {
      if (DAG_symb_DAG[DAG_symb(DAG_arg(lambda, i))])
	my_error("beta_reduce : strange apply\n");
      DAG_symb_DAG[DAG_symb(DAG_arg(lambda, i))] = PDAG[i];
    }
  /* DD+PF

     There should be no capture here since the binder_rename invariant
     is satisfied, i.e. two different binders bound different
     variables in the formula seen as a tree.  Hence, binders in
     lambda and free symbs in args are different

     The binder_rename invariant is not satisfied:
     (lambda x. f(x, x)) T,
     where T contains binders, introduces two binders of the same name
     in the tree

     After the call, the binder_rename invariant is naturally satisfied
  */
  src = beta_reduce_subst(DAG_argn(lambda));
  dest = binder_rename(src);
  DAG_free(src);
  for (i = 0; i < DAG_arity(lambda) - 1u; i++)
    {
      DAG_free(PDAG[i]);
      DAG_symb_DAG[DAG_symb(DAG_arg(lambda, i))] = DAG_NULL;
    }
  free(PDAG);
  DAG_free(lambda);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief applies beta-reduction wherever it can be
   \param src the term (or formula) to rewrite
   \return the beta-reduced term
   \remarks Non destructive
   \remarks tree-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks ite-, quantifier-, lambda-, apply-tolerant
*/
static TDAG
beta_reduce_aux2 (TDAG src)
{
  unsigned i;
  TDAG *PDAG, dest;
  if (DAG_symb(src) == APPLY_LAMBDA)
    {
      dest = beta_reduce_apply(src);
      src = dest;
      dest = beta_reduce_aux2(src);
      DAG_free(src);
      return dest;
    }
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof (TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = beta_reduce_aux2(DAG_arg(src, i));
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  for (i = 0; i < DAG_arity(dest); i++)
    DAG_free(DAG_arg(dest, i));
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief applies beta-reduction wherever it can be
   \param src the term (or formula) to rewrite
   \return the beta-reduced term
   \remarks Non destructive
   \remarks DAG-linear with respect to the lambda-free part, tree-linear
   within scope of lambda
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks sets intermediate results in Pflag field (to be eliminated)
   \remarks ite-, quantifier-, lambda-, apply-tolerant
*/
static TDAG
beta_reduce_aux(TDAG src)
{
  unsigned i;
  TDAG *PDAG, tmp;
  if (DAG_Pflag(src))
    return DAG_of_ptr(DAG_Pflag(src));
  if (DAG_symb(src) == APPLY_LAMBDA)
    {
      TDAG tmp = beta_reduce_aux2(src);
      DAG_Pflag_set(src, DAG_ptr_of(tmp));
      return tmp;
    }
  /* (f t1 ... tn) */
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = beta_reduce_aux(DAG_arg(src, i));
  tmp = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  DAG_Pflag_set(src, DAG_ptr_of(tmp));
  return tmp;
}

/*--------------------------------------------------------------*/

TDAG
beta_reduce(TDAG src)
{
  TDAG dest;
  dest = DAG_dup(beta_reduce_aux(src));
  DAG_free_Pflag(src);
  return dest;
}

/*--------------------------------------------------------------*/

void
beta_reduce_array(unsigned n, TDAG * Psrc)
{
  unsigned i;
  TDAG * PDAG;
  MY_MALLOC(PDAG, n * sizeof(TDAG));
  for (i = 0; i < n; i++)
    PDAG[i] = DAG_dup(beta_reduce_aux(Psrc[i]));
  for (i = 0; i < n; i++)
    {
      DAG_free_Pflag(Psrc[i]);
      DAG_free(Psrc[i]);
      Psrc[i] = PDAG[i];
    }
  free(PDAG);
}

/*
  -------------------------------------------------------------
  Macro expansion
  -------------------------------------------------------------
*/

/**
  Implementation of macro expansion.
 Recursively processes the DAGs, expanding the macro symbols.
 The body (definition) of each macro is also processed (once).
 
 Rationale for the implementation.
 
 The goal is to avoid applying macro-expansion more than once
 to the same DAG (and this includes macro bodies).
 
 Solution 1. Once the body of a macro has been expanded, substitute
 the bound DAG of the macro symbol with the expanded body. This 
 solution is destructive and would prevent us from recovering the
 original definition of the macro if required. It also requires
 a mechanism to recall which macro symbols have been expanded 
 (Tsymb flag, or global Thash, or global Tset). This mechanism
 require to change existing data structures.
 
 Solution 2. Adapt the generic recursive processing to macro
 expansion so that it also applies to macro bodies. Thus the
 expanded bodies will remain stored in the Pflag attribute of
 the DAG of the original macro body. This solution requires
 a specific implementation of recursive processing and avoids
 changing existing data structure. Macro body expansions are
 deleted before macro_substitute returns its value, which is
 a potential source of inefficiency if macro_substitute is
 called often. 
 */

/*--------------------------------------------------------------*/
static TDAG macro_substitute_rec(TDAG src, Tlist * Plist);
static void macro_free_Pflag(TDAG src);

static TDAG
macro_substitute_dag_one(TDAG src, Tlist * Plist)
{
  unsigned i;
  TDAG *PDAG;
  TDAG result;
  TDAG body;
  TDAG lambda;

  if (DAG_symb_type(DAG_symb(src)) != SYMB_MACRO)
    return DAG_dup(src);

  body = DAG_symb_DAG[DAG_symb(src)];
  body = binder_rename(body);
  result = DAG_dup(macro_substitute_rec(body, Plist));
  macro_free_Pflag(body);
  DAG_free(body);
  if (!DAG_arity(src))
    return result;

  lambda = result;
  /* compute the mgu of lambda formal parameters and Pargs */
  for (i = 0; i < DAG_arity(src); ++i)
    DAG_sort_unif_constrain(Plist, 
			    DAG_sort_sub(DAG_sort(lambda))[i], 
			    DAG_sort(DAG_arg(src, i)));

  MY_MALLOC(PDAG, (DAG_arity(src) + 1u) * sizeof(TDAG));
  PDAG[0] = lambda;
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i + 1u] = DAG_arg(src, i);

  result = DAG_dup(DAG_new(APPLY_LAMBDA, DAG_arity(src) + 1u, PDAG));
  DAG_free(lambda);
  return result;
}

/* -------------------------------------------------------------- */

/**
   \brief Structural recursion - generic processing adapted for macro 
   expansion.
  */
static void
macro_substitute_dag_rec(TDAG src, Tlist * Plist)
{
  unsigned i;
  TDAG *PDAG, dest, tmp;
  assert (!(DAG_symb_type(DAG_symb(src)) == SYMB_MACRO && 
	    DAG_sort_polymorphic(DAG_sort(src))));
  if (DAG_Pflag(src))
    return;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = macro_substitute_rec(DAG_arg(src, i), Plist);
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  for (i = 0; i < DAG_arity(src); i++)
    DAG_free(DAG_arg(dest, i));
  tmp = macro_substitute_dag_one(dest, Plist);
  DAG_Pflag_set(src, DAG_ptr_of(tmp));
  DAG_free(dest);

  dest = DAG_of_ptr(DAG_Pflag(src));
  if (DAG_arity(dest) > 0)
    {
      if (DAG_symb(dest) == PREDICATE_EQ)
	DAG_sort_unif_constrain(Plist, DAG_sort(DAG_arg0(dest)), 
				DAG_sort(DAG_arg1(dest)));
      else if (!DAG_symb_predefined(DAG_symb(dest)))
	{
	  Tsort sort = DAG_sort_intern(DAG_symb_sort(DAG_symb(src)));
	  unsigned i;
	  assert(DAG_sort_arity(sort) != DAG_SORT_NARY);
	  for (i = 0; i < DAG_sort_arity(sort) - 1u; ++i)
	    DAG_sort_unif_constrain(Plist,
				    DAG_sort_sub(sort)[i], 
				    DAG_sort(DAG_arg(dest, i)));
	  DAG_sort_unif_constrain(Plist, 
				  DAG_sort_sub(sort)[DAG_sort_arity(sort)-1], 
				  DAG_sort(dest));
	}
    }
}

/*--------------------------------------------------------------*/

#ifdef DEBUG_HOL_MACRO
static void
macro_debug_rec(TDAG src)
{
  int i;
  if (DAG_flag(src)) return;
  DAG_flag_set(src, 1);
  my_DAG_message("macro-expansion\narg: %D\n===>%D\n",
		 src, (TDAG) DAG_Pflag(src));
  for (i = 0; i < DAG_arity(src);++i)
    macro_debug_rec(DAG_arg(src, i));
  if (DAG_symb(src)->type == SYMB_MACRO)
    my_DAG_message("macro-expansion\narg: %D\n===>%D\n",
		   DAG_symb(src)->DAG, (TDAG) DAG_Pflag(DAG_symb(src)->DAG));
}

static void
macro_debug(TDAG src)
{
  macro_debug_rec (src);
  DAG_reset_flag (src);
}
#endif

static TDAG macro_substitute_tree_rec(TDAG src, Tlist * Plist);

static TDAG
macro_substitute_tree_one(TDAG src, Tlist * Plist)
{
  TDAG *PDAG, body, tmp;
  unsigned i;

  if (DAG_symb_type(DAG_symb(src)) != SYMB_MACRO)
    return src;

  body = DAG_symb_DAG[DAG_symb(src)];
  tmp = binder_rename(body);
  body = macro_substitute_tree_rec(tmp, Plist);
  DAG_free(tmp);
  if (!DAG_arity(src))
    {
      DAG_free(src);
      return body;
    }

  /* compute the mgu of body formal parameters and Pargs */
  for (i = 0; i < DAG_arity(src); ++i)
    DAG_sort_unif_constrain(Plist, 
			    DAG_sort_sub(DAG_sort(body))[i], 
			    DAG_sort(DAG_arg(src, i)));

  MY_MALLOC(PDAG, (DAG_arity(src) + 1u) * sizeof(TDAG));
  PDAG[0] = body;
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i + 1u] = DAG_arg(src, i);

  tmp = DAG_dup(DAG_new(APPLY_LAMBDA, DAG_arity(src) + 1u, PDAG));
  DAG_free(body);
  DAG_free(src);
  return tmp;
}

/* -------------------------------------------------------------- */

/**
   \brief Structural recursion - generic processing adapted for macro 
   expansion.
  */
static TDAG
macro_substitute_tree_rec(TDAG src, Tlist * Plist)
{
  unsigned i;
  TDAG *PDAG, dest;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = macro_substitute_tree_rec(DAG_arg(src, i), Plist);
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  for (i = 0; i < DAG_arity(src); i++)
    DAG_free(DAG_arg(dest, i));
  dest = macro_substitute_tree_one(dest, Plist);

  if (DAG_arity(dest) > 0)
    {
      if (DAG_symb(dest) == PREDICATE_EQ)
	DAG_sort_unif_constrain(Plist, DAG_sort(DAG_arg0(dest)), 
				DAG_sort(DAG_arg1(dest)));
      else if (!DAG_symb_predefined(DAG_symb(dest)))
	{
	  Tsort sort = DAG_sort_intern(DAG_symb_sort(DAG_symb(src)));
	  unsigned i;
	  assert(DAG_sort_arity(sort) != DAG_SORT_NARY);
	  for (i = 0; i < DAG_sort_arity(sort) - 1u; ++i)
	    DAG_sort_unif_constrain(Plist, 
				    DAG_sort_sub(sort)[i], 
				    DAG_sort(DAG_arg(dest, i)));
	  DAG_sort_unif_constrain(Plist, 
				  DAG_sort_sub(sort)[DAG_sort_arity(sort) - 1u], 
				  DAG_sort(dest));
	}
    }
  return dest;
}

/* -------------------------------------------------------------- */

/**
   \brief 
   Structural recursion - 
   generic processing adapted for macro expansion.
   
  */
static TDAG
macro_substitute_rec(TDAG src, Tlist * Plist)
{
  if (DAG_symb_type(DAG_symb(src)) == SYMB_MACRO && DAG_sort_polymorphic(DAG_sort(src)))
    return macro_substitute_tree_rec(src, Plist);
  else
    {
      macro_substitute_dag_rec(src, Plist);
      return DAG_of_ptr(DAG_Pflag(src));
    }
}

/*--------------------------------------------------------------*/

/**
 Post-processing after macro expansion: cleans up the Pflag 
 attribute recursively, including into macro bodies.
 */

static void
macro_free_Pflag(TDAG src)
{
  unsigned i;
  if (!DAG_Pflag(src))
    return;
  for (i = 0; i < DAG_arity(src); i++)
    macro_free_Pflag(DAG_arg(src, i));
  DAG_free(DAG_of_ptr(DAG_Pflag(src)));
  DAG_Pflag_set(src, NULL);
}

/*--------------------------------------------------------------*/
/**
 
 \brief macro expansion
 
 \seealso macro_substitute_rec
 \seealso macro_substitute_one
 \seealso macro_free_Pflag
 */
TDAG
macro_substitute(TDAG src)
{
  TDAG dest;
  Tlist unif;
  unif = NULL;
  /* macro_substitute_rec(src, &unif);
  dest = DAG_dup(DAG_Pflag(src)); */
  dest = macro_substitute_tree_rec(src, &unif);
  if (unif)   /* sort unification required */
    {
      TDAG tmp;
      DAG_sort_unif_solve(&unif);
      tmp = DAG_sort_subst_DAG(unif, dest);
      DAG_free(dest);
      dest = tmp;
      DAG_sort_unif_delete(&unif);
    }
#ifdef DEBUG_HOL_MACRO
  macro_debug(src);
#endif
  macro_free_Pflag(src);
  return dest;
}

/*--------------------------------------------------------------*/
/**
 
 \brief macro expansion
 
 \seealso macro_substitute_rec
 \seealso macro_substitute_one
 \seealso macro_free_Pflag
 */
void
macro_substitute_array(unsigned n, TDAG * Psrc)
{
  unsigned i;
  for (i = 0; i < n; i++)
    {
      TDAG dest = macro_substitute(Psrc[i]);
      DAG_free(Psrc[i]);
      Psrc[i] = dest;
    }
}

/*
  --------------------------------------------------------------
  Equality lowering
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   applies equality lowering to top most symbol if it can be.
   Rewrites equalities T1 = T2 where T1 and T2 have function
   (or predicate) sort into
   forall x_1 ... x_n . T1(x_1, ... , x_n) = T2(x_1, ... , x_n)
   New quantified variables symbols are of the form ?veriT__<n>, so
   such symbols should not be used elsewhere
   \param src the term (or formula) to rewrite
   \return the beta-reduced term
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers), if the binders are not used elsewhere.
   \remark ite-, quantifier-, lambda-, apply-tolerant
*/
static TDAG
equality_lower_one(TDAG src)
/* Safe for structural recursion if restriction on bound vars applies. */
{
  unsigned i;
  unsigned nb_bound;
  Tsymb *symb;
  TDAG DAG0u, DAG1u;
  TDAG *PDAG, PDAG1, PDAG2;
  Tlist unif = NULL;

  if (DAG_symb(src) != PREDICATE_EQ ||
      DAG_sort_arity(DAG_sort(DAG_arg0(src))) == 0 ||
      DAG_sort_instance(DAG_sort(DAG_arg0(src))))
    return src;

  DAG_sort_unif_constrain(&unif, DAG_sort(DAG_arg0(src)), DAG_sort(DAG_arg1(src)));
  if (unif)
    {
      DAG_sort_unif_solve(&unif);
      assert(unif);
      DAG0u = DAG_sort_subst_DAG(unif, DAG_arg0(src));
      DAG1u = DAG_sort_subst_DAG(unif, DAG_arg1(src));
      list_apply(unif, free);
      list_free(&unif);
    }
  else
    {
      DAG0u = DAG_arg0(src);
      DAG1u = DAG_arg1(src);
    }
  assert(DAG_sort(DAG0u) == DAG_sort(DAG1u));
  if (DAG_sort_parametric(DAG_sort(DAG0u)))
    my_DAG_error("parametric sorts in equality (%D)\n", src);
  assert(DAG_sort_arity(DAG_sort(DAG0u)) != DAG_SORT_NARY);
  assert(DAG_sort_arity(DAG_sort(DAG0u)) > 0);

  nb_bound = DAG_sort_arity(DAG_sort(DAG0u)) - 1;
  MY_MALLOC(symb, nb_bound * sizeof(Tsymb));
  for (i = 0; i < nb_bound; i++)
    {
      if (DAG_sort(DAG0u) == SORT_BOOLEAN)
	my_DAG_error("equality lowering introduces quantifiers on Booleans (%D)\n",
		     src);
      symb[i] = DAG_symb_variable(DAG_sort_sub(DAG_sort(DAG0u))[i]);
    }
  MY_MALLOC(PDAG, (nb_bound + 1) * sizeof(TDAG));
  PDAG[0] = DAG0u;
  for (i = 0; i < nb_bound; i++)
    PDAG[i + 1] = DAG_new(symb[i], 0, NULL);
  PDAG1 = DAG_new(APPLY_LAMBDA, nb_bound + 1, PDAG);
  MY_MALLOC(PDAG, (nb_bound + 1) * sizeof(TDAG));
  PDAG[0] = DAG1u;
  for (i = 0; i < nb_bound; i++)
    PDAG[i + 1] = DAG_new(symb[i], 0, NULL);
  PDAG2 = DAG_new(APPLY_LAMBDA, nb_bound + 1, PDAG);
  MY_MALLOC(PDAG, 2 * sizeof(TDAG));
  PDAG[0] = PDAG1;
  PDAG[1] = PDAG2;
  if (DAG_sort(PDAG1) == SORT_BOOLEAN)
    PDAG1 = DAG_new(CONNECTOR_EQUIV, 2, PDAG);
  else
    PDAG1 = DAG_new(PREDICATE_EQ, 2, PDAG);
  MY_MALLOC(PDAG, (nb_bound + 1) * sizeof(TDAG));
  for (i = 0; i < nb_bound; i++)
    PDAG[i] = DAG_new(symb[i], 0, NULL);
  PDAG[i] = PDAG1;
  PDAG1 = DAG_new(QUANTIFIER_FORALL, nb_bound + 1, PDAG);
  free(symb);
  return PDAG1;
}

/*--------------------------------------------------------------*/

TDAG
equality_lower(TDAG src)
{
  return structural_recursion(src, equality_lower_one);
}

/*--------------------------------------------------------------*/

void
equality_lower_array(unsigned n, TDAG * Psrc)
{
  structural_recursion_array(n, Psrc, equality_lower_one);
}
