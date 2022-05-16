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
  arithmetic rewriting
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>

#include "config.h"

#include "general.h"
#include "list.h"

#include "DAG.h"
#include "distinct-elim.h"
#include "recursion.h"
#include "number.h"
#include "simp-arith.h"

#include "DAG-print.h"

/*
  --------------------------------------------------------------
  Module for preprocessing formulas aiming at Difference Logic
  --------------------------------------------------------------
*/

/**
   \brief checks DAG matches (X + ... + X) - (Y + ... + Y) - X, Y: wildcards
*/
static int
DAG_match_diff_n_repeat(TDAG DAG)
{
  unsigned i;
  if (DAG_symb(DAG) != FUNCTION_MINUS)
    return 0;
  if (DAG_arity(DAG) != 2)
    return 0;
  if (DAG_symb(DAG_arg0(DAG)) != FUNCTION_SUM && DAG_symb(DAG_arg1(DAG)) != FUNCTION_SUM)
    return 0;
  if (DAG_arity(DAG_arg0(DAG)) != DAG_arity(DAG_arg1(DAG)))
    return 0;
  for (i = 1; i < DAG_arity(DAG_arg0(DAG_arg1(DAG))); i++)
    if (DAG_arg(DAG_arg0(DAG), i) != DAG_arg0(DAG_arg0(DAG)))
      return 0;
  for (i = 1; i < DAG_arity(DAG_arg1(DAG_arg1(DAG))); i++)
    if (DAG_arg(DAG_arg1(DAG), i) != DAG_arg0(DAG_arg1(DAG)))
      return 0;
  return 1;
}

/* PF+DD
   Takes a formula with difference logic constraints
   Transforms all constraints of the form
   x - y OP z, where OP in {=, <=, <}
   to x OP y + z
   this preprocessing step is necessary for DL Module
   to be able to recognize DL even with the flattening induced by NO
   Destructive for DAG */

static TDAG zero_variable = DAG_NULL;

/**
   \author Pascal Fontaine
   introduces a "zero variable" for X = n, X <= n, ... where X is a term
   and n a number, so that the resulting DAG explicitely belongs to DL
   This preprocessing comes last: all zero variables introduced are really necessary.
*/
static TDAG
dl_tidy_node_zero(TDAG DAG)
{
  unsigned i;

  if (!zero_variable)
    zero_variable = DAG_dup(DAG_new_args(FUNCTION_ZERO_VARIABLE, DAG_NULL));

  if (DAG_symb(DAG) == PREDICATE_EQ || DAG_symb(DAG) == PREDICATE_LESS ||
      DAG_symb(DAG) == PREDICATE_LEQ)
    {
      if (DAG_is_number(DAG_arg0(DAG)) && DAG_is_number(DAG_arg1(DAG)))
	{
	  Tnumber number0 = number_new();
	  Tnumber number1 = number_new();
	  int res;
	  number_from_DAG(number0, DAG_arg0(DAG));
	  number_from_DAG(number1, DAG_arg1(DAG));
	  if (DAG_symb(DAG) == PREDICATE_EQ)
	    res = number_equal(number0, number1);
	  else if (DAG_symb(DAG) == PREDICATE_LESS)
	    res = number_less(number0, number1);
	  else /* DAG_symb(DAG) == PREDICATE_LEQ */
	    res = !number_greater(number0, number1);
	  number_free(number0);
	  number_free(number1);
	  return res?DAG_TRUE:DAG_FALSE;
	}
      if (DAG_is_number(DAG_arg0(DAG)))
	return DAG_new_args(DAG_symb(DAG), DAG_plus(zero_variable, DAG_arg0(DAG)), 
			    DAG_arg1(DAG), DAG_NULL);
      if (DAG_is_number(DAG_arg1(DAG)))
	return DAG_new_args(DAG_symb(DAG), DAG_arg0(DAG), 
			    DAG_plus(zero_variable, DAG_arg1(DAG)), DAG_NULL);
      return DAG;
    }
  /*  return DAG; */
  if (arith_function(DAG_symb(DAG)) || !DAG_arity(DAG) || binder(DAG_symb(DAG)))
    return DAG;
  /* PF Non arithmetic symbol: check if a number as argument */
  for (i = 0; i < DAG_arity(DAG); i++)
    if (DAG_is_number(DAG_arg(DAG, i)))
      break;
  if (i < DAG_arity(DAG))
    {
      TDAG * PDAG;
      MY_MALLOC(PDAG, DAG_arity(DAG) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(DAG); i++)
	if (DAG_is_number(DAG_arg(DAG, i)))
	  {
	    PDAG[i] = DAG_plus(zero_variable, DAG_arg(DAG, i));
	  }
	else
	  PDAG[i] = DAG_arg(DAG, i);
      return DAG_new(DAG_symb(DAG), DAG_arity(DAG), PDAG);
    }
  return DAG;
}

/*--------------------------------------------------------------*/

static TDAG
dl_tidy_node(TDAG DAG)
{
  /* X - n ==> X + (-n) */
  if (DAG_symb(DAG) != PREDICATE_EQ &&
      DAG_symb(DAG) != PREDICATE_LESS &&
      DAG_symb(DAG) != PREDICATE_LEQ)
    return DAG;
  /* (X + ... + X) - (Y + ... + Y) OP c ==> X OP Y + c/n, where OP : {<=, <, =} */  
  if (DAG_match_diff_n_repeat(DAG_arg0(DAG)) && DAG_is_number(DAG_arg1(DAG)))
    {
      Tnumber number = number_new();
      Tnumber div = number_new();
      Tnumber res = number_new();
      TDAG DAG_number;
      number_from_DAG(number, DAG_arg1(DAG));
      number_set(div, (int) DAG_arity(DAG_arg0(DAG_arg0(DAG))));
      number_div(res, number, div);
      DAG_number = number_to_DAG(res);
      number_free(number);
      number_free(div);
      number_free(res);
      return DAG_new_args(DAG_symb(DAG), DAG_arg0(DAG_arg0(DAG_arg0(DAG))),
			  DAG_plus(DAG_arg0(DAG_arg1(DAG_arg0(DAG))), DAG_number), DAG_NULL);
    }
  /* c OP (X + ... + X) - (Y + ... + Y) ==> Y + c/n OP X, where OP : {<=, <, =} */  
  if (DAG_match_diff_n_repeat(DAG_arg1(DAG)) && DAG_is_number(DAG_arg0(DAG)))
    {
      Tnumber number = number_new();
      Tnumber div = number_new();
      Tnumber res = number_new();
      TDAG DAG_number;
      number_from_DAG(number, DAG_arg0(DAG));
      number_set(div, (int) DAG_arity(DAG_arg0(DAG_arg1(DAG))));
      number_div(res, number, div);
      DAG_number = number_to_DAG(res);
      number_free(number);
      number_free(div);
      number_free(res);
      /* ==> Y - X OP -c/n */
      return DAG_new_args(DAG_symb(DAG),
			  DAG_plus(DAG_arg0(DAG_arg1(DAG_arg1(DAG))), DAG_number),
			  DAG_arg0(DAG_arg0(DAG_arg1(DAG))), DAG_NULL);
    }
  /* X - Y OP c where OP : {<=, <, =} */
  if (DAG_symb(DAG_arg0(DAG)) == FUNCTION_MINUS &&
      DAG_arity(DAG_arg0(DAG)) == 2 &&
      DAG_is_number(DAG_arg1(DAG)))
    {
      TDAG X = DAG_arg0(DAG_arg0(DAG));
      TDAG Y = DAG_arg1(DAG_arg0(DAG));
      TDAG c = DAG_arg1(DAG);
      /* X - Y OP c ==> X OP Y + c, where OP: {<=, <, =} */
      return DAG_new_args(DAG_symb(DAG), X, DAG_plus(Y, c), DAG_NULL);
    }
  /* c OP X - Y where OP : {<=, <, =} */
  if (DAG_symb(DAG_arg1(DAG)) == FUNCTION_MINUS &&
      DAG_arity(DAG_arg1(DAG)) == 2 &&
      DAG_is_number(DAG_arg0(DAG)))
    {
      TDAG X = DAG_arg0(DAG_arg1(DAG));
      TDAG Y = DAG_arg1(DAG_arg1(DAG));
      TDAG c = DAG_arg0(DAG);
      /* c OP X - Y ==> Y + c OP X, where OP: {<=, <, =} */
      return DAG_new_args(DAG_symb(DAG), DAG_plus(Y, c), X, DAG_NULL);
    }
  return DAG;
}

/*
  --------------------------------------------------------------
  Rewrite t >= t' and t > t' to t' <= t and t' < t
  --------------------------------------------------------------
*/

static TDAG
greater_elim(TDAG src)
{
  if (DAG_symb(src) == PREDICATE_GREATER)
    return DAG_new_args(PREDICATE_LESS, DAG_arg1(src), DAG_arg(src, 0), DAG_NULL);
  else if (DAG_symb(src) == PREDICATE_GREATEREQ)
    return DAG_new_args(PREDICATE_LEQ, DAG_arg1(src), DAG_arg(src, 0), DAG_NULL);     
  else
    return src;
}

/*
  --------------------------------------------------------------
  Rewrite (- c) and (/ c d) where c and d are numbers
  --------------------------------------------------------------
*/

static TDAG
rewrite_div(TDAG src)
{
  if (DAG_arity(src) != 2)
    my_error("rewrite_div: strange arity for src\n");
  if (DAG_is_number(DAG_arg(src, 0)) && DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand1 = number_new();
      Tnumber operand2 = number_new();
      Tnumber div = number_new();
      TDAG dest = DAG_NULL;
      number_from_DAG(operand1, DAG_arg(src, 0));
      number_from_DAG(operand2, DAG_arg1(src));
      number_div(div, operand1, operand2);
      dest = number_to_DAG(div);
      number_free(div);
      number_free(operand1);
      number_free(operand2);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
rewrite_unary_minus(TDAG src)
{
  if (DAG_arity(src) != 1)
    my_error("rewrite_unary_minus: strange arity for src\n");
  if (DAG_is_number(DAG_arg(src, 0)))
    {
      Tnumber number = number_new();
      TDAG dest = DAG_NULL;
      number_from_DAG(number, DAG_arg(src, 0));
      number_neg(number);
      dest = number_to_DAG(number);
      number_free(number);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
rewrite_sum(TDAG src)
{
  unsigned i, count = 0;
  if (DAG_arity(src) <= 1)
    my_error("rewrite_sum: strange arity for src\n");
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_is_number(DAG_arg(src, i)))
      count++;
  if (count >= 2)
    {
      unsigned j;
      TDAG * PDAG;
      Tnumber n = number_new();
      TDAG dest;
      number_set(n, 0);
      MY_MALLOC(PDAG, (DAG_arity(src) + 1u - count) * sizeof(TDAG));
      for (i = 0, j = 0; i < DAG_arity(src); i++)
	if (!DAG_is_number(DAG_arg(src, i)))
	  PDAG[j++] = DAG_arg(src, i);
	else
	  {
	    Tnumber m = number_new();
	    number_from_DAG(m, DAG_arg(src, i));
	    number_add(n, m, n);
	    number_free(m);
	  }
      PDAG[j++] = number_to_DAG(n);
      number_free(n);
      assert(j == DAG_arity(src) + 1u - count);
      if (j >= 2)
	return DAG_new(DAG_symb(src), j, PDAG);
      dest = PDAG[0];
      free(PDAG);
      return dest;
    }
  if (count == 1 && !DAG_is_number(DAG_argn(src)))
    {
      unsigned j;
      TDAG * PDAG;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0, j = 0; i < DAG_arity(src); i++)
	if (!DAG_is_number(DAG_arg(src, i)))
	  PDAG[j++] = DAG_arg(src, i);
	else
	  PDAG[DAG_arity(src) - 1] = DAG_arg(src, i);
      return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
rewrite_minus(TDAG src)
{
  if (DAG_arity(src) != 2)
    my_error("rewrite_minus: strange arity for src\n");
  if (DAG_is_number(DAG_arg(src, 0)) && DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand1 = number_new();
      Tnumber operand2 = number_new();
      Tnumber minus = number_new();
      TDAG dest = DAG_NULL;
      number_from_DAG(operand1, DAG_arg(src, 0));
      number_from_DAG(operand2, DAG_arg1(src));
      number_sub(minus, operand1, operand2);
      dest = number_to_DAG(minus);
      number_free(minus);
      number_free(operand1);
      number_free(operand2);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief rewrite arithmetic terms:
   unary minus applied to number is rewritten as number
   divisions of numbers are rewritten to the quotient
   sum including several numbers are rewritten to a sum with one number only
   number should be at the end
   number - number is rewritten to number
   \param src term (or formula)
   \return The rewritten term
   \remarks should be used inside structural recursion
*/
static TDAG
rewrite_node(TDAG src)
{
  if (unary_minus(DAG_symb(src)))
    return rewrite_unary_minus(src);
  if (DAG_symb(src) == FUNCTION_DIV)
    return rewrite_div(src);
  if (DAG_symb(src) == FUNCTION_SUM)
    return rewrite_sum(src);
  if (DAG_symb(src) == FUNCTION_MINUS)
    return rewrite_minus(src);
  return src;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

static int simp_arith_active = -1;
static int pre_dl = 1;

/*--------------------------------------------------------------*/

void
simp_arith_logic(char * logic)
{
  if (strcmp(logic, "QF_UF") == 0)
    simp_arith_active = 0;
  else
    simp_arith_active = 1;
  if (strcmp(logic, "QF_UFIDL") == 0 ||
      strcmp(logic, "QF_RDL") == 0 ||
      strcmp(logic, "QF_IDL") == 0)
    pre_dl = 1;
  else
    pre_dl = 0;
}

/*--------------------------------------------------------------*/

TDAG
simp_arith(TDAG src)
{
  TDAG dest;
  if (simp_arith_active == -1)
    my_error("simp_arith: logic uninitialized\n");
  if (!simp_arith_active)
    return DAG_dup(src);
  dest = structural_recursion(src, greater_elim);
  /* DAG_free(src); commented out so that it remains non-destructive */
  src = dest;
  dest = structural_recursion(src, rewrite_node);
  DAG_free(src);
  src = dest;
  if (pre_dl)
    {
      dest = structural_recursion(src, dl_tidy_node);
      DAG_free(src);
      src = dest;
      dest = structural_recursion(src, dl_tidy_node_zero);
      DAG_free(src);
      src = dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

void
simp_arith_init(void)
{
}

/*--------------------------------------------------------------*/

void
simp_arith_done(void)
{
  if (zero_variable)
    DAG_free(zero_variable);
}
