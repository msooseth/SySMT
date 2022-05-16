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

#include <string.h>

#include "general.h"

#include "complete.h"
#include "recursion.h"
#include "config.h"

#define xor !=
/*--------------------------------------------------------------*/

/* DD a predefined SMT logic has been set */
static int predefined_logic_set = 0;
/* DD a predefined SMT logic has been set and we are complete */
static int predefined_logic_complete = 0;
 
/* PF interpreted symbol in input ? */ 
static int interpreted_symbols = 0;
/* PF interpreted (non arithmetic) symbol in input ? */ 
static int interpreted_non_arith_symbols = 0;
/* PF quantifier in input ? */
static int quantified_formulas = 0;
/* PF quantified variables are used in functions ? */
/* static int quantified_variables_in_functions = 0; */
/* PF Difference Logic ? */
static int DL = 0;
/* PF Linear Arithmetic ? */
static int LA = 0;
/* PF Non Linear Arithmetic ? */
static int NLA = 0;
/* PF Mix Integer and reals */
static int integer_terms = 0, real_terms = 0;


/*--------------------------------------------------------------*/

static int
numeric_literal(TDAG DAG)
{
  return DAG_is_number(DAG) ||
    (unary_minus(DAG_symb(DAG)) && DAG_is_number(DAG_arg0(DAG)));
}

static int
integer_literal(TDAG DAG)
{
  return numeric_literal(DAG) && DAG_sort(DAG) == SORT_INTEGER;
}
/*--------------------------------------------------------------*/

static int
inspect_formula (TDAG DAG)
{
  Tsymb symb = DAG_symb(DAG);
  if (quantifier(symb))
    quantified_formulas = 1;
  else if (DAG_symb_interpreted (symb))
    {
      if (boolean_connector(symb) ||
	  boolean_constant(symb))
	return 1;
      if (symb != PREDICATE_EQ)
	interpreted_symbols = 1;
      if (symb == FUNCTION_ZERO_VARIABLE ||DAG_is_number(DAG))
	{
	  DL = 1;
	  return 1;
	}
      if (symb != PREDICATE_LESS &&
	  symb != PREDICATE_LEQ &&
	  symb != PREDICATE_EQ &&
	  !arith_function(symb))
	interpreted_non_arith_symbols = 1;
      else if (symb == FUNCTION_PROD ||
	       symb == FUNCTION_DIV)
	{
	  unsigned i, c;
	  for (i = 0, c = 0; i < DAG_arity(DAG); i++)
	    if (!numeric_literal(DAG_arg(DAG, i)))
	      c++;
	  if (c > 1)
	    NLA = 1;
	  else
	    LA = 1;
	}
      else if (symb == PREDICATE_LESS ||
	       symb == PREDICATE_LEQ ||
	       symb == PREDICATE_EQ)
	{
	  if (!numeric_literal(DAG_arg0(DAG)) &&
	      !numeric_literal(DAG_arg1(DAG)))
	    DL = 1;
	  else
	    LA = 1; /* DD This check is not correct? - QF_UFIDL/mathsat/Euf.../vhard/vhard5.smt */
	}
      else if (symb == FUNCTION_SUM)
	{
	  if (DAG_arity(DAG) == 1)
	    my_error ("sum with one argument\n");
	  if (DAG_arity(DAG) != 2)
	    LA = 1;
	  if (numeric_literal(DAG_arg0(DAG)) xor
	      numeric_literal(DAG_arg1(DAG)) )
	    DL = 1;
	  else
	    LA = 1;
	}
      else
	LA = 1;
    }
  else
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	if (numeric_literal(DAG_arg(DAG, i)))
	  LA = 1;
    }
  if (DAG_sort(DAG) == SORT_INTEGER && !integer_literal(DAG))
    integer_terms = 1;
  if (DAG_sort(DAG) == SORT_REAL && !numeric_literal (DAG))
    real_terms = 1;
  return 1;
}

/*--------------------------------------------------------------*/

void
complete_init (void)
{
  predefined_logic_set = 0;
  predefined_logic_complete = 0;
  interpreted_symbols = 0;
  interpreted_non_arith_symbols = 0;
  quantified_formulas = 0;
  DL = 0;
  integer_terms = 1;
  real_terms = 1;
  LA = 0;
  NLA = 0;
}

/*--------------------------------------------------------------*/

void
complete_logic (char * logic)
{
  if (logic != NULL && strcmp (logic, "UNKNOWN") != 0)
    {
      predefined_logic_set = 1;
      predefined_logic_complete = 
	(strcmp (logic, "QF_UF") == 0 ||
	 strcmp (logic, "QF_IDL") == 0 ||
	 strcmp (logic, "QF_RDL") == 0 ||
	 strcmp (logic, "QF_UFIDL") == 0 ||
	 strcmp (logic, "QF_UFLIA") == 0 ||
	 strcmp (logic, "QF_LIA") == 0 ||
	 strcmp (logic, "QF_LRA") == 0);
    }
}

/*--------------------------------------------------------------*/

void
complete_done (void)
{
}

/*--------------------------------------------------------------*/

void
complete_add (TDAG DAG)
{
  if (!predefined_logic_set)
    structural_recursion_pred (DAG, inspect_formula);
}

/*--------------------------------------------------------------*/

int
complete_check (void)
{
  if (predefined_logic_set)
    return predefined_logic_complete;
  if (quantified_formulas)
    return 0;
  if (!interpreted_symbols)
    return 1;
  if (interpreted_non_arith_symbols)
    return 0;
  if (NLA)
    return 0;
  if (LA && real_terms)
    return 1;
  if (LA && integer_terms)
    return 1;
  if (DL && real_terms)
    return 1;
  if (DL && integer_terms)
    return 1;

  return 0;
}
