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

/* -------------------------------------------------------------- */

/**
 \brief Module for configuring the library to handle SMT-LIB logics.
 
 Internal functions create signatures for the following SMT-LIB
 theories: Core, Ints, Reals, ArraysEx, Reals_Ints.
 
 There is no support to create signatures for the following
 theories: Fixed_Size_BitVectors.
 
 The module provides the possibility to set up the DAG module with
 sorts and symbols corresponding to the following logics : AUFLIA,
 AUFLIRA, AUFNIRA, QF_A, QF_AUFLIA, QF_AX, QF_IDL, QF_LIA, QF_LRA,
 QF_NIA, QF_RDL, QF_UF, QF_UFIDL, QF_UFLIA, QF_UFLRA.
 
 There is currently no support for the following logics: AUFLIRA,
 AUFNIRA, QF_AUFBV, QF_BV, QF_UFBV, QF_UFBV[32], QF_UFLIA, QF_UFLRA.
 
 \todo check if zero variable is always necessary or only for difference
 logic theories.
 \todo logic Reals_Ints
 */

/* -------------------------------------------------------------- */

#include "config.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "options.h"

#include "general.h"

#include "veriT-DAG.h"
#include "DAG.h"
#include "DAG-print.h"
#include "response.h"

#define SYMB_NULL DAG_SYMB_NULL
#define SYMB_DP_MASK(s) DAG_symb_dp_mask(s)

Tsort     SORT_INTEGER = DAG_SORT_NULL;
Tsort     SORT_REAL = DAG_SORT_NULL;
Tsort     SORT_ARRAY = DAG_SORT_NULL;

char * SORT_INTEGER_STR = "Int";
char * SORT_REAL_STR = "Real";
char * SORT_ARRAY_STR = "Array";

Tsort     SORT_NUMERAL = DAG_SORT_NULL; /**< sort for numeral constants, as per SMT-LIB 2 */
Tsort     SORT_DECIMAL = DAG_SORT_NULL; /**< sort for decimal constants, as per SMT-LIB 2 */

Tsymb     PREDICATE_LESS = SYMB_NULL;
Tsymb     PREDICATE_LEQ = SYMB_NULL;
Tsymb     PREDICATE_GREATER = SYMB_NULL;
Tsymb     PREDICATE_GREATEREQ = SYMB_NULL;
Tsymb     PREDICATE_ISINT = SYMB_NULL;

char * PREDICATE_LESS_STR = "<";
char * PREDICATE_LEQ_STR = "<=";
char * PREDICATE_GREATER_STR = ">";
char * PREDICATE_GREATEREQ_STR = ">=";
char * PREDICATE_ISINT_STR = "is_int";

Tsymb     FUNCTION_TOREAL = SYMB_NULL;
Tsymb     FUNCTION_TOINT = SYMB_NULL;

char    * FUNCTION_TOREAL_STR = "to_real";
char    * FUNCTION_TOINT_STR = "to_int";

Tsymb     FUNCTION_SUM = SYMB_NULL;
Tsymb     FUNCTION_PROD = SYMB_NULL;
Tsymb     FUNCTION_UNARY_MINUS = SYMB_NULL;
Tsymb     FUNCTION_UNARY_MINUS_ALT = SYMB_NULL;
Tsymb     FUNCTION_MINUS = SYMB_NULL;
Tsymb     FUNCTION_DIV = SYMB_NULL;
Tsymb     FUNCTION_ABS = SYMB_NULL;
Tsymb     FUNCTION_MOD = SYMB_NULL;

/** \brief String of the predefined symbol for addition. */
char * FUNCTION_SUM_STR = "+";
/** \brief String of the predefined symbol for multiplication. */
char * FUNCTION_PROD_STR = "*";
/** \brief String of the predefined symbol for opposite. */
char * FUNCTION_UNARY_MINUS_STR = "-";
/** \brief String of the predefined symbol for subtraction. */
char * FUNCTION_MINUS_STR = "-";
/** \brief String of the predefined symbol for integer division. */
char * FUNCTION_INT_DIV_STR = "div";
/** \brief String of the predefined symbol for division. */
char * FUNCTION_DIV_STR = "/";
/** \brief String of the predefined symbol for absolute value. */
char * FUNCTION_ABS_STR = "abs";
/** \brief String of the predefined symbol for modulo. */
char * FUNCTION_MOD_STR = "mod";

Tsymb     FUNCTION_SELECT = SYMB_NULL;
Tsymb     FUNCTION_STORE = SYMB_NULL;

/** \brief String of predefined symbol for array element selection. */
char * FUNCTION_SELECT_STR = "select";
/** \brief String of predefined symbol for array element assignment. */
char * FUNCTION_STORE_STR = "store";

TDAG DAG_ONE = SYMB_NULL;
TDAG DAG_ZERO = SYMB_NULL;


/**
   \brief String of the predefined symbol for variable 0 (for difference logic) */
char * FUNCTION_ZERO_VARIABLE_STR = "veriT__zero";
Tsymb  FUNCTION_ZERO_VARIABLE = SYMB_NULL;

/*----------------------------------------------------------------*/

static char * logic = NULL;
static int init = 0;

/*
  ----------------------------------------------------------------
  Theory stuff
  ----------------------------------------------------------------
*/

/**
   \brief Creates symbols for quantifiers */
static void
DAG_sig_quantifiers(void)
{
  QUANTIFIER_EXISTS =
  DAG_symb_new(QUANTIFIER_EXISTS_STR, SYMB_QUANTIFIER, SORT_BOOLEAN);
  DAG_symb_set_predefined(QUANTIFIER_EXISTS);
  DAG_symb_set_interpreted (QUANTIFIER_EXISTS);
  QUANTIFIER_FORALL =
  DAG_symb_new(QUANTIFIER_FORALL_STR, SYMB_QUANTIFIER, SORT_BOOLEAN);
  DAG_symb_set_predefined(QUANTIFIER_FORALL);
  DAG_symb_set_interpreted (QUANTIFIER_FORALL);
}

/* -------------------------------------------------------------- */

static void
DAG_sig_let(void)
{
  LET = DAG_symb_new(LET_STR, SYMB_LET, DAG_SORT_NULL);
  DAG_symb_set_predefined(LET);
  DAG_symb_set_interpreted (LET);
}

/* -------------------------------------------------------------- */

static void
DAG_sig_extensions(void)
{
  LAMBDA = DAG_symb_new(LAMBDA_STR, SYMB_LAMBDA, DAG_SORT_NULL);
  DAG_symb_set_predefined(LAMBDA);
  DAG_symb_set_interpreted (LAMBDA);
  APPLY_LAMBDA = DAG_symb_new(APPLY_LAMBDA_STR, SYMB_APPLY, DAG_SORT_NULL);
  DAG_symb_set_predefined(APPLY_LAMBDA);
  DAG_symb_set_interpreted (APPLY_LAMBDA);
}

/* -------------------------------------------------------------- */

/**
 \brief Creates symbols for core operators
 
 \note Reference: The SMT-LIB Standard Version 2.0. p.30.
 
 \verbatim
 :sorts ((Bool 0))
 
 :funs ((true Bool)  
 (false Bool)
 (not Bool Bool)
 (=> Bool Bool Bool :right-assoc)
 (and Bool Bool Bool :left-assoc)
 (or Bool Bool Bool :left-assoc)
 (xor Bool Bool Bool :left-assoc)
 (par (A) (= A A Bool :chainable))
 (par (A) (distinct A A Bool :pairwise))
 (par (A) (ite Bool A A A))
 \endverbatim
 */
static void
DAG_sig_smtlib2_Core (void)
{
  Tsort sort;
  Tsort sortv = DAG_sort_new_var(NULL);
  
  /* SORT_BOOLEAN, SYMB_TRUE, SYMB_FALSE created at start-up by DAG */
  /* not */
  sort = DAG_sort_new_args(NULL, 2, SORT_BOOLEAN, SORT_BOOLEAN, NULL);
  CONNECTOR_NOT = DAG_symb_new(CONNECTOR_NOT_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_NOT);
  DAG_symb_set_interpreted (CONNECTOR_NOT);
  
  /* => and or xor = */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY,
			   SORT_BOOLEAN, SORT_BOOLEAN, NULL);
  CONNECTOR_IMPLIES = DAG_symb_new(CONNECTOR_IMPLIES_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_IMPLIES);
  DAG_symb_set_interpreted (CONNECTOR_IMPLIES);
  CONNECTOR_AND = DAG_symb_new(CONNECTOR_AND_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_AND);
  DAG_symb_set_interpreted (CONNECTOR_AND);
  CONNECTOR_OR = DAG_symb_new(CONNECTOR_OR_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_OR);
  DAG_symb_set_interpreted (CONNECTOR_OR);
  CONNECTOR_XOR = DAG_symb_new(CONNECTOR_XOR_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_XOR);
  DAG_symb_set_interpreted (CONNECTOR_XOR);
  CONNECTOR_EQUIV = DAG_symb_new(CONNECTOR_EQUIV_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_EQUIV);
  DAG_symb_set_interpreted (CONNECTOR_EQUIV);
  
  /* = distinct */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, sortv, SORT_BOOLEAN, NULL);
  PREDICATE_EQ = DAG_symb_new(PREDICATE_EQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_EQ);
  DAG_symb_set_interpreted (PREDICATE_EQ);
  PREDICATE_DISTINCT = DAG_symb_new(PREDICATE_DISTINCT_STR, SYMB_PREDICATE,
				     sort);
  DAG_symb_set_predefined(PREDICATE_DISTINCT);
  DAG_symb_set_interpreted (PREDICATE_DISTINCT);
  
  /* ite */
  sort = DAG_sort_new_args(NULL, 4, SORT_BOOLEAN, sortv, sortv, sortv, NULL);
  FUNCTION_ITE = DAG_symb_new(FUNCTION_ITE_STR, SYMB_ITE_FUNC, sort);
  DAG_symb_set_predefined(FUNCTION_ITE);
  DAG_symb_set_interpreted (FUNCTION_ITE);
  sort = DAG_sort_new_args(NULL, 4, SORT_BOOLEAN, SORT_BOOLEAN,
			    SORT_BOOLEAN, SORT_BOOLEAN, NULL);
  CONNECTOR_ITE = DAG_symb_new(CONNECTOR_ITE_STR, SYMB_BOOLEAN, sort);
  DAG_symb_set_predefined(CONNECTOR_ITE);
  DAG_symb_set_interpreted (CONNECTOR_ITE);
}

/* -------------------------------------------------------------- */

/**
 \note From www.smtlib.org
 
 \verbatim
 :funs ((NUMERAL Int) 
 (- Int Int)                 ; negation
 (- Int Int Int :left-assoc) ; subtraction
 (+ Int Int Int :left-assoc) 
 (* Int Int Int :left-assoc)
 (div Int Int Int :left-assoc)
 (mod Int Int Int)
 (abs Int Int)
 (<= Int Int Bool :chainable)
 (<  Int Int Bool :chainable)
 (>= Int Int Bool :chainable)
 (>  Int Int Bool :chainable)
 )
 \endverbatim
 */
static void
DAG_sig_smtlib2_Ints (void)
{
  Tsort sort;
  
  /* Int */
  SORT_INTEGER = DAG_sort_new(SORT_INTEGER_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_INTEGER);
  
  /* - (negation), abs */
  sort = DAG_sort_new_args(NULL, 2, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_UNARY_MINUS =
  DAG_symb_new(FUNCTION_UNARY_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_UNARY_MINUS);
  DAG_symb_set_interpreted (FUNCTION_UNARY_MINUS);
  FUNCTION_ABS = DAG_symb_new(FUNCTION_ABS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_ABS);
  DAG_symb_set_interpreted (FUNCTION_ABS);
  /* - (subtraction), +, *, div */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_MINUS = DAG_symb_new(FUNCTION_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_MINUS);
  DAG_symb_set_interpreted(FUNCTION_MINUS);
  FUNCTION_SUM = DAG_symb_new(FUNCTION_SUM_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_SUM);
  DAG_symb_set_interpreted(FUNCTION_SUM);
  FUNCTION_PROD = DAG_symb_new(FUNCTION_PROD_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_PROD);
  DAG_symb_set_interpreted(FUNCTION_PROD);
  FUNCTION_DIV = DAG_symb_new(FUNCTION_INT_DIV_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_DIV);
  DAG_symb_set_interpreted(FUNCTION_DIV);
  /* mod */
  sort = DAG_sort_new_args(NULL, 3, SORT_INTEGER, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_MOD = DAG_symb_new(FUNCTION_MOD_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_MOD);
  DAG_symb_set_interpreted(FUNCTION_MOD);
  /* <= < >= > */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_INTEGER, SORT_BOOLEAN, NULL);
  PREDICATE_LESS = DAG_symb_new(PREDICATE_LESS_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LESS);
  DAG_symb_set_interpreted (PREDICATE_LESS);
  PREDICATE_LEQ = DAG_symb_new(PREDICATE_LEQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LEQ);
  DAG_symb_set_interpreted (PREDICATE_LEQ);
  PREDICATE_GREATER = DAG_symb_new(PREDICATE_GREATER_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATER);
  DAG_symb_set_interpreted (PREDICATE_GREATER);
  PREDICATE_GREATEREQ = DAG_symb_new(PREDICATE_GREATEREQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATEREQ);
  DAG_symb_set_interpreted (PREDICATE_GREATEREQ);
  
  SORT_NUMERAL = SORT_INTEGER;
}

/* -------------------------------------------------------------- */

/**
 
 \brief Creates signature for SMT-LIB2 logic Reals
 \verbatim
 :sorts ((Real 0))
 
 :funs ((NUMERAL Real) 
 (DECIMAL Real) 
 (- Real Real)                  ; negation
 (- Real Real Real :left-assoc) ; subtraction
 (+ Real Real Real :left-assoc) 
 (* Real Real Real :left-assoc)
 (/ Real Real Real :left-assoc)
 (<= Real Real Bool :chainable)
 (<  Real Real Bool :chainable)
 (>= Real Real Bool :chainable)
 (>  Real Real Bool :chainable)
 )
 \verbatim
 */
static void
DAG_sig_smtlib2_Reals (void)
{
  Tsort sort;
  
  /* Real */
  SORT_REAL = DAG_sort_new(SORT_REAL_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_REAL);
  
  /* - (negation) */
  sort = DAG_sort_new_args(NULL, 2, SORT_REAL, SORT_REAL, NULL);
  FUNCTION_UNARY_MINUS =
  DAG_symb_new(FUNCTION_UNARY_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_UNARY_MINUS);
  DAG_symb_set_interpreted (FUNCTION_UNARY_MINUS);
  /* - (subtraction), +, *, / */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_REAL, SORT_REAL, NULL);
  FUNCTION_MINUS = DAG_symb_new(FUNCTION_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_MINUS);
  DAG_symb_set_interpreted(FUNCTION_MINUS);
  FUNCTION_SUM = DAG_symb_new(FUNCTION_SUM_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_SUM);
  DAG_symb_set_interpreted(FUNCTION_SUM);
  FUNCTION_PROD = DAG_symb_new(FUNCTION_PROD_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_PROD);
  DAG_symb_set_interpreted(FUNCTION_PROD);
  FUNCTION_DIV = DAG_symb_new(FUNCTION_DIV_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_DIV);
  DAG_symb_set_interpreted(FUNCTION_DIV);
  /* <= < >= > */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_REAL, SORT_BOOLEAN, NULL);
  PREDICATE_LESS = DAG_symb_new(PREDICATE_LESS_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LESS);
  DAG_symb_set_interpreted (PREDICATE_LESS);
  PREDICATE_LEQ = DAG_symb_new(PREDICATE_LEQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LEQ);
  DAG_symb_set_interpreted (PREDICATE_LEQ);
  PREDICATE_GREATER = DAG_symb_new(PREDICATE_GREATER_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATER);
  DAG_symb_set_interpreted (PREDICATE_GREATER);
  PREDICATE_GREATEREQ = DAG_symb_new(PREDICATE_GREATEREQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATEREQ);
  DAG_symb_set_interpreted (PREDICATE_GREATEREQ);
 
  SORT_NUMERAL = SORT_REAL;
  SORT_DECIMAL = SORT_REAL;
}


/**
 
 \brief Creates signature for SMT-LIB2 logic QF_UFIDL
 \verbatim
 :theories (Ints)
 
 
 :language
 "Closed quantifier-free formulas built over an arbitrary expansion with 
 free sort and function symbols of the signature consisting of 
 - all the sort and function symbols of Core and
 - the following symbols of Int:
 
 :sorts ((Int 0))
 :funs ((NUMERAL Int) 
 (- Int Int Int)
 (+ Int Int Int) 
 (<= Int Int Bool)
 (< Int Int Bool)
 (>= Int Int Bool)
 (> Int Int Bool)
 )
 \endverbatim
 */
static void
DAG_sig_smtlib2_QF_UFIDL (void)
{
  Tsort sort;
  
  /* Int */
  SORT_INTEGER = DAG_sort_new(SORT_INTEGER_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_INTEGER);
  
  /* - (subtraction), +, */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_MINUS = DAG_symb_new(FUNCTION_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_MINUS);
  DAG_symb_set_interpreted(FUNCTION_MINUS);
  FUNCTION_SUM = DAG_symb_new(FUNCTION_SUM_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_SUM);
  DAG_symb_set_interpreted(FUNCTION_SUM);
  /* <= < >= > */
  sort = DAG_sort_new_args(NULL, 3, SORT_INTEGER, SORT_INTEGER, SORT_BOOLEAN, NULL);
  PREDICATE_LESS = DAG_symb_new(PREDICATE_LESS_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LESS);
  DAG_symb_set_interpreted (PREDICATE_LESS);
  PREDICATE_LEQ = DAG_symb_new(PREDICATE_LEQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LEQ);
  DAG_symb_set_interpreted (PREDICATE_LEQ);
  PREDICATE_GREATER = DAG_symb_new(PREDICATE_GREATER_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATER);
  DAG_symb_set_interpreted (PREDICATE_GREATER);
  PREDICATE_GREATEREQ = DAG_symb_new(PREDICATE_GREATEREQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATEREQ);
  DAG_symb_set_interpreted (PREDICATE_GREATEREQ);  
  
  SORT_NUMERAL = SORT_INTEGER;
}

/* -------------------------------------------------------------- */

/**
 \brief a variable used to rewrite expressions in difference logic
 \param sort The sort of numbers (SORT_INTEGER or SORT_REAL)
 */
static void
DAG_sig_zero(Tsort sort)
{
  FUNCTION_ZERO_VARIABLE =
    DAG_symb_new(FUNCTION_ZERO_VARIABLE_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_ZERO_VARIABLE);
  DAG_symb_set_interpreted (FUNCTION_ZERO_VARIABLE);
}

/* -------------------------------------------------------------- */

/**
 \todo simplify uses DAG_ONE and DAG_ZERO - see how to best code this dependency.
 */
static void
DAG_sig_arith_constants(void)
{
  if (SORT_INTEGER == DAG_SORT_NULL)
  {
    SORT_INTEGER = DAG_sort_new(SORT_INTEGER_STR, 0, NULL);
    DAG_sort_set_predefined(SORT_INTEGER);
  }
  if (DAG_ZERO == SYMB_NULL)
  {
    DAG_ZERO = DAG_dup(DAG_new_integer(0));
    DAG_ONE = DAG_dup(DAG_new_integer(1));
  }
}

/* -------------------------------------------------------------- */

/**
 \note From www.smtlib.org
 
 \verbatim
 :sorts ((Array 2))
 
 :funs ((par (X Y) (select (Array X Y) X Y))
 (par (X Y) (store (Array X Y) X Y (Array X Y))) )
 \endverbatim
 */
static void
DAG_sig_smtlib2_ArraysEx (void)
{
  Tsort sort, X, Y, sort_inst;
  Tsort * sub;
  
  /* Array */
  SORT_ARRAY = DAG_sort_new_param(SORT_ARRAY_STR, 2);
  DAG_sort_set_predefined(SORT_ARRAY);
  
  X = DAG_sort_new_var(NULL);
  Y = DAG_sort_new_var(NULL);
  
  MY_MALLOC(sub, 2 * sizeof(Tsort));
  sub[0] = X;
  sub[1] = Y;
  sort_inst = DAG_sort_new_inst(NULL, SORT_ARRAY, 2, sub);
  
  sort = DAG_sort_new_args(NULL, 3, sort_inst, X, Y, NULL);
  FUNCTION_SELECT = DAG_symb_new(FUNCTION_SELECT_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_SELECT);
  
  sort = DAG_sort_new_args(NULL, 4, sort_inst, X, Y, sort_inst, NULL);
  FUNCTION_STORE = DAG_symb_new(FUNCTION_STORE_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_STORE);
}


/* -------------------------------------------------------------- */

/**
 \note From www.smtlib.org
 
 \todo negation, subtraction, addition, multiplication functions and
 comparison predicates are overloaded - but veriT throughout (pre-processing, arithmetic module) only considers
 one possible instance of such symbols. 
 
 \todo see how the divisible family of predicates should be implemented.
 
 \verbatim
 :sorts ((Int 0) (Real 0))
 
 :funs ((NUMERAL Int) 
 (- Int Int)                 ; negation
 (- Int Int Int :left-assoc) ; subtraction
 (+ Int Int Int :left-assoc) 
 (* Int Int Int :left-assoc)
 (div Int Int Int :left-assoc)
 (mod Int Int Int)
 (abs Int Int)
 (<= Int Int Bool :chainable)
 (<  Int Int Bool :chainable)
 (>= Int Int Bool :chainable)
 (>  Int Int Bool :chainable)
 (DECIMAL Real) 
 (- Real Real)                  ; negation
 (- Real Real Real :left-assoc) ; subtraction
 (+ Real Real Real :left-assoc) 
 (* Real Real Real :left-assoc)
 (/ Real Real Real :left-assoc)
 (<= Real Real Bool :chainable)
 (<  Real Real Bool :chainable)
 (>= Real Real Bool :chainable)
 (>  Real Real Bool :chainable)
 (to_real Int Real)
 (to_int Real Int)
 (is_int Real Bool)
 )
 
 :funs_description
 "All ranked function symbols of the form
 ((_ divisible n) Int Bool)
 where n is a positive numeral.
 \endverbatim
 */
static void
DAG_sig_smtlib2_Reals_Ints (void)
{
  Tsort sort;
  /* Int, Real */
  SORT_INTEGER = DAG_sort_new(SORT_INTEGER_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_INTEGER);
  SORT_REAL = DAG_sort_new(SORT_REAL_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_REAL);
  /* to_real */
  sort = DAG_sort_new_args(NULL, 2, SORT_INTEGER, SORT_REAL, NULL);
  FUNCTION_TOREAL = DAG_symb_new(FUNCTION_TOREAL_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_TOREAL);
  /* to_int */
  sort = DAG_sort_new_args(NULL, 2, SORT_REAL, SORT_INTEGER, NULL);
  FUNCTION_TOINT = DAG_symb_new(FUNCTION_TOINT_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_TOINT);
  /* is_int */
  sort = DAG_sort_new_args(NULL, 2, SORT_REAL, SORT_BOOLEAN, NULL);
  PREDICATE_ISINT = DAG_symb_new(PREDICATE_ISINT_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_ISINT);
  /* - (negation) */
  sort = DAG_sort_new_args(NULL, 2, SORT_REAL, SORT_REAL, NULL);
  FUNCTION_UNARY_MINUS =
  DAG_symb_new(FUNCTION_UNARY_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_UNARY_MINUS);
  DAG_symb_set_interpreted (FUNCTION_UNARY_MINUS);
  /* - (subtraction), +, *, / */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_REAL, SORT_REAL, NULL);
  FUNCTION_MINUS = DAG_symb_new(FUNCTION_MINUS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_MINUS);
  DAG_symb_set_interpreted(FUNCTION_MINUS);
  FUNCTION_SUM = DAG_symb_new(FUNCTION_SUM_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_SUM);
  DAG_symb_set_interpreted(FUNCTION_SUM);
  FUNCTION_PROD = DAG_symb_new(FUNCTION_PROD_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_PROD);
  DAG_symb_set_interpreted(FUNCTION_PROD);
  FUNCTION_DIV = DAG_symb_new(FUNCTION_DIV_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_DIV);
  DAG_symb_set_interpreted(FUNCTION_DIV);
  /* <= < >= > */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_REAL, SORT_BOOLEAN, NULL);
  PREDICATE_LESS = DAG_symb_new(PREDICATE_LESS_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LESS);
  DAG_symb_set_interpreted (PREDICATE_LESS);
  PREDICATE_LEQ = DAG_symb_new(PREDICATE_LEQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_LEQ);
  DAG_symb_set_interpreted (PREDICATE_LEQ);
  PREDICATE_GREATER = DAG_symb_new(PREDICATE_GREATER_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATER);
  DAG_symb_set_interpreted (PREDICATE_GREATER);
  PREDICATE_GREATEREQ = DAG_symb_new(PREDICATE_GREATEREQ_STR, SYMB_PREDICATE, sort);
  DAG_symb_set_predefined(PREDICATE_GREATEREQ);
  DAG_symb_set_interpreted (PREDICATE_GREATEREQ);
  
  /* abs */
  sort = DAG_sort_new_args(NULL, 2, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_ABS = DAG_symb_new(FUNCTION_ABS_STR, SYMB_FUNCTION, sort);
  DAG_symb_set_predefined(FUNCTION_ABS);
  DAG_symb_set_interpreted (FUNCTION_ABS);
  /* div */
  sort = DAG_sort_new_args(NULL, DAG_SORT_NARY, SORT_INTEGER, SORT_INTEGER, NULL);
  {
    Tsymb tmp = DAG_symb_new(FUNCTION_INT_DIV_STR, SYMB_FUNCTION, sort);
    DAG_symb_set_predefined(tmp);
  }
  /* mod */
  sort = DAG_sort_new_args(NULL, 3, SORT_INTEGER, SORT_INTEGER, SORT_INTEGER, NULL);
  FUNCTION_MOD = DAG_symb_new(FUNCTION_MOD_STR, SYMB_FUNCTION, sort);
  
  SORT_NUMERAL = SORT_INTEGER;
  SORT_DECIMAL = SORT_REAL;
}


/* -------------------------------------------------------------- */

void
DAG_smtlib_logic_set (const char * str)
{
  if (init)
    veriT_error ("setting logic twice");
  init = 1;
  logic = strmake(str);
  
  DAG_sig_let();
  DAG_sig_smtlib2_Core();
  if (str != NULL)
  {
    if (!strcmp(str, "AUFLIA"))
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Ints();
      DAG_sig_smtlib2_ArraysEx();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "AUFLIRA") == 0 || strcmp(str, "UNKNOWN") == 0)
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Reals_Ints();
      DAG_sig_smtlib2_ArraysEx();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "AUFNIRA") == 0)
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Reals_Ints();
      DAG_sig_smtlib2_ArraysEx();
      DAG_sig_arith_constants();
      }
    else if (strcmp(str, "LRA") == 0)
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    /* \todo
     else if (strcmp(str, "QF_ABV") == 0)
     {
     DAG_sig_smtlib2_ArraysEx();
     }
     else if (strcmp(str, "QF_AUFBV") == 0)
     {
     DAG_sig_smtlib2_ArraysEx();
     } */
    else if (strcmp(str, "QF_AUFLIA") == 0)
    {
      DAG_sig_smtlib2_Ints();
      DAG_sig_smtlib2_ArraysEx();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_AX") == 0)
    {
      DAG_sig_smtlib2_ArraysEx();
    }
    /* \todo
     else if (strcmp(str, "QF_BV") == 0)
     {
     }
     */
    else if (strcmp(str, "QF_IDL") == 0)
    {
      DAG_sig_smtlib2_Ints();
      DAG_sig_arith_constants();
      DAG_sig_zero(SORT_INTEGER);
    }
    else if (strcmp(str, "QF_LIA") == 0)
    {
      DAG_sig_smtlib2_Ints();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_LRA") == 0)
    {
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_NIA") == 0)
    {
      DAG_sig_smtlib2_Ints();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_NRA") == 0)
    {
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_RDL") == 0)
    {
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
      DAG_sig_zero(SORT_REAL);
    }
    else if (strcmp(str, "QF_UF") == 0)
    {
    }
    /* \todo
     else if (strcmp(str, "QF_UFBV") == 0)
     {
     
     }*/
    else if (strcmp(str, "QF_UFIDL") == 0)
    {
      DAG_sig_smtlib2_QF_UFIDL();
      DAG_sig_arith_constants();
      DAG_sig_zero(SORT_INTEGER);
    }
    else if (strcmp(str, "QF_UFLIA") == 0)
    {
      DAG_sig_smtlib2_Ints();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_UFLRA") == 0)
    {
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "QF_UFNRA") == 0)
    {
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "UFLRA") == 0)
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Reals();
      DAG_sig_arith_constants();
    }
    else if (strcmp(str, "UFNIA") == 0)
    {
      DAG_sig_quantifiers();
      DAG_sig_smtlib2_Ints();
      DAG_sig_arith_constants();
    }
    else
    {
      my_DAG_warning("Unrecognized SMT-LIB2 logic: %s.\n", str);
      my_DAG_warning("Assuming Core logic.\n");
    }
  }
  DAG_sig_extensions();
}

/* -------------------------------------------------------------- */

char * 
DAG_smtlib_logic (void)
{
  return logic;
}

/* -------------------------------------------------------------- */

void
DAG_smtlib_logic_init (void)
{
  assert(init == 0);
}

/* -------------------------------------------------------------- */

void
DAG_smtlib_logic_done (void)
{
  free(logic);
}
