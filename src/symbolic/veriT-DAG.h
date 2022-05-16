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

/**
  \file veriT-DAG.h
  \author Pascal Fontaine

  \brief API to build formulas, terms, symbols and sorts to use with libveriT.

  Type Tsort is for the representation of sorts, type Tsymb is for symbols,
  and type TDAG is for terms and formulas. 

  A term or formula is made of a symbol and the sub-terms or
  sub-formulas.  A symbol has a sort. The sort for predicate and
  function symbols is a tuple of sorts, where the last element of the
  tuple is the sort of the result and the remaining elements of the
  type are the sorts of the parameters.

  Some technical details:

  - Formulas and terms are represented by DAGs.  

  - Maximal sharing is used (two identical DAGs are merged.)
   
  - Facilities for sorts are provided.  

  - Facilities for symbols are provided. Each symbol has a sort.
   
  - Declaring several times a same symbol is allowed, as long as
   declaration are coherent (i.e. the same).  

   - Using an undeclared symbol issues a warning, but no error
   message.  

   - DAGs are associated reference counters. For any used DAG, its
   reference counter should be greater than 0. DAGs are nonetheless
   created with a reference counter set to zero in the case of DAGs
   that are immediately set as subDAGs (think bottom-up construction
   of terms in a parser). In other situations, the reference_counter
   should be set explicitly to one by DAG_dup.

*/

#ifndef __VERIT_DAG_H
#define __VERIT_DAG_H

#include <stdarg.h>

#include "assoc.h"
#include "hash.h"
#include "list.h"
#include "stack.h"
#include "table.h"
#include "types.h"

#include "DAG-symb.h"
#include "DAG-sort.h"
#include "DAG.h"

/*--------------------------------------------------------------*/

#define DAG_ptr_of_symb(symb) \
  ((void *) (uintptr_t) (symb))

#define DAG_symb_of_ptr(P) \
  ((Tsymb) (uintptr_t) (P))

/*--------------------------------------------------------------*/
/*        Predefined symbols                                    */
/*--------------------------------------------------------------*/

/** \brief String for the predefined symbol TRUE */
extern char *    BOOLEAN_TRUE_STR;
/** \brief String for the predefined symbol FALSE */
extern char *    BOOLEAN_FALSE_STR;
/** \brief Predefined symbol for boolean constant TRUE */
extern Tsymb     BOOLEAN_TRUE;
/** \brief Predefined symbol for boolean constant FALSE */
extern Tsymb     BOOLEAN_FALSE;

/** \brief Name of predefined negation symbol */
extern char *    CONNECTOR_NOT_STR;
/** \brief Name of predefined disjunction symbol */
extern char *    CONNECTOR_OR_STR;
/** \brief Name of predefined exclusive disjunction symbol */
extern char *    CONNECTOR_XOR_STR;
/** \brief Name of predefined conjunction symbol */
extern char *    CONNECTOR_AND_STR;
/** \brief Name of predefined implication symbol */
extern char *    CONNECTOR_IMPLIES_STR;
/** \brief Name of predefined equivalence symbol */
extern char *    CONNECTOR_EQUIV_STR;
/** \brief Name of predefined (boolean) conditional symbol */
extern char *    CONNECTOR_ITE_STR;
/** \brief Predefined symbol for negation */
extern Tsymb     CONNECTOR_NOT;
/** \brief Predefined symbol for disjunction (n-ary) */
extern Tsymb     CONNECTOR_OR;
/** \brief Predefined symbol for exclusive or (n-ary) */
extern Tsymb     CONNECTOR_XOR;
/** \brief Predefined symbol for conjunction (n-ary) */
extern Tsymb     CONNECTOR_AND;
/** \brief Predefined symbol for implication */
extern Tsymb     CONNECTOR_IMPLIES;
/** \brief Predefined symbol for equivalence */
extern Tsymb     CONNECTOR_EQUIV;
/** \brief Predefined symbol for (boolean) conditional */
extern Tsymb     CONNECTOR_ITE;

/** \brief String for the equality symbol */
extern char *    PREDICATE_EQ_STR;
/** \brief Predefined symbol for the equality operator */
extern Tsymb     PREDICATE_EQ;
/** \brief String for the distinct symbol */
extern char *    PREDICATE_DISTINCT_STR;
/** \brief Predefined symbol for the distinct operator */
extern Tsymb     PREDICATE_DISTINCT;
/** \brief String for the predefined relational symbol "smaller than" */
extern char *    PREDICATE_LESS_STR;
/** \brief String for the predefined relational symbol "smaller or equal" */
extern char *    PREDICATE_LEQ_STR;
/** \brief String for the predefined relational symbol "greater than" */
extern char *    PREDICATE_GREATER_STR;
/** \brief String for the predefined relational symbol "greater or equal" */
extern char *    PREDICATE_GREATEREQ_STR;
/** \brief String for the predefined predicate IsInt */
extern char *    PREDICATE_ISINT_STR;

/** \brief Symbol for the strictly smaller than relational operator */
extern Tsymb     PREDICATE_LESS;
/** \brief Symbol for the smaller or equal relational operator */
extern Tsymb     PREDICATE_LEQ;
/** \brief Symbol for the strictly greater than relational operator */
extern Tsymb     PREDICATE_GREATER;
/** \brief Symbol for the greater or equal relational operator */
extern Tsymb     PREDICATE_GREATEREQ;
/** \brief Symbol for the predicate testing integrality on real numbers */
extern Tsymb     PREDICATE_ISINT;

/** \brief String for variable 0 (for difference logic) */
extern char *    FUNCTION_ZERO_VARIABLE_STR;
/** \brief Symbol for variable 0 (for difference logic) */
extern Tsymb     FUNCTION_ZERO_VARIABLE;

/** \brief String of the predefined symbol for the functional conditional */
extern char *    FUNCTION_ITE_STR;
/** \brief Symbol for the functional operator IF THEN ELSE */
extern Tsymb     FUNCTION_ITE;

/** \brief String of the predefined symbol for addition */
extern char *    FUNCTION_SUM_STR;
/** \brief String of the predefined symbol for multiplication */
extern char *    FUNCTION_PROD_STR;
/** \brief String of the predefined symbol for opposite */
extern char *    FUNCTION_UNARY_MINUS_STR;
/** \brief String of the predefined symbol for subtraction */
extern char *    FUNCTION_MINUS_STR;
/** \brief String of the predefined symbol for division */
extern char *    FUNCTION_DIV_STR;

/** \brief Predefined symbol for arithmetic sum (n-ary) */
extern Tsymb     FUNCTION_SUM;
/** \brief Predefined symbol for arithmetic product (n-ary) */
extern Tsymb     FUNCTION_PROD;
/** \brief Predefined symbol for arithmetic unary minus */
extern Tsymb     FUNCTION_UNARY_MINUS;
/** \brief Alternative predefined symbol for arithmetic unary minus */
extern Tsymb     FUNCTION_UNARY_MINUS_ALT;
/** \brief Predefined symbol for arithmetic binary minus */
extern Tsymb     FUNCTION_MINUS;
/** \brief Predefined symbol for arithmetic division minus */
extern Tsymb     FUNCTION_DIV;

/** \brief String of the predefined symbol for existential quantification */
extern char *    QUANTIFIER_EXISTS_STR;
/** \brief String of the predefined symbol for universal quantification */
extern char *    QUANTIFIER_FORALL_STR;
/** \brief Predefined symbol for existential quantification */
extern Tsymb     QUANTIFIER_EXISTS;
/** \brief Predefined symbol for universal quantification */
extern Tsymb     QUANTIFIER_FORALL;

/** \brief String of the predefined symbol for let construction */
extern char *    LET_STR;
/** \brief Predefined symbol for let construction */
extern Tsymb     LET;

/** \brief String of the predefined symbol for lambda abstraction */
extern char *    LAMBDA_STR;
/** \brief String of the predefined symbol for beta reduction */
extern char *    APPLY_LAMBDA_STR;
/** \brief Predefined symbol for lambda-abstraction operator */
extern Tsymb     LAMBDA;
/** \brief Predefined symbol for beta reduction */
extern Tsymb     APPLY_LAMBDA;

/** \brief String of predefined symbol for array element selection */
extern char *    FUNCTION_SELECT_STR;
/** \brief String of predefined symbol for array element assignment */
extern char *    FUNCTION_STORE_STR;
/** \brief Predefined symbol for array element selection */
extern Tsymb     FUNCTION_SELECT;
/** \brief Predefined symbol for array element assignment */
extern Tsymb     FUNCTION_STORE;

/**
   \brief Tests if symbol c is a boolean connector
   \param c shall be an expression of type Tsymb */
#define boolean_connector(c) ((c == CONNECTOR_NOT) || \
			      (c == CONNECTOR_OR) || \
			      (c == CONNECTOR_XOR) || \
			      (c == CONNECTOR_AND) || \
			      (c == CONNECTOR_IMPLIES) || \
			      (c == CONNECTOR_EQUIV) || \
			      (c == CONNECTOR_ITE))

/**
   \brief Tests if symbol c is a boolean constant
   \param c shall be an expression of type Tsymb */
#define boolean_constant(c) ((c == BOOLEAN_TRUE) || \
			     (c == BOOLEAN_FALSE))

/**
   \brief Tests if symbol c is a quantifier
   \param c shall be an expression of type Tsymb */
#define quantifier(c) ((c == QUANTIFIER_EXISTS) || \
		       (c == QUANTIFIER_FORALL))

/**
   \brief Tests if symbol c is a quantifier
   \param c shall be an expression of type Tsymb */
#define binder(c) ((c == QUANTIFIER_EXISTS) || \
		   (c == QUANTIFIER_FORALL) || \
		   (c == LAMBDA))

/**
   \brief Tests if symbol c is an arithmetic operator
   \param c shall be an expression of type Tsymb */
#define arith_function(c) ((c == FUNCTION_SUM) || \
			   (c == FUNCTION_PROD) || \
			   (c == FUNCTION_UNARY_MINUS) || \
			   (c == FUNCTION_UNARY_MINUS_ALT) || \
			   (c == FUNCTION_MINUS) || \
			   (c == FUNCTION_DIV))

/**
   \brief Tests if symbol c is a arithmetic comparison operator
   \param c shall be an expression of type Tsymb */
#define arith_comparison(c) ((c == PREDICATE_LESS) || \
			     (c == PREDICATE_LEQ) ||   \
			     (c == PREDICATE_GREATER) ||  \
			     (c == PREDICATE_GREATEREQ))

#define unary_minus(c) ((c == FUNCTION_UNARY_MINUS) || \
			(c == FUNCTION_UNARY_MINUS_ALT))

extern void      DAG_smtlib_logic_init(void);
/**
   \brief Sets the logic.
   \param str is the name of the logic, NULL for default setup. Nomenclature is that of SMT-LIB 2.0
   \note This function must be called at most once  */
extern void      DAG_smtlib_logic_set(const char * str);

extern char *    DAG_smtlib_logic(void);

extern void      DAG_smtlib_logic_done(void);

#endif /* __VERIT_DAG_H */
