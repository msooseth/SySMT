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
   \file DAG.h
   \author Pascal Fontaine
   
   \brief Module for representing sorts, symbols, signatures, formulas,
   terms ...
   - Formulas and terms are represented by DAGs
   - Maximal sharing is used (two identical DAGs are merged)
   - Facilities for sorts are provided
   - Facilities for symbols are provided. Each symbol has a sort
   - Declaring several times a same symbol is allowed, as long as
   declaration are coherent (i.e. the same)
   - Using an undeclared symbol issues a warning, but no error
   message
   - Type checking is assumed to be done at the end, not on-the-fly.
   \todo Some things could be better:
   - polymorphism, subsorts
   - sorts should be unifiable
   - one should be able to use several "integer sort", let's say
   apple numbers and banana numbers
   - Attribute lists or Hash tables or both...
   - Hash table for symbols
   - optional on-the-fly type checking.
   - Functional simplification (that only depend on argument),
   and bit for functional simplification: apply simp on building terms */

#ifndef __DAG_H
#define __DAG_H

#include <stdarg.h>

#include "hash.h"
#include "list.h"
#include "table.h"
#include "stack.h"

#include "veriT-DAG.h"

/*
  --------------------------------------------------------------
  Main datastructure
  --------------------------------------------------------------
*/

typedef unsigned TDAG;
TSstack(_DAG, TDAG); /* typedefs Tstack_DAG */
TSstack(_DAGstack, Tstack_DAG); /* typedefs Tstack_DAGstack */

/** \brief special (NULL) value for type TDAG */
#define DAG_NULL ((TDAG) 0)

/**
 \brief Structure to represent DAGs
 */
struct TSDAG
{
  /** \brief topmost symbol */
  Tsymb     symb;
  /** \brief sort */
  Tsort     sort;
  /** \brief array of sub-terms */
  TDAG     *PDAG;
  /** \brief field for user */
  int       misc;
  /** \brief (private) hash key */
  unsigned  hash_key;
  /** \brief (private) reference counter */
  unsigned  gc_count;
#ifndef PEDANTIC
  /** \brief size of the array of sub-terms */
  unsigned  arity : 30;
  /** \brief indicates if DAG contains quantifiers (set on DAG construction) */
  bool      quant : 1;
  /** \brief indicates if DAG is ground (call qnt_ground on a DAG to set the ground bit on all (sub)terms) */
  bool      ground : 1;
#else
  unsigned  arity;
  bool      quant;
  bool      ground;
#endif
};

TSstack(_SDAG, struct TSDAG);

/** \brief The symbol table: stored in a single chunk of memory */
extern Tstack_SDAG DAG_table;

#define __DAG_DATA(DAG) (DAG_table->data[(TDAG) (DAG)])

/*
  --------------------------------------------------------------
  Accessors
  --------------------------------------------------------------
*/

/** \brief DAG symbol */
#define DAG_symb(DAG) (__DAG_DATA(DAG).symb)
/**  \brief DAG arity */
#define DAG_arity(DAG) (__DAG_DATA(DAG).arity)
/** \brief DAG sort */
#define DAG_sort(DAG) (__DAG_DATA(DAG).sort)
/** \brief Array of DAG args */
#define DAG_args(DAG) (__DAG_DATA(DAG).PDAG)
/** \brief DAG's (i-1)-th arg */
#define DAG_arg(DAG,i) (__DAG_DATA(DAG).PDAG[i])
/** \brief DAG's first arg */
#define DAG_arg0(DAG) (__DAG_DATA(DAG).PDAG[0])
/** \brief DAG's second arg */
#define DAG_arg1(DAG) (__DAG_DATA(DAG).PDAG[1])
/** \brief DAG's last arg */
#define DAG_argn(DAG) (__DAG_DATA(DAG).PDAG[DAG_arity(DAG) - 1])
/** \brief DAG misc */
#define DAG_misc(DAG) (__DAG_DATA(DAG).misc)
/** \brief DAG misc */
#define DAG_misc_set(DAG, val) (__DAG_DATA(DAG).misc = val)
/** \brief DAG contains quantifiers */
#define DAG_quant(DAG) (__DAG_DATA(DAG).quant)
/** \brief DAG is ground */
#define DAG_ground(DAG) (__DAG_DATA(DAG).ground)
/** \brief DAG hash key */
#define DAG_key(DAG) (__DAG_DATA(DAG).hash_key)

/*
  --------------------------------------------------------------
  Constructors - Destructors
  --------------------------------------------------------------
*/

/**
   \brief DAG constructor
   \param symb topmost symbol
   \param arity number of sub-terms
   \param PDAG array of subterms
   \return Creates (if new) and returns TDAG from symb and PDAG.
   \remark Destructive for PDAG */
extern TDAG      DAG_new(Tsymb symb, unsigned arity, TDAG * PDAG);

/**
   \brief DAG constructor
   \param symb The topmost symbol of the constructed term.
   \param ... subterms, followed by NULL.
   \pre The number of subterms needs to be compatible with the arity of symb
   \return Creates (if new) and returns TDAG from symb and given arguments */
extern TDAG      DAG_new_args(Tsymb symb, ...);

/**
   \brief like DAG_new, but with a list for sub terms
   \param symb the top-most symbol
   \param list the list of arguments
   \remark non destructive for the list */
extern TDAG      DAG_new_list(Tsymb symb, Tlist list);

/**
   \brief like DAG_new, but with a stack for sub terms
   \param symb the top-most symbol
   \param stack_arg the stack of arguments
   \remark non destructive for the stack */
extern TDAG      DAG_new_stack(Tsymb symb, Tstack_DAG stack_arg);

/**
   \brief Reference counter increment
   \param DAG its reference counter will be incremented
   \return the result is the same as the argument */
extern TDAG      DAG_dup(TDAG DAG);

/**
   \brief Destructor.
   \param DAG to be freed
   \remark The reference counter of DAG is decremented. If the resulting value
   is zero, then DAG is freed */
extern void      DAG_free(TDAG DAG);

/*
  --------------------------------------------------------------
  Specific constructors
  --------------------------------------------------------------
*/

/**
   \brief DAG constructor
   \param value an integer
   \return Creates (if new) and returns DAG representing integer value */
extern TDAG      DAG_new_integer(long value);

/**
   \brief DAG constructor
   \param num an integer interpreted as numerator
   \param den an integer interpreted as denominator
   \return Creates (if new) and returns DAG representing rational num/den.
   \remark User is responsible for overflow, if using version with
   native data types */
extern TDAG      DAG_new_rational(long num, long den);

/**
   \brief DAG constructor
   \param value textual representation of a numeral 0|[1-9][0-9]*
   \return Creates (if new) and returns DAG representing integer value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_numeral_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a decimal (0|[1-9][0-9]*)\.[0-9]+
   \return Creates (if new) and returns DAG representing decimal value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_decimal_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a binary #b[01]+
   \return Creates (if new) and returns DAG representing binary value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_binary_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of an hexadecimal #x[0-9A-Fa-f]+
   \return Creates (if new) and returns DAG representing hexadecimal value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_hex_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a floating point 0.[0-9]+ | [1-9][0-9]*.[0-9]+
   \return Creates (if new) and returns DAG representing floating point value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_decimal_str(char * value);
/* PF kept for backward compatibility with SMT-LIB 1.2 */
extern TDAG      DAG_new_float_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a rational [1-9][0-9]* / [0-9]+[1-9] or [1-9][0-9]*
   \return Creates (if new) and returns DAG representing rational value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_rational_str(char * value);

/**
   \brief DAG constructor
   \param value string
   \return Creates (if new) and returns DAG representing string value */
extern TDAG      DAG_new_str(char * value);

/** \brief Conveniency macro constructor for binary conjunctions */
#define DAG_and2(A, B) DAG_new_args(CONNECTOR_AND, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for equalities  */
#define DAG_eq(A, B) DAG_new_args(PREDICATE_EQ, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for equivalences */
#define DAG_equiv(A, B) DAG_new_args(CONNECTOR_EQUIV, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for equivalences */
#define DAG_implies(A, B) DAG_new_args(CONNECTOR_IMPLIES, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for negations */
#define DAG_not(A) DAG_new_args(CONNECTOR_NOT, A, DAG_NULL)

/** \brief Conveniency macro constructor for negations of equality */
#define DAG_neq(A, B) DAG_not(DAG_eq(A, B))

/** \brief Conveniency macro constructor for binary disjunctions */
#define DAG_or2(A, B) DAG_new_args(CONNECTOR_OR, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for ternary disjunctions */
#define DAG_or3(A, B, C) DAG_new_args(CONNECTOR_OR, A, B, C, DAG_NULL)

/** \brief Conveniency macro constructor for addition */
#define DAG_plus(A, B) DAG_new_args(FUNCTION_SUM, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for subtraction */
#define DAG_minus(A, B) DAG_new_args(FUNCTION_MINUS, A, B, DAG_NULL)

/** \brief Conveniency macro constructor for ite boolean terms */
#define DAG_ite(A, B, C) DAG_new_args(CONNECTOR_ITE, A, B, C, DAG_NULL)

extern TDAG      DAG_TRUE;  /*< \brief Represents the formula TRUE */
extern TDAG      DAG_FALSE; /*< \brief Represents the formula FALSE */
extern TDAG      DAG_ONE;  /*< \brief Represents the term ONE */
extern TDAG      DAG_ZERO; /*< \brief Represents the term ZERO */

/*
  --------------------------------------------------------------
  Specific recognizers
  --------------------------------------------------------------
*/

/**
   \brief Tests if DAG is a rational literal */
extern int       DAG_is_rational(TDAG DAG);

/**
   \brief Tests if DAG is an integer literal */
extern int       DAG_is_integer(TDAG DAG);

/**
   \brief Tests of DAG is a numeric literal */
extern int       DAG_is_number(TDAG DAG);

/**
   \brief Tests of DAG is a boolean atom */
extern int       DAG_is_atom(TDAG DAG);

/*
  --------------------------------------------------------------
  Fundamental data structure and handling functions
  --------------------------------------------------------------
*/

extern int DAG_identity(TDAG DAG1, TDAG DAG2);

/**
    \brief tests if DAG f is a literal.
    \param f a DAG
    \pre f is of sort SORT_BOOLEAN */
#define DAG_literal(f) ((f) && ( !boolean_connector(DAG_symb(f)) ||	\
				 (DAG_symb(f) == CONNECTOR_NOT &&	\
				  !boolean_connector(DAG_symb(DAG_arg0(f))))))

/**
   \brief Builds and returns an instance 

   \param DAG to be instantiated.

   \pre DAG must be a quantified formula. The Pflag attribute of the
   quantified variables shall be set to DAG of the instantiated term. */
extern TDAG      DAG_instantiate(TDAG DAG);

extern unsigned dp_mask_arith;

/** \brief TDAG version of generic functions, to instantiate data containers */
extern unsigned DAG_hash(TDAG DAG);
extern int      DAG_equal(TDAG DAG1, TDAG DAG2);
extern int      DAG_cmp(TDAG DAG1, TDAG DAG2);
extern int      DAG_cmp_q(TDAG *PDAG1, TDAG *PDAG2);

/*--------------------------------------------------------------*/

/**
   \brief gets the sorts and symbols in DAG
   \param DAG the DAG
   \param Psort address where the list of sorts is to be appended
   \param Psymb address where the list of symbols is to be appended
   \post  No sort or symbol is added twice
*/
extern void      DAG_logic_get(TDAG DAG, Tlist * Psort, Tlist * Psymb);

/**
   \brief gets the sorts and symbols in DAG
   \param list a list of DAGs
   \param Psort address where the list of sorts is to be appended
   \param Psymb address where the list of symbols is to be appended
   \post  No sort or symbol is added twice
*/
extern void      DAG_list_logic_get(Tlist list, Tlist * Psort, Tlist * Psymb);

/*
  --------------------------------------------------------------
  Initialisation-release functions
  --------------------------------------------------------------
*/

/**
   \brief Initializes veriT-DAG module.
   \remark Module options must have been initialized before veriT-DAG module */
extern void      DAG_init(void);

/**
   \brief Closes veriT-DAG module, frees all allocated data structures.
   \remark Module options must be closed after veriT-DAG module */
extern void      DAG_done(void);

typedef void (*TDAG_hook_resize) (unsigned old, unsigned new);
typedef void (*TDAG_hook_free) (TDAG);

/**
   \brief adds a function to be notified of the resizing of the DAG stack
   \param hook_resize the function to call at each resize
   \remark new size is given as argument of hook_resize
   \remark if used to allocate side information, hook_resize should be used
   to allocate and initialize this information */
extern void DAG_set_hook_resize(TDAG_hook_resize hook_resize);

/**
   \brief adds a function to be notified of the freeing of a DAG
   \param hook_free the function to call at each DAG free
   \remark DAG which is free given as argument of hook_free
   \remark use as reinitialization of side information linked with DAG */
extern void DAG_set_hook_free(TDAG_hook_free hook_free);

#endif /* __DAG_H */
