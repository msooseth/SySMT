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

#ifndef DAG_SORT_H
#define DAG_SORT_H

#include <stdarg.h>

#include "table.h"
#include "types.h"
#include "stack.h"

/*--------------------------------------------------------------*/

/**
   \brief Type for sorts of symbols and DAGs

   Facilities for disjoint sorts.
   A sort is either
   - scalar : This is just a name.
   - functional : sort_1 x ... sort_{n-1} -> sort_{n}, with n > 1.
   - n-ary : sort_1 x ... (arbitrary number of times) x sort_1 -> sort_2

   arity is respectively 0, n, DAG_SORT_NARY in those cases.

   Compound sorts are "non-scalar" sorts (either functional or n-ary).

   There may be aliases (i.e. names) to sorts (that is, even the
   compound ones).  An alias may be bound to only one sort.
   DAG_sort_new(_args) fails when using several times the same name.
   However, it will not fail when declaring the same sort twice,
   i.e. it fails only when declaring different sorts with the same
   name.

   Any compound sort should be defined uniquely .  That is two aliases
   should never refer to similar compound sorts.

   Notice that arity (for a functional sort) is not the number of arguments
   of the function having such a sort, but the number of arguments + 1
   since the domain is also taken into account. 

   Boolean sort is just as any other sort.  Predicates are thus a
   special kind of function.  

   \todo make sure functions, and quantifiers are ok with that sort */

typedef unsigned Tsort;

#define DAG_SORT_NULL ((Tsort) 0)

#define DAG_SORT_NARY ((unsigned)-1)

typedef struct TSsort
{
  char     *name; /*< sort name; optional (may be NULL), must be unique */
  unsigned arity; /*< number of arguments, (compound, polymorphic sorts),
		    DAG_SORT_NARY for a polyadic sort */
  Tsort    *sub;  /*< array of sub-sorts (compound, polymorphic sorts) */
  Ttable   variables;
  unsigned nbvariables;
  void *   binding;         /*< place-holder to attach pointer values */
#ifndef PEDANTIC
  unsigned mark : 1;        /*< marker for user-defined processing */
  unsigned predefined : 1;  /*< predefined sorts */
  unsigned variable : 1;    /*< sort variable */
  unsigned instance : 1;    /*< instances of sort constructors */
  unsigned parametric : 1;  /*< parametric sort constructors */
  unsigned polymorphic : 1; /*< polymorphic sorts */
#else
  unsigned mark;           /*< marker for user-defined processing */
  unsigned predefined;     /*< predefined sorts */
  unsigned variable;       /*< sort variable */
  unsigned instance;       /*< instances of sort constructors */
  unsigned parametric;     /*< parametric sort constructors */
  unsigned polymorphic;    /*< polymorphic sorts */
#endif
} TSsort;

TSstack(_Ssort, TSsort);

extern Tstack_Ssort DAG_sort_stack;

TSstack(_sort, Tsort);

#define __DAG_SORT_DATA(sort) (DAG_sort_stack->data[(Tsort) (sort)])

#define DAG_ptr_of_sort(sort) ((void *) (uintptr_t) (sort))

#define DAG_sort_of_ptr(P) ((Tsort) (uintptr_t) (P))

/*
  --------------------------------------------------------------
  Constructors
  --------------------------------------------------------------
*/

/**
   \brief old sort constructor
   \param name pointer to string naming the sort (may be NULL)
   \param arity number of sub-sorts in a compound sort; if arity is
   DAG_SORT_NARY, then symbol of this sort may have any number of
   arguments of sort sub[0], and returns argument of sort sub[1].
   \param sub array storing sub-sorts in compound sorts
   \return a new sort
   \remark Two sorts are equal if they have the same arity and sub-sorts
   - If an equal sort of the same name as already been created, it is
   returned.
   - If a different sort with the same name has already been created,
   it is an error.
   - If an equal sort with a different, not null, name has already been
   created, it is an error.
   - If an equal sort with a null name has already been created, its
   name is set to the given name and it is returned.
   \remark Destructive for sub 
   \remark Created sort is functional. Set functional field to 0 to change */
extern Tsort     DAG_sort_new(const char *name, unsigned arity, Tsort * sub);

/**
   \brief Sort constructor
   \param name pointer to string naming the sort (may be NULL)
   \param arity number of sub-sorts in a compound sort; if arity is
   DAG_SORT_NARY, then symbol of this sort may have any number of
   arguments of sort sub[0], and returns argument of sort sub[1].
   \param ... for compound sorts, sub-sorts are given as arguments,
   followed by NULL
   \return a new sort
   \remark just an interface for above function */
extern Tsort     DAG_sort_new_args(const char *name, unsigned arity, ...);

/**
   \brief creates a sort variable with the given name
   \param name
   \pre name must either be NULL or a valid string.
   \return It returns a sort variable:
   - when called with NULL, it generates a fresh sort variable,
   the name of this variable is '_ (single-quote underscore) followed
   by a positive integer.
   - when called with a string, it generates a sort variable of the
   given name.
   \remark If called twice with the same (non-NULL) string, then
   returns the same sort */
extern Tsort     DAG_sort_new_var(char * name);

/**
   \brief creates a parametric sort constructor
   \param name
   \param arity
   \remark If there is already a constructor of the same name and arity,
   then it is returned.
   \remark If name is NULL, an error is printed and execution halts.
   \remark If there is already a constructor of the same name and
   different arity, an error is printed to stderr and execution halts.
   \remark If arity is 0, then the result is DAG_sort_new_func(name, 0, NULL) */
extern Tsort     DAG_sort_new_param(char * name, unsigned arity);

/**
   \brief creates an instance of a parametric sort constructor
   \param the name of the resulting sort (optional: may be NULL)
   \param sort the parametric sort constructor
   \param arity the number of arguments
   \param sub the arguments
   \remark If there is already an instance of the constructor and
   arguments, then it is returned
   \remark Fails if arity != sort->arity */
extern Tsort     DAG_sort_new_inst(char * name, Tsort sort,
				   unsigned arity, Tsort * sub);

/*
  --------------------------------------------------------------
  Accessing sorts
  --------------------------------------------------------------
*/

/**
   \brief Gets sort with name
   \param name of the searched sort
   \return the sort named name, or NULL if not found */
extern Tsort     DAG_sort_lookup(const char *name);

/**
   \brief Accesses the name of the sort.
   \param sort
   \return a pointer to the name string of the sort, if declared and named,
   NULL otherwise */
#define DAG_sort_name(sort) (__DAG_SORT_DATA(sort).name)

/**
   \brief Accesses the arity of the sort.
   \param sort
   \return the arity of the sort */
#define DAG_sort_arity(sort) (__DAG_SORT_DATA(sort).arity)

/**
   \brief Accesses the i-th sub-sort of the sort.
   \param sort The accessed sort.
   \param i The accessed position.
   \pre i is a valid sub-sort position.
   \return compound sort i.
   This routine may be used to access the elements of a functional sort */
#define DAG_sort_sub(sort) (__DAG_SORT_DATA(sort).sub)

/**
   \brief Tests if sort is predefined
   \param sort */
#define DAG_sort_predefined(sort) (__DAG_SORT_DATA(sort).predefined == 1)

/**
   \brief Tests if sort is parametric
   \param sort the sort
   \remarks (List 1) is parametric, (List Int) and Int are not */
#define DAG_sort_parametric(sort) (__DAG_SORT_DATA(sort).parametric == 1)

/**
   \brief Tests if sort is polymorphic
   \param sort the sort */
#define DAG_sort_polymorphic(sort) (__DAG_SORT_DATA(sort).polymorphic == 1)

#define DAG_sort_nbvariables(sort) (__DAG_SORT_DATA(sort).nbvariables)

#define DAG_sort_variables(sort) (__DAG_SORT_DATA(sort).variables)

/**
   \brief Tests if sort is an instance of a parametric sort constructor
   \param sort */
#define DAG_sort_instance(sort) (__DAG_SORT_DATA(sort).instance == 1)

/**
   \brief tests if a sort is a sort variable
   \param sort The tested sort */
#define DAG_sort_variable(sort) (__DAG_SORT_DATA(sort).variable == 1)
extern int DAG_sort_variable_fn(Tsort);

/**
   \brief mark, i.e. sets the misc attribute, sort
   \param sort a sort */
extern void      DAG_sort_mark(Tsort sort);

/**
   \brief unmark, i.e. unsets the misc attribute, sort
   \param sort a sort */
extern void      DAG_sort_unmark(Tsort sort);

/**
   \brief checks if sort is marked
   \param sort a sort
   \return the value of the \a misc attribute */
extern int       DAG_sort_is_marked(Tsort sort);

/**
   \brief returns the pointer bound to sort
   \param sort a sort
*/
#define DAG_sort_binding(sort) (__DAG_SORT_DATA(sort).binding)

extern void  DAG_sort_bind(Tsort sort1, void * P);
extern void  DAG_sort_unbind(Tsort sort);

/**
   \brief recursively unbinds sort and sub-sorts
   \param sort a sort */
extern void  DAG_sort_unbind_rec(Tsort sort);

/**
   \brief Sets a sort as predefined */
#define   DAG_sort_set_predefined(S) (__DAG_SORT_DATA(S).predefined = 1)

/**
   \brief returns a compatible sort, if any
   \param sort1 a sort
   \param sort2 a sort
   \return The combination of two sorts \f$s_1\f$ and \f$s_2\f$ is defined as
   - <tt>Real</tt> when eiter either \f$s_1\f$ or \f$s_2\f is <tt>Integer</tt>
   and the other is <tt>Real</tt>,
   - <tt>sort1</tt> when they are equal,
   - NULL, otherwise.
   \todo Make the result of this test dependent on theory. */
extern Tsort DAG_sort_combine(Tsort, Tsort);

#ifdef DEBUG
extern int DAG_sort_invariant(Tsort sort);
#endif

/*
  --------------------------------------------------------------
  Module initialization and release
  --------------------------------------------------------------
*/

extern void DAG_sort_init(void);
extern void DAG_sort_done(void);

/*--------------------------------------------------------------*/

/** \brief Name of predefined boolean sort */
extern char * SORT_BOOLEAN_STR;
/** \brief Name of predefined integer sort */
extern char * SORT_INTEGER_STR;
/** \brief Name of predefined real/rational sort */
extern char * SORT_REAL_STR;
/** \brief Name of predefined sort for unintepreted values */
extern char * SORT_UNINTERPRETED_STR;
/** \brief Name of predefined array sort */
extern char * SORT_ARRAY_STR;
/** \brief Name of predefined (array) element sort */
extern char * SORT_ELEMENT_STR;
/** \brief Name of predefined (array) index sort */
extern char * SORT_INDEX_STR;

/** \brief Predefined boolean sort */
extern Tsort     SORT_BOOLEAN;
/** \brief Predefined integer sort */
extern Tsort     SORT_INTEGER;
/** \brief Predefined real/rational sort */
extern Tsort     SORT_REAL;

/*
  Rationale for adding the following two variables:

  In SMT-LIB2, a numeral constant may be either of sort Int or
  Real, depending on the logic used. The DAG library has routine
  to build the signature of a given logic. The parser calls this routine 
  and thus sets up to following variables to the correct sort. Later,
  when the reads a constant, it only needs to call the DAG library
  routine according to the syntactic nature (numeral/decimal) */

/** \brief Sort used to build NUMERAL constants (SMT-LIB2) */
extern Tsort     SORT_NUMERAL;
/** \brief Sort used to build DECIMAL constants (SMT-LIB2) */
extern Tsort     SORT_DECIMAL;

#endif /* DAG_SORT_H */


