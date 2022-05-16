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

#ifndef DAG_SYMB_H
#define DAG_SYMB_H

#include "DAG-sort.h"

/*
  --------------------------------------------------------------
  Symbol data structure
  --------------------------------------------------------------
*/

typedef unsigned Tsymb;
TSstack(_symb, Tsymb); /* typedefs Tstack_symb */

/*--------------------------------------------------------------*/

/**
   \brief Type for the different kinds of symbols
   \todo This is a mess */
typedef enum TEsymb_type {
  SYMB_UNKNOWN,    /*< Should never be */
  SYMB_PREDICATE,  /*< Identifies predicate symbols */
  SYMB_FUNCTION,   /*< Identifies function symbols */
  SYMB_VARIABLE,   /*< Quantified variables */
  SYMB_ITE_FUNC,   /*< ITE functor */
  SYMB_ITE,        /*< boolean-valued ITE */
  SYMB_QUANTIFIER, /*< Universal or existential quantifiers */
  SYMB_BOOLEAN,    /*< Boolean connectors */
  SYMB_BOOLEAN_CONSTANT,  /*< True or False */
  SYMB_INTEGER,    /*< Integer numeric values */
  SYMB_BINARY,     /*< Binary numeric values */
  SYMB_HEX,        /*< Hexadecimal numeric values */
  SYMB_RATIONAL,   /*< Rational numeric values */
  SYMB_STRING,     /*< string values */
  SYMB_LAMBDA,     /*< Lambda abstraction operator */
  SYMB_LET,        /*< Let operator */
  SYMB_APPLY,      /*< Application of a lambda expression (beta reduction) */
  SYMB_SKOLEM,     /*< Skolem constants */
  SYMB_MACRO,      /*< Macro symbols */
  SYMB_TYPE_NB     /*< Should never be.
		       Trick to known number of enumerators in Tsymb_type
                       at compile time */
} Tsymb_type;

/*--------------------------------------------------------------*/

#define DAG_SYMB_NULL ((Tsymb) 0)

/*--------------------------------------------------------------*/
/**
   \brief Structure to represent symbols of DAGs */
typedef struct TSsymb
{
  char     *name;            /*< symbol name; overloading is possible */
  unsigned  key;             /*< result of hash function */
  int       misc;            /*< placeholder for clients */
  void*     Pflag;           /*< placeholder for clients */
  Thash     hash;            /*< hash table with symbol as top symbol */
  Tsymb_type type;           /*< identifies the symbol kind */
  Tsort     sort;            /*< sort of the symbol */
  unsigned  dp_mask;         /*< mask of flags identifying decision procedures where symbol is handled */
  unsigned  interpreted : 1; /*< flags if symbol is interpreted */
  unsigned  predefined : 1;  /*< flags if symbol is predefined */
  /** s, if it is an instance of polymorphic symbol s, NULL otherwise */
  /* Tsymb     origin; */
} TSsymb;

TSstack(_Ssymb, TSsymb);
/** \brief stack of symbols, stored in a single chunk of memory */
extern Tstack_Ssymb DAG_symb_stack;

/*--------------------------------------------------------------*/

#define __DAG_SYMB_DATA(symb) (DAG_symb_stack->data[symb])

#define DAG_ptr_of_symb(symb) ((void *) (uintptr_t) (symb))
#define DAG_symb_of_ptr(P) ((Tsymb) (uintptr_t) (P))

/**
   \brief Accesses the name of the symbol
   \param symb
   \return The name of symb */
#define DAG_symb_name(symb) (__DAG_SYMB_DATA(symb).name)

/**
   \brief Accesses the kind of the symbol
   \param symb
   \return The kind of symb */
#define DAG_symb_type(symb) (__DAG_SYMB_DATA(symb).type)

/**
   \brief Accesses the sort of the symbol
   \param symb
   \return The kind of symb */
#define DAG_symb_sort(symb) (__DAG_SYMB_DATA(symb).sort)

/**
    \brief Associates a DAG to symbol
    \param symb
    \param DAG
    \remark This is useful for instantiations (think symb is a variable) */
/* #define DAG_symb_set_bind_DAG(symb,val)	(__DAG_SYMB_DATA(symb).DAG = val) */

/**
   \brief Gets DAG associated DAG to symbol
   \param symb
   \return DAG associated to symb 
   This is useful for instantiations (think symb is a variable) */
/* #define DAG_symb_get_bind_DAG(symb) (__DAG_SYMB_DATA(symb).DAG) */

/**
   \brief Marks symbol as being interpreted.
   \param symb a symbol
   \remark Macros need to be marked as interpreted symbols */
#define DAG_symb_set_interpreted(symb)		\
  (__DAG_SYMB_DATA(symb).interpreted = true)

/**
   \brief Tests if symbol is interpreted.
   \param symb a symbol
   \remark Macros are considered interpreted symbols */
#define DAG_symb_interpreted(symb) (__DAG_SYMB_DATA(symb).interpreted)

#define DAG_symb_hash(symb) (__DAG_SYMB_DATA(symb).hash)

#define DAG_symb_misc(symb) (__DAG_SYMB_DATA(symb).misc)

#define DAG_symb_set_misc(symb,v) (__DAG_SYMB_DATA(symb).misc = (v))

#define DAG_symb_reset_misc(symb) DAG_symb_set_misc(symb,0)

#define DAG_symb_set_predefined(symb) (__DAG_SYMB_DATA(symb).predefined = true)

#define DAG_symb_predefined(symb) (__DAG_SYMB_DATA(symb).predefined)

#define DAG_symb_Pflag(symb) (__DAG_SYMB_DATA(symb).Pflag)

/**
   \brief Sets the Pflag attribute of symb [deprecated].
   \note This assignment used to be provided as a macro, but this causes 
   an error whenever the lhs might change the address where symb is stored.
   The function call prevents this from happening as the assigned value is
   evaluated before the call, and the assignment occurs within the call */
extern void DAG_symb_set_Pflag(Tsymb symb, void * P);

#define DAG_symb_dp_mask(symb) (__DAG_SYMB_DATA(symb).dp_mask)

#define DAG_symb_key(symb) (__DAG_SYMB_DATA(symb).key)

/*
  --------------------------------------------------------------
  Initialisation-release functions
  --------------------------------------------------------------
*/

/**
   \brief Initializes DAG-symb module */
extern void DAG_symb_init(void);
/**
   \brief Closes DAG_symb module */
extern void DAG_symb_done(void);

typedef void (*TDAG_symb_hook_resize) (unsigned old, unsigned new);

/**
   \brief adds a function to be notified of the resizing of the symb stack
   \param hook_resize the function to call at each resize
   \remark new size is given as argument of hook_resize
   \remark if used to allocate side information, hook_resize should be used
   to allocate and initialize this information */
extern void DAG_symb_set_hook_resize(TDAG_symb_hook_resize hook_resize);

/*
  --------------------------------------------------------------
  Constructors
  --------------------------------------------------------------
*/

/**
   \brief Constructor
   \param name string naming the symbol
   \param type identifies the kind of symbols that needs to be created
   \param sort the symbol sort
   \return returns the declared symbol
   \note Declares a new symbol
   \note name is not freed in the call */
extern Tsymb     DAG_symb_new(const char *name, Tsymb_type type, Tsort sort);

/**
   \brief Gets symbol with given name and sort.
   \param name string naming the symbol
   \param sort the symbols sort
   \return A symbol <b>s1</b> of sort <b>sort1</b> is candidate for
   the result if <b>s1</b> subsumes <b>sort</b> and there is no other
   symbol <b>s2</b> of sort <b>sort2</b> such that <b>sort1</b>
   subsumes <b>sort2</b> and <b>sort2</b> subsumes <b>sort</b>.
   Returns NULL if there are 0 or several candidates, and the
   candidate symbol otherwise */
extern Tsymb     DAG_symb_lookup_sort(char *name, Tsort sort);

/**
   \brief Specialized constructor 
   \param sort sort of the symbol to create
   \return symbol of a fresh skolem symbol of the given sort */
extern Tsymb     DAG_symb_skolem(Tsort sort);

/**
   \brief Specialized constructor 
   \param sort sort of the symbol to create
   \return symbol of a fresh constant symbol of the given sort */
extern Tsymb     DAG_symb_const(Tsort sort);

/**
   \brief Specialized constructor
   \param sort sort of the symbol to create
   \return symbol of a fresh variable of the given sort */
extern Tsymb     DAG_symb_variable(Tsort sort);

/**
   \brief Specialized constructor 
   \param sort sort of the symbol to create
   \return symbol of a fresh function symbol of the given sort */
extern Tsymb     DAG_symb_function(Tsort sort);

/**
   \brief Specialized constructor 
   \param sort sort of the symbol to create
   \return symbol of a fresh predicate of the given sort */
extern Tsymb     DAG_symb_predicate(Tsort sort);

/**
   \brief tests if a symbol is a predicate symbol
   \param symb the tested symbol
   \return 1 if \c symb is a predicate symbol, 0 otherwise
   \note A symbol is a predicate symbol if its kind is 
   PREDICATE_SYMB or if it is FUNCTION_SYMB with Boolean range */
extern int       DAG_symb_is_predicate(Tsymb symb);



/**
   \brief Gets symbol with given name.
   \param name string naming the symbol
   \param nb_arg the number of subterms
   \param PDAG the array of nb_arg subterms (optional)
   \param sort the symbols sort (optional)
   \return Returns the appropriate Tsymb for name, if declared, or
   DAG_SYMB_NULL if zero or several symbols match.
   \remark PDAG and sort are used for taking the right symbol if name
   is overloaded */
extern Tsymb     DAG_symb_lookup(char *name, unsigned nb_arg,
				 Tsort * Psort, Tsort sort);


/*--------------------------------------------------------------*/

/**
   \brief returns sort of application of symb to arguments of sort
   Psort[0] ...Psort[n-1]
   \param symb the symbol
   \param n the number of arguments
   \param Psort the argument sorts
   \return DAG_SORT_NULL if it cannot be applied */
extern Tsort DAG_symb_check (Tsymb, unsigned, Tsort *);

extern Tsymb DAG_symb_integer(long value);
extern Tsymb DAG_symb_rational(long num, long den);
extern Tsymb DAG_symb_numeral_str(char * value);
extern Tsymb DAG_symb_decimal_str(char * value);
extern Tsymb DAG_symb_binary_str(char * value);
extern Tsymb DAG_symb_hex_str(char * value);
extern Tsymb DAG_symb_rational_str(char * value);
extern Tsymb DAG_symb_str(char * value);


#endif
