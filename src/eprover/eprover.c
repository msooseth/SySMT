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
   \file eprover.c

   This module is responsible for calling the E prover with
   clues that have been marked as relevant by Nelson and Oppen.
   
   The communication with E is file-based. The module produces a file
   containing clauses in TPTP3 format. E is then called with this
   file's contents as input. The result of E in TSTP format is
   redirected to another file. This TSTP output is then parsed to
   extract information that is queried by the module's client.

   Caveat: SMT is sorted and E only supports unsorted TPTP3 input. 

   If the current set of clues contains more than one non-Boolean
   sort, then the TPTP3 problem shall be printed with sort
   information. The output of E then includes sort information that is
   needed to construct correctly sorted SMT formulas. A large part of
   the code in this file is responsible from translating from veriT
   logic to and from E logic.

   The non-Boolean sorts occuring in the set of clues are stored
   in \a e_sort_list. The length of \a e_sort_list is used to test if
   sort information shall be printed.

   Also, since the (unsorted) output of E is parsed to TDAG, and
   TDAGs are sorted, the unsorted terms of the output needs to be
   cast in the sort system without overlapping the sorts of the SMT
   problem. To do this, a fresh sort \f$U\f$ is created when the module is
   initialized. It is stored in variable \c tptp_sort.

   The sort of the terms built from the TSTP output is stored in
   \a tptp_sort.

   If the problem is multi-sorted, the sort information is coded for
   the E prover using so-called "mapping functions".  For each SMT
   sort \f$s\f$, there exists a "sort mapping function" \f$f_s : U
   \rightarrow U\f$.  The variable \c symb_of_sort is a list of pairs
   where the key attribute is a sort \f$s\f$ and the value attribute
   is the symbol of the corresponding sort mapping function \f$f_s\f$.

   For each SMT symbol \f$f\f$ of arity \f$n$, there exists a "symbol
   mapping function" \f$f'\f$ also of arity \f$n\f$, but with
   arguments in \f$U\f$. The return sort is \f$U\f$ if \f$f\f$ is a
   function symbol and Boolean if \f$f\f$ is a predicate symbol.

   Variable \a symb_of_symb is a list of pairs where, either the key
   attribute is a symbol \f$f\f$ and the value attribute is the
   corresponding mapping symbol function \f$f'\f$, or the converse.

   Abstracted terms need also to be mapped to some term with the TPTP
   sort. Variable \a DAG_of_DAG is a list of pairs where the key is an
   abstracted term and the value is a fresh constant of the TPTP sort.

   When the inferences of the E prover are read, it is necessary to
   convert it to a formula using the corresponding SMT sorts and 
   symbols. Also the E prover creates new symbols on-the-fly, and
   corresponding symbols need to be created in the SMT logic. There
   are two such symbols: variables and skolem functions.
   --------------------------------------------------------------
*/

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "general.h"
#include "hash.h"
#include "itable.h"
#include "options.h"
#include "sys.h"
#include "table.h"
#include "set.h"

#include "clue.h"
#include "clue-print.h"
#include "congruence.h"
#include "global.h"
#include "recursion.h"
#include "simplify.h"
#include "veriT-signal.h"
#include "veriT-status.h"

#ifdef PROOF
#include "proof.h"
#endif

#include "eprover.h"
#include "eprover-int.h"
#include "tptp-logic.h"
#include "tstp.h"

#include "config.h"

#include "DAG.h"
#include "DAG-tmp.h"
#include "DAG-ptr.h"
#include "DAG-print.h"

#define MULTISORTED (list_length(e_sort_list) >= 2)

#define sort_of_ptr(s) DAG_sort_of_ptr(s)
#define ptr_of_sort(s) DAG_ptr_of_sort(s)
#define symb_of_ptr(s) DAG_symb_of_ptr(s)
#define ptr_of_symb(s) DAG_ptr_of_symb(s)
#define symb_Pflag(s) DAG_symb_Pflag(s)
#define symb_set_Pflag(s,v) DAG_symb_set_Pflag(s,v)
#define symb_misc(s) DAG_symb_misc(s)

typedef struct TDAG_ext {
  TDAG DAG;
  unsigned flag;
} TDAG_ext;

#define DAG_flag(D) (((TDAG_ext *) DAG_tmp)[D].flag)
#define DAG_DAG(D) (((TDAG_ext *) DAG_tmp)[D].DAG)

/*-----------------------------------------------------------------------*/
/*                               DD options                              */
/*-----------------------------------------------------------------------*/

/**
   \addtogroup arguments_user

   - --disable-e

   \brief disables E prover (default)
*/
static bool e_options_disable = true;

/**
   \addtogroup arguments_user

   - --enable-e

   \brief enables E prover (disabled by default)
*/
static bool e_options_enable = false;

/**
   \addtogroup arguments_developer

   - --trace-e

   \brief maintains exchanges with E prover in the file system
   (disabled by default)
*/
static bool e_options_traceable = false;

struct {
  char * dir;
  char * inp;
  char * out;
  char * err;
} e_filenames;

/*-----------------------------------------------------------------------*/
/*      Variables accessed by other files in the E prover module         */
/*-----------------------------------------------------------------------*/

Tderivation e_derivation;       /** last derivation produced by E prover */
Tlist       e_sort_list;        /** sorts of terms */

/*-----------------------------------------------------------------------*/
/*                          Local variables                              */
/*-----------------------------------------------------------------------*/

/** \brief the current number of clues pushed by the user */
static int e_level;

/** \brief table storing stacked clues */
static Ttable e_clues_table;

/* DD+PF current decidability status of E prover */
static Tstatus status;

/* DD lemmas already generated (and need not be repeated) */
static Thash e_lemmas_hash;

/* DD lemmas generated but not consumed */
static Ttable e_new_lemmas_table;

/* DD+PF variable equalities derived by the decision procedure */
static Ttable e_var_eq_table; 

/* DD recalls the size of the clue stack when e_solve was called the last time */
static uintptr_t e_solve_point;

/** identifies the decision procedure in the combination schema */
static uintptr_t e_id;

/*-----------------------------------------------------------------------*/

static Tlist e_clue_premisses (const uintptr_t);

/*-----------------------------------------------------------------------*/
/*                            History stuff: declarations                */
/*-----------------------------------------------------------------------*/

/* DD records that a clue has been stored */
static void history_clue_store (void);
/* DC records a equality clue found */
static void history_equality_found (Tclue clue);
/* DD records that the logic is now multisorted */
static void history_sort_add (Tsort sort);
/* DD records that a sort has been set */
static void history_sort_set (Tsort sort);
/* DD records current status before assigning it a new value */
static void history_status_change ();
/* revert events recorded up to level */
static void history_backtrack (unsigned level);
/* DD empties history */
static void history_reset (void);
/* DD frees memory used to record history */
static void history_free (void);
#ifdef DEBUG_E
/* DD displays history to stdout */
static void history_print (void);
#endif

static int  DAG_symb_arity(Tsymb symb);

/*--------------------------------------------------------------------------*/
/*                                Other stuff                               */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/

void 
e_set_status (const Tstatus s)
{
  if (status != s)
    {
      history_status_change ();
      status = s;
    }
}

/*--------------------------------------------------------------------------*/
/*                     SMT to TPTP: sort stuff                              */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/

/**
   The routines hereafter are responsible for updating the list of
   sorts appearing in the clues given to the module. This list is
   stored in Variable \a e_sort_list.
*/


/**
   \brief adds new sorts to e_sort_list
   \param DAG a DAG
   \note  Appends to e_sort_list the sorts in DAG that are
   not already in there. Uses the misc attribute of Tsort
   records.
*/
static void
e_sort_check_DAG (TDAG DAG)
{
  int i;
  Tsort sort = DAG_sort(DAG);

  if (sort != SORT_BOOLEAN && !DAG_sort_is_marked(sort))
    {
      history_sort_add(sort);
      e_sort_list = list_add(e_sort_list, ptr_of_sort(sort));
      history_sort_set(tptp_sort);
      if (MULTISORTED)
	tptp_logic_set_sort(DAG_SORT_NULL);
      else 
	tptp_logic_set_sort(sort_of_ptr(list_car(e_sort_list)));
      DAG_sort_mark(sort);
    }
  for (i = 0; i < DAG_arity(DAG); ++i)
    e_sort_check_DAG (DAG_arg(DAG, i));
}

/*--------------------------------------------------------------------------*/
/**
   \brief adds new sorts to e_sort_list
   \param clue a clue
   \note  appends to e_sort_list the sorts in clue that are
   not already in there.
   \note uses the misc flag of Tsort records.
*/
static void
e_sort_check_clue (Tclue clue)
{
  assert (clue != NULL);
  LIST_LOOP_BEGIN(e_sort_list, void *, P);
  Tsort sort = sort_of_ptr(P);
  DAG_sort_mark(sort);
  LIST_LOOP_END(e_sort_list);
  switch (clue->type)
    {
    case CLUE_ABSTRACT_QUANT: 
    case CLUE_ABSTRACT_PRED: 
    case CLUE_ABSTRACT_TERM: 
      e_sort_check_DAG(clue->DAG[0]);
      break;
    case CLUE_INEQUALITY:
    case CLUE_MERGE: 
      e_sort_check_DAG(clue->DAG[0]);
      e_sort_check_DAG(clue->DAG[1]);
      break;
    default: 
      my_error ("e_sort_check_clue\n");
    }
  LIST_LOOP_BEGIN(e_sort_list, void *, P);
  Tsort sort = sort_of_ptr(P);
  DAG_sort_unmark(sort);
  LIST_LOOP_END(e_sort_list);
}

/*--------------------------------------------------------------*/
static Tstack_sort collect_sort;
static Tstack_symb collect_symb;

/*--------------------------------------------------------------*/

static void 
collect_sorts_node (Tsort sort)
{
  int i;
  if (DAG_sort_variable(sort) || DAG_sort_parametric(sort))
    return;
  if (DAG_sort_is_marked(sort))
    return;
  DAG_sort_mark(sort);
  if (DAG_sort_arity(sort) == DAG_SORT_NARY)
    {
      collect_sorts_node(DAG_sort_sub(sort)[0]);
      collect_sorts_node(DAG_sort_sub(sort)[1]);
    }
  else if (!DAG_sort_instance(sort) && DAG_sort_arity(sort) > 0)
    for (i = 0; i < DAG_sort_arity(sort); ++i)
      collect_sorts_node(DAG_sort_sub(sort)[i]);
  else 
    stack_push(collect_sort, sort);
}

/*--------------------------------------------------------------*/

static void
collect_logic_DAG_node(TDAG src)
{
  Tsymb symb = DAG_symb(src);
  if (DAG_symb_type(symb) == SYMB_QUANTIFIER ||
      DAG_symb_type(symb) == SYMB_BOOLEAN ||
      DAG_symb_type(symb) == SYMB_BOOLEAN_CONSTANT ||
      symb == PREDICATE_EQ ||
      symb_misc(symb) || 
      symb_Pflag(symb))
    return;
  collect_sorts_node(DAG_symb_sort(symb));
  if (DAG_symb_type(symb) != SYMB_VARIABLE)
    {
      stack_push(collect_symb, symb);
      DAG_symb_set_misc(symb, 1);
    }
}

/*--------------------------------------------------------------*/

static void
collect_logic_DAG(TDAG src)
{
  structural_recursion_void(src, collect_logic_DAG_node);
}

/*--------------------------------------------------------------*/

void      
collect_logic(Tlist list)
{
  unsigned i;
  list_apply(list, (TFapply) collect_logic_DAG);

  for (i = 0; i < collect_sort->size; i++)
    DAG_sort_unmark(collect_sort->data[i]);

  for (i = 0; i < collect_symb->size; i++)
    DAG_symb_reset_misc(collect_symb->data[i]);
}

/*--------------------------------------------------------------------------*/
/*                          SMT to TPTP: symbols map                        */
/*--------------------------------------------------------------------------*/

/** \brief List of pairs sort, symbol */
static Tlist    symb_of_sort;
/** \brief List of pairs symbol, symbol */
static Tlist    symb_of_symb;
/** \brief List of pairs abstract term, constant */
static Tlist    DAG_of_DAG;

typedef struct TSDAG_pair {
  TDAG key;
  TDAG value;
} * TDAG_pair;

typedef struct TSsort_symb
{
  Tsort sort;
  Tsymb symb;
} * Tsort_symb;

typedef struct TSsymb_symb
{
  Tsort symb1;
  Tsymb symb2;
} * Tsymb_symb;

/*--------------------------------------------------------------------------*/

/**
   \brief Sets Pflag of key DAG to value DAG
   \param assoc a pair of DAGs
*/
static void
bind_key_DAG(TDAG_pair assoc)
{
  DAG_DAG(assoc->key) =  assoc->value;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Unsets Pflag of key DAG
   \param assoc a pair of DAGs
*/
static void
unbind_key_DAG(TDAG_pair assoc)
{
  DAG_DAG(assoc->key) = DAG_NULL;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Sets Pflag of value DAG to key DAG
   \param assoc a pair of DAGs
*/
static void
bind_value_DAG(TDAG_pair assoc)
{
  DAG_DAG(assoc->value) = assoc->key;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Unsets Pflag of value DAG
   \param assoc a pair of DAGs
*/
static void
unbind_value_DAG(TDAG_pair assoc)
{
  DAG_DAG(assoc->value) = DAG_NULL;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Binds key with symbol.
   \param assoc a pair where the key is a sort, and the value a symbol
   \post The binding attribute of the sort is the symbol, and the Pflag
   attribute of the symbol is the sort.
*/
static void
bind_sort_symb(Tsort_symb assoc)
{
  DAG_sort_bind(assoc->sort, DAG_ptr_of(assoc->symb));
  DAG_symb_set_Pflag(assoc->symb, DAG_ptr_of(assoc->sort));
}

/*--------------------------------------------------------------------------*/

/**
   \brief Binds key with symbol.
   \param assoc a pair where the key is a sort, and the value a symbol
   \pre The binding attribute of the sort is the symbol, and the Pflag
   attribute of the symbol is the sort.
   \post The sort's \a binding attribute and the symbol's \a Pflag 
   attribute are set to \a NULL.
*/
static void
unbind_sort_symb(Tsort_symb assoc)
{
  DAG_sort_unbind(assoc->sort);
  DAG_symb_set_Pflag(assoc->symb, NULL);
}

/*--------------------------------------------------------------------------*/

/**
   \brief Binds two symbols.
   \param assoc a pair where the key and the value are symbols.
   \post The Pflag attribute of each symbol is the other symbol.
*/
static void
bind_symb_symb (Tsymb_symb assoc)
{
  symb_set_Pflag(assoc->symb1, DAG_ptr_of(assoc->symb2));
  symb_set_Pflag(assoc->symb2, DAG_ptr_of(assoc->symb1));
}

/*--------------------------------------------------------------------------*/

/**
   \brief Unbinds two symbols.
   \param assoc a pair where the key and the value are symbols.
   \pre The Pflag attribute of each symbol is the other symbol.
   \post The Pflag attribute of each symbol is set to \a NULL.
*/
static void
unbind_symb_symb (Tsymb_symb assoc)
{
  symb_set_Pflag(assoc->symb1, NULL);
  symb_set_Pflag(assoc->symb2, NULL);
}

/*
  --------------------------------------------------------------------------
  SMT to TPTP: abstraction of ground terms
  --------------------------------------------------------------------------
*/

/**
   \brief Abstracts a DAG and registers the abstraction in \a DAG_of_DAG.
   \param DAG a DAG
   \note A constant symbol of the sort for TPTP terms is created and
   a pair with \a DAG as key and that constant as value is added to
   the list \a DAG_of_DAG.
*/
static void 
abstract_DAG(TDAG DAG)
{
  TDAG DAG0 = DAG_new(tptp_logic_const(), 0, NULL);
  TDAG_pair assoc;
  MY_MALLOC(assoc, sizeof(struct TSDAG_pair));
  assoc->key = DAG;
  assoc->value = DAG_dup(DAG0);
  DAG_of_DAG = list_add(DAG_of_DAG, assoc);
}

/*--------------------------------------------------------------------------*/

static void 
abstract_DAG_shallow(TDAG DAG)
{
  unsigned i;
  if (DAG_flag(DAG))
    return;
  DAG_flag(DAG) = 1;
  for (i = 0; i < DAG_arity(DAG); ++i)
    abstract_DAG(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------------------*/

static void 
abstract_DAG_deep(TDAG DAG)
{
  if (DAG_flag(DAG))
    return;
  DAG_flag(DAG) = 1;
  if (DAG_ground(DAG) && !DAG_quant(DAG) && DAG_sort(DAG) != SORT_BOOLEAN)
    abstract_DAG(DAG);
  else
    {
      int i;
      for (i = 0; i < DAG_arity(DAG); ++i)
	abstract_DAG_deep(DAG_arg(DAG, i));
    }
}

/*--------------------------------------------------------------------------*/

static void
abstract_DAG_formula(TDAG DAG)
{
  if (DAG_flag(DAG))
    return;
  DAG_flag(DAG) = 1;
  if (DAG_symb_type(DAG_symb(DAG)) == SYMB_QUANTIFIER)
    abstract_DAG_formula(DAG_argn(DAG));
  else if (DAG_arity(DAG) == 0)
    return;
  else if (DAG_sort(DAG_arg0(DAG)) == SORT_BOOLEAN)
    {
      int i;
      for (i = 0; i < DAG_arity(DAG); ++i)
	abstract_DAG_formula(DAG_arg(DAG, i));
    }
  else /* DAG is an atom */
    {
      int i;
      for (i = 0; i < DAG_arity(DAG); ++i)
	abstract_DAG_deep(DAG_arg(DAG, i));
    }
}

/*--------------------------------------------------------------------------*/

static void
clue_abstract_DAG(Tclue clue)
{
  if (clue->type == CLUE_ABSTRACT_QUANT)
    abstract_DAG_formula(clue->DAG[0]);
  else if (clue->type == CLUE_ABSTRACT_PRED)
      abstract_DAG_shallow(clue->DAG[0]);
  else if (clue->type == CLUE_ABSTRACT_TERM)
    {
      abstract_DAG(clue->DAG[1]);
      abstract_DAG_shallow(clue->DAG[0]);
    }
  else if (clue->type == CLUE_MERGE)
    {
      abstract_DAG(clue->DAG[0]);
      abstract_DAG(clue->DAG[1]);
    }
}

/*--------------------------------------------------------------------------*/

static void
DAG_flag_reset(TDAG DAG)
{
  unsigned i;
  if (!DAG_flag(DAG))
    return;
  DAG_flag(DAG) = 0;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_flag_reset(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------------------*/

static void
DAG_DAG_reset(TDAG DAG)
{
  unsigned i;
  if (!DAG_DAG(DAG))
    return;
  DAG_DAG(DAG) = DAG_NULL;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_DAG_reset(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------------------*/

/**
   \brief Resets the flag attributes of DAGs in clue
   \param clue the clue
*/
static void
clue_reset_DAG(Tclue clue)
{
  if (clue->type == CLUE_ABSTRACT_QUANT)
    DAG_flag_reset(clue->DAG[0]);
  else if (clue->type == CLUE_ABSTRACT_PRED)
    DAG_flag_reset(clue->DAG[0]);
  else if (clue->type == CLUE_ABSTRACT_TERM)
    {
      DAG_flag_reset(clue->DAG[1]);
      DAG_flag_reset(clue->DAG[0]);
    }
  else if (clue->type == CLUE_MERGE)
    {
      DAG_flag_reset(clue->DAG[0]);
      DAG_flag_reset(clue->DAG[1]);
    }
}

/*
  --------------------------------------------------------------------------
  Processing E inferences
  --------------------------------------------------------------------------
*/

/**
   The following routines are responsible for translating inferences
   from the E prover into formulas in the logic handled by veriT. 
   
   The symbols in the E inferences are:
   1) variable symbols: they are mapped to variable symbols of the
   correct sort.
   2) sort function symbols: they are unary symbols that are used to
   infer the sort of other symbols.
   3) skolem symbols: they are mapped to Skolem symbols of the correct
   sort.
   4) other function symbols: they are mapped to function symbols of the
   correct sort
   5) predicate symbols: they are mapped to predicate symbols of the
   correct sort.

   2), 4) and 5) are recorded in association lists \a symb_of_symb and
   \a symb_of_sort. 1) and 3) are fresh symbols created by E and the
   corresponding veriT symbols need to be computed. The scope of 1) is
   inference and needs to be cleaned up after translating each
   inference.  The scope of 3) is a full derivation and needs to be 
   cleaned up after processing all inferences.

 */

static Tlist var_symb_list;     /** bound variable symbols */
static Tlist skl_symb_list;     /** skolem symbols created by E */
static Tlist epr_symb_list;     /** predicate symbols created by E */
/*--------------------------------------------------------------------------*/

/**
   \brief tests if an E symbol is a sort function symbol
*/
static int
sort_fun_check (Tsymb symb)
{
  return symb_misc(symb) == TPTP_SYMB_SORT;
}

/*--------------------------------------------------------------------------*/

/**
   \brief returns the sort associated to a sort function symbol
   \param symb a symbol
   \pre \a symb is a sort function symbol
*/
static Tsort
sort_fun_sort (Tsymb symb)
{
  return sort_of_ptr(symb_Pflag(symb));
}

/*--------------------------------------------------------------------------*/

/**
   \brief Builds the sort of a symbol generated in E
   \param DAG A DAG that has the symbol as root.
   \param sort The result sort of the symbol.
   \pre The root of \a DAG is a symbol generated by E (skolem or 
   predicate definition).
*/
static Tsort
infer_symb_sort (TDAG DAG, Tsort sort)
{
  int i, arity;
  Tsort *sub;
  arity = DAG_arity(DAG);
  if (arity > 0)
    {
      MY_MALLOC(sub, (1+arity)*sizeof(Tsort));
      for (i = 0; i < arity; ++i)
	{
	  Tsymb symb = DAG_symb(DAG_arg(DAG, i));
	  assert(DAG_symb_type(symb) == SYMB_VARIABLE);
	  sub[i] = DAG_symb_sort(symb_of_ptr(symb_Pflag(symb)));
	}
      sub[i] = sort;
      return DAG_sort_new(NULL, 1+arity, sub);
    }
  else
    return sort;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Auxiliary routine used in recursive traversal of inference
   to infer the sort of E variable symbols
*/
static void
infer_variable_sort (TDAG DAG)
{
  Tsymb symb = DAG_symb(DAG);
  /* if the head symbol is a sort function and its argument is a
     variable, then the sort of the corresponding variable is that 
     of the sort function */
  if (sort_fun_check(symb))
    {
      TDAG DAG0;
      assert(DAG_arity(DAG) == 1);
      DAG0 = DAG_arg0(DAG);
      if (DAG_symb_type(DAG_symb(DAG0)) == SYMB_VARIABLE &&
	  symb_Pflag(DAG_symb(DAG0)) == NULL)
	{
	  DAG_symb_set_Pflag(DAG_symb(DAG0),
			     ptr_of_symb(DAG_symb_variable(sort_fun_sort(symb))));
	  var_symb_list = list_add(var_symb_list, ptr_of_symb(DAG_symb(DAG0)));
	}
    }
  else if (symb_Pflag(symb) != NULL)
    {
      int   i;
      symb = symb_of_ptr(symb_Pflag(symb));
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  TDAG DAG0 = DAG_arg(DAG, i);
	  Tsymb symb0 = DAG_symb(DAG0);
	  if (DAG_symb_type(symb0) == SYMB_VARIABLE && symb_Pflag(symb0) == NULL)
	    {
	      DAG_symb_set_Pflag(symb0,
				 ptr_of_symb(DAG_symb_variable(DAG_sort_sub(DAG_symb_sort(symb))[i])));
	      var_symb_list = list_add(var_symb_list, 
				       ptr_of_symb(symb0));
	    }
	}
    }
}

/*--------------------------------------------------------------------------*/

/**
   \brief Auxiliary routine used in recursive traversal of inference
   to infer the sort of E predicate symbols
   \param DAG a DAG
   \note If \a DAG_symb(DAG) is a predicate symbol created in the derivation
   \a DAG_symb_Pflag(DAG_symb(DAG)) is used to store the multi-sorted symbol
   corresponding to \a DAG_symb(DAG).
*/
static void
infer_epred_sort (TDAG DAG)
{
  if (symb_misc(DAG_symb(DAG)) == TPTP_SYMB_PREDICATE)
    {
      assert(DAG_symb_type(DAG_symb(DAG)) == SYMB_PREDICATE);
      if (DAG_symb_Pflag(DAG_symb(DAG)))
	{
	  DAG_symb_set_Pflag(DAG_symb(DAG),
			     ptr_of_symb(DAG_symb_predicate(infer_symb_sort(DAG, SORT_BOOLEAN))));
	  epr_symb_list = list_add(epr_symb_list, 
				   ptr_of_symb(DAG_symb(DAG)));
	}
    }
}

/*--------------------------------------------------------------------------*/

/**
   \brief Auxiliary routine used in recursive traversal of inference
   to infer the sort of E skolem symbols
*/
static void
infer_skolem_sort (TDAG DAG)
{
  /* if the head symbol is a sort function and its argument is a
     skolem symbol, then the sort of the corresponding variable is
     that of the sort function */
  if (sort_fun_check(DAG_symb(DAG)))
    {
      TDAG DAG0;
      Tsymb symb, symb0;
      assert(DAG_arity(DAG) == 1);
      DAG0 = DAG_arg0(DAG);
      symb = DAG_symb(DAG);
      symb0 = DAG_symb(DAG0);
      if (symb_misc(symb0) == TPTP_SYMB_SKOLEM)
	{
	  assert (DAG_symb_type(symb0) == SYMB_SKOLEM);
	  if (symb_Pflag(symb0) == NULL)
	    {
	      DAG_symb_set_Pflag(symb0,
				 ptr_of_symb(DAG_symb_skolem(infer_symb_sort(DAG0, sort_fun_sort(symb)))));
	      skl_symb_list = list_add(skl_symb_list, ptr_of_symb(symb0));
	    }
	}
    }
}

/*--------------------------------------------------------------------------*/

static void
DAG_with_sort(TDAG DAG)
{
  if (DAG_DAG(DAG))
    return;
  if (sort_fun_check(DAG_symb(DAG)))
    {
      DAG_with_sort(DAG_arg0(DAG));
      DAG_DAG(DAG) = DAG_DAG(DAG_arg0(DAG));
    }
  else 
    {
      int i;
      TDAG *PDAG;
      TDAG tmp;
      MY_MALLOC(PDAG, DAG_arity(DAG) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  DAG_with_sort(DAG_arg(DAG, i));
	  PDAG[i] = DAG_DAG(DAG_arg(DAG, i));
	}
      tmp = DAG_new(symb_Pflag(DAG_symb(DAG))?
		    symb_of_ptr(symb_Pflag(DAG_symb(DAG))):DAG_symb(DAG),
		    DAG_arity(DAG), PDAG);
      DAG_DAG(DAG) = tmp;
    }
}

/*--------------------------------------------------------------------------*/

static int check_symbols_free_aux (TDAG DAG)
{
  return symb_misc(DAG_symb(DAG)) == 0;
}

/*--------------------------------------------------------------------------*/

static int check_symbols_free_DAG (TDAG DAG)
{
  return structural_recursion_pred(DAG, check_symbols_free_aux);
}

/*--------------------------------------------------------------------------*/

/**
   \brief Translates an inference from E logic to veriT logic.
   \pre All sort function symbols are bound to the corresponding
   sort (DAG_symb_Pflag(symb) == sort)
   \pre TSTP function symbols are bound to the corresponding E
   function symbol.
   \pre Some E-generated symbols may be bound to a veriT symbol
   \post All E-generated symbols occuring in \a DAG are bound to a
   veriT symbol.
*/
static TDAG
process_inference(TDAG DAG)
{
  TDAG result;
  assert (var_symb_list == NULL);
  /* Find the sort of quantified variables: for each TSTP variable
     create a variable symbol of adequate sort. */
  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_symb_set_misc(assoc->symb, TPTP_SYMB_SORT);
  LIST_LOOP_END(symb_of_sort);
  list_apply(symb_of_sort, (TFapply) bind_sort_symb);
  list_apply(symb_of_symb, (TFapply) bind_symb_symb);
  structural_recursion_void(DAG, (void (*) (TDAG)) infer_variable_sort);
  /* Find the sort of predicate symbols generated by E . */
  structural_recursion_void(DAG, (void (*) (TDAG)) infer_epred_sort);
  /* Find the sort of Skolem symbols: for each TSTP skolem symbol,
     create a skolem symbol of adequate sort. */
  structural_recursion_void(DAG, (void (*) (TDAG)) infer_skolem_sort);

  list_apply(symb_of_sort, (TFapply) unbind_sort_symb);
  /* Translate to sorted DAGs */
  list_apply(DAG_of_DAG, (TFapply) bind_value_DAG);
  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_symb_set_Pflag(assoc->symb, ptr_of_sort(assoc->sort));
  LIST_LOOP_END(symb_of_sort);
  DAG_with_sort(DAG);
  result = DAG_dup(DAG_DAG(DAG));
  DAG_DAG_reset(DAG);

  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_symb_set_Pflag(assoc->symb, NULL);
  LIST_LOOP_END(symb_of_sort);
  list_apply(DAG_of_DAG, (TFapply) unbind_value_DAG);
  list_apply(symb_of_symb, (TFapply) unbind_symb_symb);
  while (var_symb_list)
    {
      Tsymb symb = symb_of_ptr(list_car(var_symb_list));
      DAG_symb_set_Pflag(symb, NULL);
      var_symb_list = list_remove(var_symb_list);
    }
  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_symb_reset_misc(assoc->symb);
  LIST_LOOP_END(symb_of_sort);
  return result;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Processes the TPTP derivation into veriT logic
   \param derivation The derivation produced by E
   \note  If the problem is multi-sorted, alters the DAGs in the inferences 
   stored in \a derivation DAGs, sets ignore flag for inferences that include
   Skolem symbols created in the derivation.
   \note Some inference rules of the E prover create new symbols. These are:
   variables, skolem symbols, and defined predicate symbols. If the client 
   logic is multi-sorted, this routine is responsible for creating fresh
   symbols in that multi-sorted logic for each symbol generated by the E 
   prover. Note that the scope of variable symbols is the inference it
   appears in, while the scope of skolem and defined predicate symbols is
   the full derivation.
*/
static void
process_derivation(Tderivation deriv)
{
  int i;
  /* marks all definition and skolem symbols generated in the derivation */
  tptp_mark_symbols();
  /* set the ignore attribute all inferences where such symbols may occur */
  for (i = 0; i < table_length(deriv->steps); ++i) 
    {
      Tinference inference = (Tinference) table_get(deriv->steps, i);
      inference->ignore = !check_symbols_free_DAG(inference->DAG);
    }
  if (MULTISORTED) /* multi-sorted client logic */
    {
      assert(skl_symb_list == NULL);
      assert(epr_symb_list == NULL);
      /* skip axioms */
      for (i = deriv->nb_axioms+1; i < table_length(deriv->steps); ++i)
	{
	  Tinference inference;
	  TDAG DAG;
	  inference = (Tinference) table_get(deriv->steps, i);
	  DAG = process_inference(inference->DAG);
	  DAG_free(inference->DAG);
	  inference->DAG = DAG;
	}
      while (skl_symb_list)
	{
	  Tsymb symb = symb_of_ptr(list_car(skl_symb_list));
	  DAG_symb_set_Pflag(symb, NULL);
	  skl_symb_list = list_remove(skl_symb_list);
	}
      while (epr_symb_list)
	{
	  Tsymb symb = symb_of_ptr(list_car(epr_symb_list));
	  DAG_symb_set_Pflag(symb, NULL);
	  epr_symb_list = list_remove(epr_symb_list);
	}
      tptp_unmark_symbols();
    }
  tptp_unmark_symbols();
}

/*--------------------------------------------------------------------------*/
/*                       Communication with E                   */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/

/**
   \brief Tests availability of the E prover binary.  
   \return 1 if found, 0 otherwise.
   \note assumes that the host system has a command processor
   able to interpret the following command:
   <tt>eprover > /dev/null 2>&1</tt>.
*/
static int
e_binary_test (void)
{
  /* DD flags if we have tested the E prover is installed (and in the path) */
  static int tested = 0;
  /* DD flags if the E prover is installed (and in the path) */
  static int found = 0;

  if (tested) return found;

  tested = 1;
  if (system("eprover --version > /dev/null 2>&1"))
    {
      my_message("Cannot find eprover.\n");
      my_message("For optimal results, download and install eprover in your PATH.\n");
      my_message("Repository: http://www.eprover.org\n");
      e_set_status (UNDEF);
      found = 0;
    }
  else
    {
      found = 1;
    }
  return found;
}

/*--------------------------------------------------------------------------*/

static void 
e_filenames_new(void)
{
  size_t sz;
  static long id = 0;
	    
  if (e_filenames.dir == NULL)
    e_filenames.dir = sys_create_directory ();
  sz = strlen(e_filenames.dir) + 1 + l_str_size(id) + strlen("prover.in.") + 1;
  MY_MALLOC(e_filenames.inp, sizeof(char) * sz);
  MY_MALLOC(e_filenames.out, sizeof(char) * sz);
  MY_MALLOC(e_filenames.err, sizeof(char) * sz);

  sprintf(e_filenames.inp, "%s/prover.in.%li", e_filenames.dir, id);
  sprintf(e_filenames.out, "%s/prover.ou.%li", e_filenames.dir, id);
  sprintf(e_filenames.err, "%s/prover.st.%li", e_filenames.dir, id);

  id += 1;
}

/*--------------------------------------------------------------------------*/

static void 
e_filenames_delete(void)
{
  free(e_filenames.inp);
  e_filenames.inp = NULL;
  free(e_filenames.out);
  e_filenames.out = NULL;
  free(e_filenames.err);
  e_filenames.err = NULL;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Computes an upper limit for the E prover
   \param clues The table of clues that will be given to E
   \return Returns a positive number that is used to set an 
   upper limit on the number of clauses the E prover processes.
   This number depends on the number and the size of the 
   stacked clues.
   \note The returned value is purely heuristic but no smaller
   than 500.
*/
static unsigned long
processed_clause_limit (Ttable clauses)
{
  unsigned long result;
  int i;
  result = 0;
  for (i = 0; i < table_length (clauses); ++i)
    {
      unsigned long size = clue_DAG_size ((Tclue) table_get (clauses, i));
      if (result < size) result = size;
    }
  result *= table_length(e_clues_table);
  if (result < 500) result = 500;
  return result;
}

/*--------------------------------------------------------------------------*/

/**
   \brief Generate a command string for E
   \param limit an upper limit for E
   \return A command string for E to process a file \a name_in, with
   standard output and error streams directed to files \a name_out and
   \a name_err, respectively, such that the number of clauses processed by E
   shall not exceed \a limit:
   <tt>eprover -l 4 --tstp-format 
   --definitional-cnf=0 -xAuto -tAuto --processed-clauses-limit=limit
   name_in 1> name_out 2> name_err </tt>
*/
static char * 
e_generate_command(unsigned long limit)
{
  const char COMMAND_PREFIX_STR [] = "eprover --definitional-cnf=0 -l 4 --tstp-format -xAuto -tAuto";
  char * result;
  size_t length;
  char * limit_str;

  MY_MALLOC(limit_str, (1 + ul_str_size(limit)) * sizeof(char));
  sprintf (limit_str, "%lu", limit);
  result = NULL, length = 0;
  result = strapp(result, &length, COMMAND_PREFIX_STR);
  result = strapp(result, &length, " --processed-clauses-limit=");
  result = strapp(result, &length, limit_str);
  free (limit_str);
#ifdef OPTION_CHECK_TIME
  if (option_max_time > 0)
    {
      char * option_max_time_str;
      MY_MALLOC (option_max_time_str, (1 + ul_str_size ((unsigned long) option_max_time)) * sizeof(char));
      sprintf (option_max_time_str, "%i", option_max_time);
      result = strapp (result, &length, " --soft-cpu-limit=");
      result = strapp(result, &length, option_max_time_str);
      free (option_max_time_str);
    }
#endif
  result = strapp(result, &length, " ");
  result = strapp(result, &length, e_filenames.inp);
  result = strapp(result, &length, " 1> ");
  result = strapp(result, &length, e_filenames.out);
  result = strapp(result, &length, " 2> ");
  result = strapp(result, &length, e_filenames.err);

  return result;
}

/*--------------------------------------------------------------------------*/

/**
   \brief  Updates symb_of_sort and symb_of_symb with symbols and sorts
   found in clues
   \param list A list of DAGs
   \post  The mapping of sorts and symbols is registered in lists
   symb_of_sort and symb_of_symb
   \author David Deharbe
 */

static void
e_pre_input(Ttable e_clues_table)
{
  Tlist DAGs;
  int   i;
  unsigned j;

  if (!MULTISORTED)
    return;

  /* store in DAGs all the terms that are to be printed */
  DAGs = NULL;
  for (i = 0; i < table_length(e_clues_table); ++i)
    {
      Tclue clue = (Tclue) table_get(e_clues_table, i);
      assert(clue != NULL);
      if (clue->type == CLUE_ABSTRACT_TERM || 
	  clue->type == CLUE_ABSTRACT_QUANT || 
	  clue->type == CLUE_ABSTRACT_PRED)
	DAGs = list_add(DAGs, DAG_ptr_of(clue->DAG[0]));
      else
	DAGs = list_add(DAGs, DAG_ptr_of(clue->DAG[0]));
      if (clue->type == CLUE_ABSTRACT_TERM || clue->type == CLUE_MERGE) 
	DAGs = list_add(DAGs, DAG_ptr_of(clue->DAG[1]));
    }
  assert(DAG_of_DAG == NULL);
  table_apply(e_clues_table, (TFapply) clue_abstract_DAG);
  table_apply(e_clues_table, (TFapply) clue_reset_DAG);

  list_apply(DAG_of_DAG, (TFapply) bind_key_DAG);
  /*
    Let U be the SMT sort of terms in TPTP logic
    1) For each sort s in SMT, create a symbol f_s: U -> U
    2) For each function symbol f in SMT of non-negative arity n, 
    create a symbol f': U x ... x U -> U
    3) For each predicate symbol p in SMT of non-negative arity n, 
    create a symbol p': U x ... x U -> Bool
  */

  /* 1), 2) and 3) Find all relevant sorts and symbols */
  stack_INIT(collect_sort);
  stack_INIT(collect_symb);
  collect_logic(DAGs);
  list_free(&DAGs);

#ifdef DEBUG_E
  my_DAG_message("logic_get:\n");
  my_DAG_message("\tsorts:\n");
  for (j = 0; j < collect_sort->size; j++)
    my_DAG_message("\t\t%S\n", collect_sort->data[j]);
  my_DAG_message("\tsymbs:\n");
  for (j = 0; j < collect_symb->size; j++)
    my_DAG_message("\t\t%s\n", DAG_symb_name(collect_symb->data[j]));
#endif
  /* 1) Mark all sorts that have already a mapping symbol */
  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_sort_mark(assoc->sort);
  LIST_LOOP_END(symb_of_sort);
  /* Then a) for each sort that has no symbol yet, create and register */
  for (j = 0; j < collect_sort->size; j++)
    {
      Tsort sort = collect_sort->data[j];
      if (sort != SORT_BOOLEAN && !DAG_sort_is_marked(sort))
	{
	  Tsort_symb assoc;
	  MY_MALLOC(assoc, sizeof(struct TSsort_symb));
	  assoc->sort = sort;
	  /* The symbol is a function symbol, of arity one. 
	     The name is made up here */
	  assoc->symb = tptp_logic_function(DAG_sort_name(sort), 1);
	  symb_of_sort = list_add(symb_of_sort, assoc);
#ifdef DEBUG_E
	  my_DAG_message("symb_of_sort %S -> %u\n", sort,
			 symb_of_ptr(assoc->value));
#endif
	}
    }
  /* b) unmark sorts. */
  LIST_LOOP_BEGIN(symb_of_sort, Tsort_symb, assoc);
  DAG_sort_unmark(assoc->sort);
  LIST_LOOP_END(symb_of_sort);

  /* 2) and 3) Mark all symbols that already have a mapping symbol */
  LIST_LOOP_BEGIN(symb_of_symb, Tsymb_symb, assoc);
  DAG_symb_set_misc(assoc->symb1, 1);
  LIST_LOOP_END(symb_of_symb);
  /* Then, a) for each symb without mapping symbol, create and register; */
  for (j = 0; j < collect_symb->size; j++)
    {
      Tsymb symb = collect_symb->data[j];
      if (!DAG_symb_misc(symb))
	{
	  Tsymb_symb assoc;
	  MY_MALLOC(assoc, sizeof(struct TSsymb_symb));
	  assoc->symb1 = symb;
	  if (DAG_sort_arity(DAG_symb_sort(symb)) == 0)
	    assoc->symb2 = DAG_symb_is_predicate(symb)?symb:
	      tptp_logic_function(DAG_symb_name(symb), 0);
	  else
	    assoc->symb2 =
	      (DAG_symb_is_predicate(symb)?tptp_logic_predicate:
	       tptp_logic_function)
	      (DAG_symb_name(symb), DAG_symb_arity(symb));
#ifdef DEBUG_E
	  my_DAG_message("symb_of_symb %u[%s] -> %u\n", symb,
			 DAG_symb_name(symb), assoc->symb2);
#endif
	  symb_of_symb = list_add(symb_of_symb, assoc);
	}
    }
  /* unmark symbols that were already mapped. */
  LIST_LOOP_BEGIN(symb_of_symb, Tsymb_symb, assoc);
  DAG_symb_reset_misc(assoc->symb1);
  LIST_LOOP_END(symb_of_symb);

  /* Bind all sorts with the mapping symbol */
  list_apply(symb_of_sort, (TFapply) bind_sort_symb);
  /* Bind all symbols with the mapping symbol */
  list_apply(symb_of_symb, (TFapply) bind_symb_symb);

  stack_free(collect_sort);
  stack_free(collect_symb);
}

/*--------------------------------------------------------------------------*/

static void
e_write_input(char * filename, Tderivation deriv, Ttable clues_table)
{
  FILE* file;
  int   i;
  file = sys_open_file(filename, "w");
#ifdef DEBUG_E
  setbuf(file, NULL);
#endif
  fprintf(file,"# File %s\n", filename);
  fprintf(file,
	  ("# Proof obligation in the TPTP3/TSTP prover syntax,"
	   "generated with veriT.\n"));

  for (i = 0; i < table_length(e_clues_table); ++i)
    {
      TDAG DAG;
      Tclue clue = (Tclue) table_get(e_clues_table, i);
      assert(clue != NULL);
      tstp_print_clue(file, clue, i, !MULTISORTED);
      switch (clue->type) 
	{
	case CLUE_ABSTRACT_QUANT :
	case CLUE_ABSTRACT_PRED :
	  DAG = clue->DAG[0];
	  break;
	case CLUE_ABSTRACT_TERM :
	case CLUE_MERGE:
	  DAG = DAG_eq(clue->DAG[0], clue->DAG[1]);
	  break;
	case CLUE_INEQUALITY:
	  DAG = DAG_not(DAG_eq(clue->DAG[0], clue->DAG[1]));
	  break;
        default:
          my_error("internal error in e_write_input.\n");
	}
      /* Those two lines added by PF while reading code: strange DAG does not
	 appear somewhere */
      my_DAG_message("%D\n", DAG);
      my_error("internal error: fix\n");
    }
  sys_close_file(file);
}

/*--------------------------------------------------------------------------*/

/**
   \brief  Unbinds sorts and symbols attributes
   \pre    Attributes binding and Pflag of symbols and sorts are set
   \post   sorts and symbols have the binding and Pflag attributes unset
   \author David Deharbe
 */

static void
e_post_input(void)
{
  if (!MULTISORTED) return;

  list_apply(DAG_of_DAG, (TFapply) unbind_key_DAG);
  /* Unbind all sorts */
  list_apply(symb_of_sort, (TFapply) unbind_sort_symb);
  /* Unbind all symbols */
  list_apply(symb_of_symb, (TFapply) unbind_symb_symb);
}

/*--------------------------------------------------------------------------*/

/**
   \brief  Preamble to processing output of E prover
 */

static void
e_pre_output(void)
{
  if (!MULTISORTED) return;
  /* Bind all sort function symbols */
  list_apply(symb_of_sort, (TFapply) bind_sort_symb);
  /* Bind all symbols */
  list_apply(symb_of_symb, (TFapply) bind_symb_symb);
  /* Bind abstracted DAGs */
  list_apply(DAG_of_DAG, (TFapply) bind_value_DAG);
}

/*--------------------------------------------------------------------------*/

/* 
   DD reads the output generated by the prover into the files
   e_filenames.out (standard output) and e_filenames.err (standard
   error).  sets up status with the proof status and updates
   e_derivation with the rule applications.
*/
static void
e_read_output(void)
{
  char * cmd;
  size_t cmdlen;

  e_set_status (UNDEF);

  /* DD+PF the following code handles the case when the E prover has
     been killed by the system, due to a time limit imposed to
     veriT */
  cmd = NULL;
  cmdlen = 0;
  cmd = strapp(cmd, &cmdlen, "grep \"eprover: Unable to reset cpu time limit\" ");
  cmd = strapp(cmd, &cmdlen, e_filenames.err);
  cmd = strapp(cmd, &cmdlen, " > /dev/null");
  if (system(cmd) == 0)
    {
      e_set_status (UNDEF);
      return;
    }
  free(cmd);

  tstp_parse_file(e_filenames.out);
}

/*--------------------------------------------------------------------------*/

/**
   \brief  Unbinds sorts and symbols attributes
   \pre    Attributes binding and Pflag of symbols and sorts are set
   \post   sorts and symbols have the binding and Pflag attributes unset
   \author David Deharbe
 */

static void
e_post_output(void)
{
  if (!MULTISORTED) return;

  /* Unbind all sorts */
  list_apply(symb_of_sort, (TFapply) unbind_sort_symb);
  /* Unbind all symbols */
  list_apply(symb_of_symb, (TFapply) unbind_symb_symb);
  /* Unbind abstract DAGs */
  list_apply(DAG_of_DAG, (TFapply) unbind_value_DAG);
}

/*--------------------------------------------------------------------------*/
/*                  Management of data structures for E output              */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/

/* DD empties data structures where the output from E is stored */
static void
e_output_reset (void)
{
  derivation_reset (e_derivation);
  table_apply (e_var_eq_table, (TFapply) & clue_free);
  table_erase (e_var_eq_table);
}

/*--------------------------------------------------------------------------*/

/* DD frees data structures where the output from E is stored */

static void
e_output_free (void)
{
  derivation_free (& e_derivation);
  table_apply (e_var_eq_table, (TFapply) & clue_free);
  table_free (&e_var_eq_table);
}


/*--------------------------------------------------------------------------*/

static int 
is_var_eq (const TDAG DAG)
{
  return DAG && DAG_symb(DAG) == PREDICATE_EQ;
}

/*--------------------------------------------------------------------------*/
/*                              Finding premisses                           */
/*--------------------------------------------------------------------------*/
/**
   \brief stores in the list pointed to by Plist the DAG of the 
   axioms given to E that were used to derive step 'id'; 
   \param id is an inference number, it is a valid index of the
   table \a e_derivation->steps.
   \note each step is visited at most once: 'flag' is set on the 
   visited steps.
*/

static void
e_DAG_premisses_aux (const uintptr_t id, Tlist * Plist)
{
  Tinference inference;
  Tlist  premisses;
  assert (id <= table_length (e_derivation->steps));
  assert (id > 0);

  inference = table_get (e_derivation->steps, id);
  if (inference->flag) return;
  inference->flag = 1;
  premisses = inference->premisses;
  LIST_LOOP_BEGIN (premisses, Tpremisse, p);
  uintptr_t id2 = premisse_value(p);
  if (premisse_is_external(p))
    {
      Tinference inference;
      assert(list_length(premisses) == 1);
      inference = table_get(e_derivation->steps, id);
      *Plist = list_cons(DAG_ptr_of(inference->DAG), *Plist);
    }
  else
    e_DAG_premisses_aux(id2, Plist);
  LIST_LOOP_END (premisses);
}

/*--------------------------------------------------------------------------*/
/* DD id is a step in the last inference performed by E.
   the function returns the list of DAGs of the clues given to E 
   that have been employed to derive the given step. */
static Tlist
e_DAG_premisses (uintptr_t id)
{
  Tunsigned i;
  Tlist result;

  result = NULL;
  e_DAG_premisses_aux (id, &result);
  for (i = 0; i < table_length (e_derivation->steps); ++i)
    inference_reset_flag ((Tinference) table_get(e_derivation->steps, i));

  return result;
}

/*--------------------------------------------------------------------------*/
/* DD stores in the list pointed to by Plist the steps given to 
   E that were used to derive step 'id'; 
   each step is visited at most once: the visited steps see their 
   'processed' flag set.
*/

static void
e_clue_premisses_aux (const uintptr_t i, Tlist * Plist)
{
  Tinference inference;
  Tlist      premisses;
  assert (i < table_length (e_derivation->steps));
  inference = table_get (e_derivation->steps, i);
  /** check that we do not reach the dummy inference */
  assert (i > 0);
  if (inference->flag) return;
  inference->flag = 1;
  premisses = inference->premisses;
  LIST_LOOP_BEGIN(premisses, Tpremisse, p);
  uintptr_t id2 = premisse_value(p);
  if (premisse_is_external(p))
    {
      Tclue clue = (Tclue) table_get(e_clues_table, id2);
      if (clue->type != CLUE_ABSTRACT_TERM)
	*Plist = list_add(*Plist, clue);
    }
  else
    e_clue_premisses_aux(id2, Plist);
  LIST_LOOP_END(premisses);
}

/*--------------------------------------------------------------------------*/
/* DD id is a step number in the last derivation; 
   returns a list of all the clues employed to reach that step. */
static Tlist
e_clue_premisses (uintptr_t id)
{
  Tlist result = NULL;

  e_clue_premisses_aux (id, &result);
  table_apply (e_derivation->steps, (TFapply) & inference_reset_flag);

  return result;
}

/*--------------------------------------------------------------------------*/
/**
   \brief Builds and returns the DAG of a lemma.  
   \param id shall be a clause in the saturated set of the last derivation.  
   \return the lemma is the implication whose antecedent is the conjunction 
   of the hypothesis used to derive the clause and consequent is the 
   clause itself.
   \return it returns NULL if the lemma is trivial (e.g. p => p).
*/
static TDAG 
e_lemma(const Tunsigned id)
{
  TDAG       conclusion;
  TDAG       antecedent;
  TDAG       lemma;
  Tlist      premisses;

  assert (!e_options_disable || e_options_enable);
  assert (id < table_length (e_derivation->steps));
  assert (id > e_derivation->nb_axioms);

  premisses = e_DAG_premisses(id);

  /* Handle the case of a tautology. */
  if (premisses == NULL)
    return DAG_NULL;
  
  /* Build antecedent of lemma. */
  if (list_cdr (premisses) == premisses)
    antecedent = DAG_dup(DAG_of_ptr(list_car(premisses)));
  else
    antecedent = DAG_dup(DAG_new_list(CONNECTOR_AND, premisses));
  list_free (&premisses);

  /* If antecedent is a tautology, consequent is too: not interesting. */
  if (antecedent == DAG_TRUE)
    {
      DAG_free(antecedent);
      return DAG_NULL;
    }
      
  conclusion =  ((Tinference) table_get (e_derivation->steps, id))->DAG;

  /* Handle the case of a worthless implication */
  if (antecedent == conclusion)
    {
      DAG_free(antecedent);
      return DAG_NULL;
    }

  /* E often rewrites quantified formulas by only changing the propositional structure of the matrix.
     This does not seem to be interesting to build lemmas from this. */
  if (DAG_symb(antecedent) == QUANTIFIER_FORALL && 
      DAG_symb(conclusion) == QUANTIFIER_FORALL &&
      DAG_arity(antecedent) == DAG_arity(conclusion)) 
    {
#ifdef DEBUG_E
      my_DAG_message ("E: filtered out lemma:\n\t%D => %D\n", antecedent, conclusion);
#endif
      return DAG_NULL;
    }

  lemma = DAG_implies(antecedent, conclusion);
  DAG_free(antecedent);
#ifdef DEBUG_E
  my_DAG_message ("E: produced lemma %D.\n", lemma);
#endif

  return lemma;
}

#ifdef PROOF
/*--------------------------------------------------------------------------*/
/*                           Proof production stuff                         */
/*--------------------------------------------------------------------------*/
static TDAG
my_clue_DAG(Tclue clue)
{
  TDAG result = DAG_NULL;;
  switch (clue->type) {
  case CLUE_ABSTRACT_QUANT:
  case CLUE_ABSTRACT_PRED:
    result = clue->DAG[0];
    break;
  case CLUE_ABSTRACT_TERM:
    if (clue->DAG[0] != clue->DAG[1])
      result = DAG_eq(clue->DAG[0], clue->DAG[1]);
    else
      result = DAG_TRUE;
    break;
  case CLUE_MERGE:
    assert (clue->DAG[0] != clue->DAG[1]);
    result = DAG_eq(clue->DAG[0], clue->DAG[1]);
    break;
  }
  if (!clue->polarity)
    result = DAG_not(result);
  return result;
}



Tproof_id
e_build_proof(Tlist clues, TDAG DAG)
{
  Tlist lits = NULL;
  Tproof_id proof_id;
  LIST_LOOP_BEGIN(clues, Tclue, clue);
  lits = list_add(lits, DAG_ptr_of(DAG_not(my_clue_DAG(clue))));
  LIST_LOOP_END(clues);
  if (DAG)
    lits = list_add(lits, DAG_ptr_of(DAG));
  proof_id = proof_clause_list(fol_generic, lits);
  list_free(&lits);
  return proof_id;
}
#endif

/*--------------------------------------------------------------------------*/
/*                      Implementation of public routines                   */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/

Tstatus 
e_status (void)
{
  return status;
}

/*--------------------------------------------------------------------------*/

void
e_push (Tclue clue)
{
  if (e_options_disable || !e_options_enable) 
    {
      clue_free (clue);
      return;
    }

  e_level += 1;
#ifdef DEBUG_E
  my_message("E: e_push (");
  clue_print2(clue);
  fprintf(stderr, ")\n");
  fprintf (stderr, "level %i\n", e_level);
#endif

  if (status == UNSAT || clue == NULL)
    {
      clue_free (clue);
      return;
    }

  e_set_status (OPEN);
  e_sort_check_clue (clue);
  history_clue_store ();
  table_push(e_clues_table, (void *) clue);
#ifdef DEBUG_E
  history_print();
#endif
}

/*--------------------------------------------------------------------------*/
static int e_flag_solve_last = 0;

/* 
   DD removes a clue in LIFO order 
*/
void
e_pop (void)
{
  if (e_options_disable || !e_options_enable) return;
  e_flag_solve_last = 0;
  history_backtrack (e_level);
  e_level -= 1;
#ifdef DEBUG_E
  my_message("E: e_pop ()");
  fprintf (stderr, "level %i\n", e_level);
#endif
#ifdef DEBUG_E
  history_print();
#endif
}

/*--------------------------------------------------------------------------*/

/*
  DD runs the E prover on the set of clues on the clue stack; updates
  status with the result of this run; 

  stores the derivation in e_derivation
*/
Tstatus
e_solve (void)
{
  char * command_str; /* DD command line to run E */

  if (e_options_disable || !e_options_enable) return OPEN;

  /* DD returns if external eprover binary is not available */
  if (!e_binary_test()) return OPEN;
  
  if (e_flag_solve_last)
    my_message("e_solve called twice\n");
  e_flag_solve_last = 1;

#ifdef DEBUG_E
  {
    int i;
    my_message("E: e_solve\n");
    for (i = 0; i < table_length(e_clues_table); ++i)
      {
	Tclue clue = (Tclue) table_get(e_clues_table, i);
	assert(clue != NULL);
	clue_fprint(stderr, clue);
	fprintf (stderr, "\n");
      }
  }
#endif

  /* DD returns if clue has been pushed since last call to e_solve() */
  if (e_solve_point == table_length(e_clues_table))
    return status;
  e_solve_point = table_length(e_clues_table);

  /* DD E solver needs to be called - prepare data structures */
  e_output_reset ();
  e_filenames_new();
  e_pre_input(e_clues_table);
  e_write_input(e_filenames.inp, e_derivation, e_clues_table);
  e_post_input();

  command_str = e_generate_command(processed_clause_limit(e_clues_table));
  system(command_str);  
  free(command_str);

  e_pre_output();
  e_read_output();
  e_post_output();

  process_derivation(e_derivation);
  while (DAG_of_DAG)
    {
      TDAG_pair assoc = (TDAG_pair) list_car(DAG_of_DAG);
      DAG_free(DAG_of_ptr(assoc->value));
      free(assoc);
      DAG_of_DAG = list_remove(DAG_of_DAG);
    }

  /** 
      process output: 
      - detect unsatisfiability;
      - if not unsatifiable, find variable equalities;
      - lemmas are not computed here but will be evaluated lazily in e_has_lemma.
  */ 
  if (e_derivation->conflict)
    e_set_status (UNSAT);
  else
    {
      /* DD Finds variable equalities; DAG flags are set to avoid duplicates, 
       * and DAG Pflags link variable equalities */
      Tunsigned i;
      TDAG head = DAG_NULL;
      for (i = e_derivation->nb_axioms + 1; i < table_length (e_derivation->steps); ++i)
	{
	  TDAG DAG;
	  DAG = ((Tinference) table_get (e_derivation->steps, i))->DAG;
	  if (DAG && !DAG_flag(DAG) &&
	      is_var_eq(DAG) && DAG_arg0(DAG) != DAG_arg1(DAG))
	    {
	      /* DD create a clue, register its id, and push it in the queue */
	      Tclue clue;
	      TUproof proof;
#ifdef DEBUG_E
	      my_DAG_message("found variable equality %D.\n", DAG);
#endif
	      assert(DAG_flag(DAG) == DAG_NULL);
	      DAG_DAG(DAG) = head;
	      head = DAG;
	      DAG_flag(DAG) = 1;
	      proof.arith = e_clue_premisses(premisse_value(i));
	      clue = clue_new_merge(DAG_arg0(DAG), 
				    DAG_arg1(DAG), 
				    e_id, proof);
	      e_eq_queue_push (clue);
	    }
	}
      /** DD DAG flags are now unset */
      while (head)
	{
	  TDAG next = DAG_DAG(head);
	  DAG_flag(head) = 0;
	  DAG_DAG(head) = DAG_NULL;
	  head = next;
	}
    }
  if (!e_options_traceable)
    {
      remove(e_filenames.inp);
      remove(e_filenames.out);
      remove(e_filenames.err);
    }
  e_filenames_delete();

  return status;
}

/*--------------------------------------------------------------------------*/

static void 
e_signal_handle(int sig, void * P)
{
  printf("Signal #%i caught.\n", sig);
  if (e_filenames.inp)
    {
      if (!e_options_traceable)
	remove(e_filenames.inp);
      free(e_filenames.inp);
      e_filenames.inp = NULL;
    }
  if (e_filenames.out)
    {
      if (!e_options_traceable)
	remove(e_filenames.out);
      free(e_filenames.out);
      e_filenames.out = NULL;
    }
  if (e_filenames.err)
    {
      if (!e_options_traceable)
	remove(e_filenames.err);
      free(e_filenames.err);
      e_filenames.err = NULL;
    }
  if (e_filenames.dir)
    {
      remove(e_filenames.dir);
      free(e_filenames.dir);
    }
  _exit(sig);
}

/*--------------------------------------------------------------------------*/

void       
e_init (const unsigned id)
{
#ifdef DEBUG_E
  my_message("E: e_init (%u)\n", id);
#endif
  e_id = id;
  options_new (0, "disable-e", "Disable E prover", &e_options_disable);
  options_new (0, "enable-e", "Enable E prover", &e_options_enable);
  options_new (0, "trace-e", "Maintains intermediate files", 
	       &e_options_traceable);
  e_solve_point = 0;
  e_filenames.dir = e_filenames.inp = e_filenames.out = e_filenames.err = NULL;
  status = OPEN;
  e_clues_table = table_new (50, 50);
  e_var_eq_table = table_new (50, 50);
  e_lemmas_hash = hash_new (50, (TFhash) DAG_hash, (TFequal) DAG_equal, 
			    (TFfree) DAG_free);
  e_new_lemmas_table = table_new (50, 50);
  e_derivation = derivation_new ();
  e_sort_list = NULL;
  symb_of_sort = NULL;
  symb_of_symb = NULL;
  DAG_of_DAG = NULL;
  var_symb_list = NULL;
  skl_symb_list = NULL;
  e_binary_test();
  tptp_logic_init();
  veriT_signal_register(e_signal_handle, NULL);
}

/*--------------------------------------------------------------------------*/

void       
e_done (void)
{
#ifdef DEBUG_E
  my_message("E: e_done\n");
#endif
  history_free ();
  list_free(&e_sort_list);

  list_apply(symb_of_sort, (TFapply) free);
  list_free(&symb_of_sort);
  list_apply(symb_of_symb, (TFapply) free);
  list_free(&symb_of_symb);
  assert(DAG_of_DAG == NULL);

  if (e_filenames.dir && !e_options_traceable)
    {
      remove(e_filenames.dir);
      free(e_filenames.dir);
    }
  hash_free(&e_lemmas_hash); /* DD all DAGs in e_lemmas_hash are applied DAG_free */
  table_apply(e_new_lemmas_table, (TFapply) DAG_free);
  table_free(&e_new_lemmas_table);
  table_apply(e_clues_table, (TFapply) clue_free);
  table_free(&e_clues_table);
  e_output_free();
  tptp_logic_quit();
}

/*--------------------------------------------------------------------------*/

void
e_reset(void)
{
  if (e_options_disable || !e_options_enable) return;
#ifdef DEBUG_E
  my_message("E: e_reset\n");
#endif
  e_level = 0;
  e_solve_point = 0;

  list_apply(symb_of_sort, (TFapply) free);
  list_free(&symb_of_sort);
  list_apply(symb_of_symb, (TFapply) free);
  list_free(&symb_of_symb);
  assert(DAG_of_DAG == NULL);

  if (e_new_lemmas_table)
    {
      table_apply (e_new_lemmas_table, (TFapply) DAG_free);
      table_erase (e_new_lemmas_table);
    }
  history_reset ();
  derivation_reset (e_derivation);
  e_output_reset ();
  status = OPEN;
}

/*--------------------------------------------------------------------------*/

/* DD prints the current state of the decision procedure (TODO) */
void
e_print (FILE * file)
{
}

/*--------------------------------------------------------------------------*/

/* DD returns the clues that were used to derive a given clue */
Tlist
e_premisses (const Tclue clue)
{
  Tlist tmp;
  assert (!e_options_disable || e_options_enable);
  tmp = list_cpy((Tlist) clue->proof.arith);
#ifdef DEBUG_E
  my_message("E: e_premisses (");
  clue_fprint(stderr, clue);
  fprintf(stderr, ")\n");
  list_clue_fprint (stderr, tmp);
#endif
#ifdef PROOF
  clue->proof_id = e_build_proof(tmp, DAG_eq(clue->DAG[0], clue->DAG[1]));
#endif
  return tmp;
}

/*--------------------------------------------------------------------------*/

/* DD returns the conflict set */
#ifdef PROOF
Tlist
e_conflict (Tproof_id * Pproof_id)
#else
  Tlist
  e_conflict (void)
#endif
{
  Tlist result;
#ifdef PROOF
  *Pproof_id = 0;
#endif
#ifdef DEBUG_E
  my_message("E: e_conflict %i\n", e_derivation->conflict);
#endif
  assert (!e_options_disable || e_options_enable);
  assert (status == UNSAT);
  result = e_clue_premisses(e_derivation->conflict);
#ifdef DEBUG_E
  list_clue_fprint (stderr, result);
#endif
#ifdef PROOF
  * Pproof_id = e_build_proof(result, DAG_NULL);
#endif
  return result;
}

/*--------------------------------------------------------------------------*/

/* DD tests if the procedure has derived variable equalities */
bool
e_eq_queue_empty(void)
{
#ifdef DEBUG_E
  my_message("E: e_eq_queue_empty: %i\n", table_empty (e_var_eq_table));
#endif
  return table_empty (e_var_eq_table);
}

/*--------------------------------------------------------------------------*/

/* DD removes and returns a clue to the list of variable equalities
   derived by the procedure */
Tclue
e_eq_queue_pop(void)
{
  assert (table_length (e_var_eq_table) > 0);
#ifdef DEBUG_E
  my_message("E: e_eq_queue_pop (");
  clue_fprint(stderr, (Tclue) table_top(e_var_eq_table));
  fprintf(stderr, ")\n");
#endif
  return (Tclue) table_pop(e_var_eq_table);
}

/*--------------------------------------------------------------------------*/

/* DD adds a clue to the list of variable equalities derived by the
   procedure */
void
e_eq_queue_push(Tclue clue)
{
#ifdef DEBUG_E
  my_message("E: e_eq_queue_push (");
  clue_fprint (stderr, clue);
  fprintf (stderr, ")\n");
#endif
  history_equality_found (clue);
  table_push(e_var_eq_table, (void *) clue);
}

/*--------------------------------------------------------------------------*/
/* DD pushes on table all the lemmas that were derived, i.e.  the
   clauses in the saturation set of the previous call to the E prover.
*/
void e_lemmas (Ttable table)
{
#ifdef DEBUG_E
  my_message("E: e_lemmas\n");
#endif
  while (!table_empty(e_new_lemmas_table))
    {
      TDAG DAG = DAG_of_ptr(table_pop(e_new_lemmas_table));
#ifdef DEBUG_E
      my_DAG_message ("E: %D\n", DAG);
#endif      
      table_push(table, DAG_ptr_of(DAG));
#ifdef PROOF
      proof_add_fol_lemma(DAG_dup(DAG));
#endif
    }
}

/*--------------------------------------------------------------------------*/
/*
  DD Test applied to lemmas after simplification.
*/
static int
interesting_lemma (TDAG DAG)
{
  if (DAG == DAG_TRUE) return 0;
  return 1;
}

/*--------------------------------------------------------------------------*/
/* DD tests if the module has produced lemmas */
bool e_has_lemma (void)
{
  Tunsigned i;
  bool result;
  if (e_options_disable || !e_options_enable) return false;
  if (table_length(e_new_lemmas_table) > 0) return true;
  result = false;

  if (table_length(e_derivation->steps) > e_derivation->nb_axioms)
    {
      for (i = table_length (e_derivation->steps) - 1; 
	   i > e_derivation->nb_axioms ; --i)
	{
	  Tinference inf = (Tinference) table_get (e_derivation->steps, i);
	  if (!inf->ignore &&
	      (inf->final || (DAG_ground(inf->DAG) && !DAG_quant(inf->DAG))))
	    {
	      TDAG lemma;
	      lemma = e_lemma(i);
	      /* e_lemma returns DAG_NULL when the lemma is not interesting */
	      if (lemma == DAG_NULL) continue;
	      lemma = DAG_dup(lemma);
#ifndef PROOF
	      lemma = simplify_formula(lemma);
#endif
	      /** filter interesting lemmas after simplification too */
	      if (!interesting_lemma(lemma)) 
		{
		  DAG_free(lemma);
		  continue;
		}
	      /** do not generate the same lemma twice */
	      if (hash_lookup(e_lemmas_hash, DAG_ptr_of(lemma))) 
		{
		  DAG_free(lemma);
		  continue;
		}

	      /** a lemma is generated */
	      result = true;
	      hash_insert(e_lemmas_hash, DAG_ptr_of(DAG_dup(lemma)));
	      table_push(e_new_lemmas_table, DAG_ptr_of(lemma));
	    }
	}
    }

  return result;
}

/*-----------------------------------------------------------------------*/
/*                            History stuff                              */
/*-----------------------------------------------------------------------*/

/* DC identifies a recorded event */

#define HISTORY_EQUALITY_FOUND 0
#define HISTORY_STATUS_CHANGE  1
#define HISTORY_SORT_ADD       2
#define HISTORY_CLUE_STORE     3
#define HISTORY_SORT_SET       4

typedef struct TShistory
{
  void *             Pdata;
  int                data;
  int                level;
  int                kind;
  struct TShistory * next;
} *Thistory;

/* DC list of events recorded */
static Thistory e_history;

/*-----------------------------------------------------------------------*/

static Thistory
history_new_record (int kind)
{
  Thistory record;

  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = e_level;
  record->kind = kind;
  record->next = e_history;
  e_history = record;

  return record;
}

/*-----------------------------------------------------------------------*/

/* DC records a equality clue found */
static void
history_equality_found (Tclue clue)
{
  Thistory record;
  record = history_new_record (HISTORY_EQUALITY_FOUND);
  clue_dup (clue);
  record->Pdata = (void *) clue;
}


/*-----------------------------------------------------------------------*/

/* DC change the set of returned equalities to previous state */
static void
history_equality_found_back ()
{
  Tclue clue;
#ifdef DEBUG_E
  my_message ("backtracking equality.\n");
#endif
  clue = (Tclue) e_history->Pdata;
  list_free (&clue->proof.arith);
  clue_free (clue);
}

/*-----------------------------------------------------------------------*/

/* DD records current status before assigning it a new value */
static void
history_status_change ()
{
  Thistory record;
  record = history_new_record (HISTORY_STATUS_CHANGE);
  record->data = status;
}


/*-----------------------------------------------------------------------*/

/* DD restores the status value */
static void
history_status_change_back ()
{
#ifdef DEBUG_E
  my_message ("backtracking status change from %i to %i.\n", 
	      status, e_history->data);
#endif
  status = (Tstatus) e_history->data;
}

/*-----------------------------------------------------------------------*/

/* DD records that the logic is now multisorted */
static void
history_sort_add (Tsort sort)
{
  (void) history_new_record (HISTORY_SORT_ADD);
}

/*-----------------------------------------------------------------------*/

/* DD revert to a monosorted logic */
static void
history_sort_add_back ()
{
#ifdef DEBUG_E
  my_message ("backtracking multisort set.\n");
#endif
  e_sort_list = list_remove(e_sort_list);
}

/*-----------------------------------------------------------------------*/

/* DD records that a clue has been stored */
static void
history_clue_store (void)
{
  (void) history_new_record(HISTORY_CLUE_STORE);
}


/*-----------------------------------------------------------------------*/

/* DD removes a stored clue */
static void
history_clue_store_back ()
{
  Tclue clue = (Tclue) table_top(e_clues_table);
#ifdef DEBUG_E
  my_message ("backtracking clue store.\n");
#endif
  clue_free(clue);
  table_pop(e_clues_table);
}

/*-----------------------------------------------------------------------*/

/* DD records that a sort has been set */
static void
history_sort_set (Tsort sort)
{
  Thistory record = history_new_record (HISTORY_SORT_SET);
  record->Pdata = ptr_of_sort(sort);
}


/*-----------------------------------------------------------------------*/

/* DD unset sort */
static void
history_sort_set_back ()
{
#ifdef DEBUG_E
  my_message ("backtracking sort set.\n");
#endif
  tptp_logic_set_sort(sort_of_ptr(e_history->Pdata));
}

/*-----------------------------------------------------------------------*/

/* revert events recorded up to level */
static void
history_backtrack (unsigned level)
{
#ifdef DEBUG_E
  my_message ("Backtracking to level %u\n", level);
#endif
  while (e_history != NULL && e_history->level >= level)
    {
      Thistory tmp;
      switch (e_history->kind)
	{
	case HISTORY_EQUALITY_FOUND:
	  history_equality_found_back ();
	  break;
	case HISTORY_STATUS_CHANGE:
	  history_status_change_back ();
	  break;
	case HISTORY_SORT_ADD:
	  history_sort_add_back ();
	  break;
	case HISTORY_CLUE_STORE:
	  history_clue_store_back ();
	  break;
	case HISTORY_SORT_SET:
	  history_sort_set_back ();
	  break;
	default:
	  assert (0);
	}
      tmp = e_history->next;
      free (e_history);
      e_history = tmp;
    }
}

/*-----------------------------------------------------------------------*/

static void
history_reset (void)
{
  history_backtrack (0);
}

/*-----------------------------------------------------------------------*/

static void
history_free (void)
{
  history_reset ();
}

/*-----------------------------------------------------------------------*/

/* revert events recorded up to level */
#ifdef DEBUG_E
static void
history_print ()
{
  int      counter;
  Thistory ptr = e_history;
  counter = 0;
  while (ptr) 
    {
      switch (ptr->kind)
	{
	case HISTORY_EQUALITY_FOUND:
	  my_message ("E : history %i - equality found.\n", ptr->level);
	  break;
	case HISTORY_STATUS_CHANGE:
	  my_message ("E : history %i - status changed.\n", ptr->level);
	  break;
	case HISTORY_SORT_ADD:
	  my_message ("E : history %i - sort add.\n", ptr->level);
	  break;
	case HISTORY_CLUE_STORE:
	  ++counter;
	  my_message ("E : history %i - clue stored.\n", ptr->level);
	  break;
	case HISTORY_SORT_SET:
	  my_message ("E : history %i - sort set.\n", ptr->level);
	  break;
	default:
	  assert (0);
	}
      ptr = ptr->next;
    }
  assert (counter == table_length(e_clues_table));
}
#endif

static int
DAG_symb_arity(Tsymb symb)
{
  int arity = DAG_sort_arity(DAG_symb_sort(symb));
  if (arity == DAG_SORT_NARY)
    return -1;
  else
    return arity - 1;
}
