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
  Module for congruence closure
  --------------------------------------------------------------
*/

/* TODO
   DAG_add_q: may add a predicate DAG, and cause problems
   In DAG_add there is something about quantifiers:
     tidy things about quantifiers
   DEAD_NODES is not used consistently and not up to date?
   handle if-then-else terms
   Hash: it seems hashs are not that great.  Try to tune
   Re-read CC_union, CC_desunion
*/

/* PF
   Clues produced by this modules:
   - literal clues
     1. inequalities by CC_union :
       * an inequality X != Y has been once added
       * X is relevant for given DP
       * Y was not relevant for same DP
       * union make Y relevant for same DP
     2. inequalities by CC_anti_merge :
       * an inequality is pushed with both members relevant for given DP
     3. predicates by CC_set_predicate
     No equalities should be send (only merges)
   - merge clues by CC_union :
       * when two classes relevant for DP are merged
       * or when class relevant for DP changes representant
   - abstract (DAG_add)
       * when new term is found with top most symbol relevant for DP
         Predicates not sent this way, but through literal clues (see
         above)
*/

/* #define DEBUG_CC */

#include "config.h"

#include <limits.h>
#include <stdlib.h>
#include <strings.h>
#if defined(DEBUG_CC)
#include <stdio.h>
#endif

#include "config.h"
#include "types.h"
#include "general.h"
#include "hash.h"
#include "hashmap.h"
#include "list.h"
#include "recursion.h"
#include "table.h"
#include "stack.h"

#include "undo.h"

#include "bool.h"
#include "clue.h"
#if defined(DEBUG_CC)
#include "clue-print.h"
#endif
#include "config.h"
#include "congruence.h"
#include "DAG-symb.h"
#include "dll-DAG.h"
#include "DAG.h"
#include "DAG-ptr.h"
#include "DAG-tmp.h"
#include "DAG-print.h"
#ifdef PROOF
#include "polarities.h"
#include "proof.h"
#endif
#include "veriT-status.h"

#define symb_hash(s) DAG_symb_hash(s)
#define symb_type(s) DAG_symb_type(s)
#define symb_name(s) DAG_symb_name(s)
#define symb_dp_mask(s) DAG_symb_dp_mask(s)
#define symb_key(s) DAG_symb_key(s)
#define symb_misc(s) DAG_symb_misc(s)

static Tstatus status;

/* DD+PF mask of DPs in the NO game */
unsigned CC_mask = 0;

/* DD+PF mask of DPs that should be informed of quantified formulas */
unsigned CC_mask_quantified = 0;

/* DD+PF buffers of clues for each DP */
Tstack_clue CC_buffer;
/* DD identifies the decision procedure in the Nelson Oppen combination */
unsigned CC_id;

/* One hash table for each symbol
   DAG : use hash_keys.
   How does it react with a != a
   p(a), !p(a) */

/* PF if DEAD_NODE is true for a node, it is assumed to be a constant for
   congruence closure.
   Should only depend on DAG_symb(DAG) */
/* PF TODO: there used to be 
#define DEAD_NODE(DAG) (quantifier(DAG_symb(DAG)) || DAG_symb(DAG) == LAMBDA)
*/
#define DEAD_NODE(DAG) (quantifier(DAG_symb(DAG)))

#ifdef PROOF
#define EXPLAIN_CLASSIC
#endif

typedef TDAG Tclass;

/**
   \brief table of class indexed by DAG */
Tclass *class;

typedef struct Tclass_info
{
  unsigned elem_nb;             /*< nb of elements in class */
  TDAG elem;                    /*< next element in class */
  unsigned pred_nb;		/*< nb of predecessors */
  Tlist pred;			/*< list of TDAG for predecessors */
  TDAG DAG;			/*< representing DAG for subDAGs in sigs. */
  unsigned ineq_nb;		/*< nb of inequalities */
  Tlist ineq;			/*< list of inequality clues about class */
  unsigned watch_eq_nb;		/*< nb of watch equalities */
  Tlist watch_eq;		/*< list of watch equalities */
  unsigned dp_mask;             /*< DPs interested by the class */
  Tboolean_value boolean_value;	/*< boolean value if class for a predicate */
} Tclass_info;

static Tclass_info * class_info = NULL;

typedef struct TCC
{
#ifdef EXPLAIN_CLASSIC
  Tstack_clue stack_eq;         /*< Equalities with DAG in one member */
#else
  TDAG next;
  Tclue clue;
#endif
  Tclue clue_pred;              /*< clue setting value to a predicate */
} TCC;

static TCC * CC = NULL;

#define CC_find(a) (class_info + class[a])

/*
  --------------------------------------------------------------
  Class list
  --------------------------------------------------------------
*/

/* #define CC_CLASS_LIST */

#ifdef CC_CLASS_LIST

#warning CC_CLASS_LIST set

/**
   \brief list of classes (one DAG per class, the representative) */
Tdll_DAG class_list = DLL_DAG_NULL;
/**
   \brief For each DAG, points to its element in the list of classes */
Tdll_DAG *in_class_list;

#define CLASS_LIST_RM(class1)				\
  assert(in_class_list[class1]);			\
  assert(dll_DAG_car(in_class_list[class1]) == class1);	\
  class_list = dll_DAG_remove(in_class_list[class1]);	\
  in_class_list[class1] = DLL_DAG_NULL;

#define CLASS_LIST_ADD(class1)				\
  assert(!in_class_list[class1]);			\
  class_list = dll_DAG_cons(class1, class_list);	\
  in_class_list[class1] = class_list;

#else

#define CLASS_LIST_RM(class1)
#define CLASS_LIST_ADD(class1)

#endif

/*
  --------------------------------------------------------------
  Tclass (congruence classes)
  --------------------------------------------------------------
*/

#ifdef DEBUG_CC
static void
class_print(Tclass class0)
/* PF print class information */
{
  TDAG DAG;
  Tlist list;
  Tclass_info * Pclass = class_info + class0;
  my_DAG_message("Class %d, with representative %D, mask %d, value %d:\n",
		 class0, Pclass->DAG, Pclass->dp_mask, Pclass->boolean_value);
  DAG = class0;
  while (DAG)
    {
      my_DAG_message("  %D\n", DAG);
      DAG = class_info[DAG].next;
    }
  my_DAG_message("  Predecessors (%d)\n", Pclass->pred_nb);
  list = Pclass->pred;
  LIST_LOOP_BEGIN(list, void *, P);
  {
    TDAG DAG = DAG_of_ptr(P);
    my_DAG_message("  %D\n", DAG);
  }
  LIST_LOOP_END(list);
  my_DAG_message("  Inequalities (%d)\n", Pclass->ineq_nb);
  list = Pclass->ineq;
  LIST_LOOP_BEGIN(list, Tclue, clue);
  my_DAG_message("    NOT(%D = %D)\n", clue->DAG[0], clue->DAG[1]);
  LIST_LOOP_END(list);
  my_DAG_message("  Watch equalities (%d)\n", Pclass->watch_eq_nb);
  list = Pclass->watch_eq;
  LIST_LOOP_BEGIN(list, Tclue, clue);
  my_DAG_message("    NOT(%D = %D)\n", clue->DAG[0], clue->DAG[1]);
  LIST_LOOP_END(list);
}
#endif

/*
  --------------------------------------------------------------
  (Signatures table)
  --------------------------------------------------------------
*/

/* PF hash key is not calculated from the classes of subterms
   but rather from a given representative associated to those classes.
   When merging, this allows to either
   - change the representative of the surviving class and reenter
     signatures of the parents of this class
   - reenter the parents of the disappearing class
     according to the number of parents in both classes */

/* PF signature hash table */
Thash sig_hash = NULL;
/* PF zero arity DAGs are not maintained in sig_hash.
   So put in this table */
Tstack_DAG zero_arity = NULL;
/* PF Quantified formulas are not maintained in sig_hash.
   So put in this list */
Tstack_DAG CC_quantified = NULL;

#ifdef DEBUG_CC
static int sig_hash_n = 0;
#endif

/*--------------------------------------------------------------*/

/* PF compute the hash function associated to DAG */
static unsigned
sig_hash_function(TDAG DAG)
{
  unsigned i;
  unsigned key;
  assert(DAG);
  if (DEAD_NODE(DAG))
    return DAG_key(DAG);
  key = symb_key(DAG_symb(DAG));
  key = hash_one_at_a_time_u_inc(key, DAG_arity(DAG));
  for (i = 0; i < DAG_arity(DAG); i++)
    key = hash_one_at_a_time_u_inc(key,
				   DAG_key(CC_find(DAG_arg(DAG, i))->DAG));
  return hash_one_at_a_time_inc_end(key);
  /* PF Old hash (it is better for some case)
     TODO: investigate different hash functions
  key = (int) DAG_symb(DAG);
  key = key << 1 ^ key >> 1 ^ DAG_arity(DAG);
  for (i = DAG_arity(DAG) - 1; i >= 0; --i)
    key = key << 1 ^ key >> 1 ^ CC_find(DAG_arg(DAG, i))->DAG_key(DAG);
  return key;
  */
}

/*--------------------------------------------------------------*/

/* PF returns 1 iff signatures are equal */
static bool
sig_hash_equal(TDAG DAG1, TDAG DAG2)
{
  unsigned i, j;
  assert(DAG1);
  assert(DAG2);
  /* TODO: rather make sure no dead node in sig_hash */
  if (DEAD_NODE(DAG1) || DEAD_NODE(DAG2))
    return DAG1 == DAG2;
  if (DAG_symb(DAG1) != DAG_symb(DAG2) || DAG_arity(DAG1) != DAG_arity(DAG2))
    return false;
  j = DAG_arity(DAG1);
  for (i = 0; i < j; i++)
    if (class[DAG_arg(DAG1, i)] != class[DAG_arg(DAG2, i)])
      return false;
  return true;
}

/*--------------------------------------------------------------*/

/* PF returns the DAG (in sig table) if signature of DAG exists */
static TDAG
sig_query(TDAG DAG)
{
  assert(DAG);
  return DAG_of_ptr(hash_lookup(sig_hash, DAG_ptr_of(DAG)));
}

/*--------------------------------------------------------------*/

/* PF delete signature of DAG from table */
static void
sig_delete(TDAG DAG)
{
  assert(DAG);
  assert(sig_query(DAG));
  hash_remove(sig_hash, DAG_ptr_of(DAG));
}

/*--------------------------------------------------------------*/

/* PF add signature of DAG from table */
static void
sig_enter(TDAG DAG)
{
  assert(DAG);
  assert(!sig_query(DAG));
  hash_insert(sig_hash, DAG_ptr_of(DAG));
}

/*
  --------------------------------------------------------------
  clue between terms functions
  --------------------------------------------------------------
*/

#ifdef EXPLAIN_CLASSIC
static inline void
clue_store(Tclue clue)
{
  assert(clue && clue->DAG[0] && clue->DAG[1]);
  stack_push(CC[clue->DAG[0]].stack_eq, clue);
  stack_push(CC[clue->DAG[1]].stack_eq, clue);
}

/*--------------------------------------------------------------*/

static inline void
clue_unstore(Tclue clue)
{
  assert(clue && clue->DAG[0] && clue->DAG[1]);
  assert(stack_top(CC[clue->DAG[0]].stack_eq) == clue);
  assert(stack_top(CC[clue->DAG[1]].stack_eq) == clue);
  stack_dec(CC[clue->DAG[0]].stack_eq);
  stack_dec(CC[clue->DAG[1]].stack_eq);
  clue_free(clue);
}
#endif

/*--------------------------------------------------------------*/

static inline void
clue_store_pred(Tclue clue)
{
  assert(clue && clue->DAG[0] && !clue->DAG[1]);
  assert(!CC[clue->DAG[0]].clue_pred);
  CC[clue->DAG[0]].clue_pred = clue;
}

/*--------------------------------------------------------------*/

static inline void
clue_unstore_pred(Tclue clue)
{
  assert(clue && clue->DAG[0] && !clue->DAG[1]);
  assert(CC[clue->DAG[0]].clue_pred == clue);
  CC[clue->DAG[0]].clue_pred = NULL;
  clue_free(clue);
}

/*--------------------------------------------------------------*/

static void
clue_dispatch(Tclue clue, unsigned dp_mask)
{
#ifdef DEBUG_CC
  my_message("CC: clue_dispatch, mask %d\n", dp_mask);
  clue_fprint(stderr, clue);
  fprintf(stderr, "\n");
#endif
  assert(dp_mask == dp_mask_arith);
  stack_push(CC_buffer, clue);
}

/*--------------------------------------------------------------*/

static TDAG
CC_abstract_DAG(TDAG DAG)
{
  unsigned i;
  TDAG * PDAG;
  MY_MALLOC(PDAG, DAG_arity(DAG) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(DAG); i++)
    PDAG[i] = CC_abstract(DAG_arg(DAG, i));
  return DAG_new(DAG_symb(DAG), DAG_arity(DAG), PDAG);
}

/*--------------------------------------------------------------*/

static void
CC_notify_merge(TDAG DAG1, TDAG DAG2, unsigned dp_mask)
{
  TUproof proof;
  proof.generic = NULL;
  clue_dispatch(clue_new_merge(DAG1, DAG2, 0, proof), dp_mask);
}


/*--------------------------------------------------------------*/

static void
CC_notify_inequality(TDAG DAG1, TDAG DAG2, Tclue clue, unsigned dp_mask)
{
  TUproof proof;
  proof.clue = clue;
  clue_dispatch(clue_new_inequality(DAG1, DAG2, 0, proof), dp_mask);
}

/*--------------------------------------------------------------*/

static void
CC_notify_abstract_term(TDAG DAG1, TDAG DAG2, unsigned dp_mask)
{
  clue_dispatch(clue_new_abstract(DAG1, DAG2), dp_mask);
}

/*--------------------------------------------------------------*/

static void
CC_notify_abstract_pred(TDAG DAG1, TDAG DAG2, unsigned polarity, 
                        Tclue clue, unsigned dp_mask)
{
  TUproof proof;
  proof.clue = clue;
  clue_dispatch(clue_new_abstract_pred(DAG1, DAG2, polarity, proof), dp_mask);
}

/*
  --------------------------------------------------------------
  Get equalities and all that
  --------------------------------------------------------------
*/

/* PF

   Classes contains DAGs that are equal according to some equalities.
   All those DAGs are linked by a spanning tree.  Those links are
   labeled by the reason of the equality which may be (1) it was in
   the original set of literals (2) it has been deduced by congruence
   (3) it has been deduced by an external DP
   
   Concretely, CC[DAG] for every DAG has a clue field which contains
   the edges of the spanning tree in the form of a list of clues.  For
   each clue in that list, there are two DAGs, one of which is A, the
   other being the other node of the edge.

   If DAG0 and DAG1 are in the same class, the equality of DAG0 and
   DAG1 is a direct consequence of reflexivity, transitivity, and
   symmetry of equality, and all the equalities DAG2 = DAG3, where
   DAG2 and DAG3 are src and dest nodes of edges on the path from DAG0
   and DAG1.

   To get the transitivity chain between DAG0 and DAG1, it suffice to
   number the edges from DAG0 on all the spanning tree, until DAG1 is
   found (function mark), and collect all clues by decreasing number
   from DAG1 to DAG0 (collect_tr_clues)

   mark, unmark, collect_tr_clues are help functions for
   collect_tr_equalities.
*/

#ifdef EXPLAIN_CLASSIC

static unsigned mark_shortcut = 1;

/*--------------------------------------------------------------*/

static void
mark_setend(TDAG DAG)
{
  mark_shortcut = 1;
  DAG_tmp_unsigned[DAG] = INT_MAX;
}

/*--------------------------------------------------------------*/

static void
mark(TDAG DAG, unsigned n)
{
  unsigned i;
  Tstack_clue stack_eq = CC[DAG].stack_eq;
  assert(n < UINT_MAX);
  DAG_tmp_unsigned[DAG] = n;
  for (i = stack_size(stack_eq); mark_shortcut && i; --i)
    {
      Tclue clue = stack_get(stack_eq, i - 1);
      TDAG dest;
      if (!clue->DAG[1])
	continue;
      dest = (clue->DAG[0] == DAG) ? clue->DAG[1] : clue->DAG[0];
      if (!DAG_tmp_unsigned[dest])
	mark(dest, n + 1);
      else if (DAG_tmp_unsigned[dest] == INT_MAX)
	{
	  DAG_tmp_unsigned[dest] = n + 1;
	  mark_shortcut = 0;
	}
      else
	assert(DAG_tmp_unsigned[dest] == n - 1);
    }
}

/*--------------------------------------------------------------*/

static void
unmark(TDAG DAG)
{
  unsigned i;
  Tstack_clue stack_eq = CC[DAG].stack_eq;
  /* assert ((unsigned)list_length(PCC->clue) == PCC->clue_nb); */
  DAG_tmp_unsigned[DAG] = 0;
  for (i = 0; i < stack_size(stack_eq); i++)
    {
      Tclue clue = stack_get(stack_eq, i);
      TDAG dest = clue->DAG[clue->DAG[0] == DAG];
      if (DAG_tmp_unsigned[dest])
	unmark(dest);
    }
}

/*--------------------------------------------------------------*/

static Tlist
collect_tr_clues(TDAG DAG)
{
  unsigned i;
  Tstack_clue stack_eq = CC[DAG].stack_eq;
  if (DAG_tmp_unsigned[DAG] == 1)
    return NULL;
  for (i = 0; i < stack_size(stack_eq); i++)
    {
      Tclue clue = stack_get(stack_eq, i);
      TDAG dest = clue->DAG[clue->DAG[0] == DAG];
      if (DAG_tmp_unsigned[dest] == DAG_tmp_unsigned[DAG] - 1)
	return list_add(collect_tr_clues(dest), clue);
    }
  my_error("collect_tr_clues: inconsistency\n");
  return NULL;
}

/*--------------------------------------------------------------*/

/* PF get clues that allow (by transitivity) to deduce equality
   between DAG0 and DAG1 */
static Tlist
collect_tr_equalities(TDAG DAG0, TDAG DAG1)
{
  Tlist clues;
  assert(DAG0);
  assert(DAG1);
  DAG_tmp_reserve();
  if (DAG0 == DAG1)
    return NULL;
  mark_setend(DAG1);
  mark(DAG0, 1);
  clues = collect_tr_clues(DAG1);
  unmark(DAG0);
  DAG_tmp_release();
  return clues;
}

/*--------------------------------------------------------------*/

#ifdef PROOF
/**
   \brief get clues that allow to deduce equality between DAG0 and
   DAG1 by transitivity
   \param DAG0 the first DAG
   \param DAG1 the second DAG
   \remark proof is reset to transitivity clause 
   \return the set of clues
 */
static Tlist
collect_equalities(TDAG DAG0, TDAG DAG1, Tproof_id * proof)
{
  Tlist tmp;
  assert(DAG0 && DAG1);
  assert(DAG_sort(DAG0) != SORT_BOOLEAN);
  *proof = 0;
  if (DAG0 == DAG1) /* PF reflexivity */
    {
      *proof = proof_clause(eq_reflexive, 1, DAG_dup(DAG_eq(DAG0, DAG1)));
      return NULL;
    }
  tmp = collect_tr_equalities(DAG0, DAG1);
  assert(tmp);
    /* Either list_length(tmp) == 1:
         clue comes from elsewhere (clue->origin != 0)
         or user (clue->type is CLUE_LITERAL, _MODEL_EQUALITY)
         or congruence
       or it is transitivity */
  if (list_cdr(tmp) != tmp) /* PF transitivity */
    {
      int orient;
      TDAG DAG = DAG0;
      Tstack_DAG lits;
      stack_INIT(lits);
      LIST_LOOP_BEGIN(tmp, Tclue, clue);
      orient = (DAG == clue->DAG[0]) ? 0 : 1;
      assert(clue->DAG[orient] == DAG);
      /* IMPROVE: orient may not be necessary, if orientation
	 (symmetry of eq) is handled by proof module */
      DAG = clue->DAG[1 - orient];
      stack_push(lits, DAG_dup(DAG_neq(clue->DAG[orient],
				       clue->DAG[1 - orient])));
      LIST_LOOP_END(tmp);
      stack_push(lits, DAG_dup(DAG_eq(DAG0, DAG1)));
      /* PF TODO I am surprised not to see resolution here */
      *proof = proof_clause_stack(eq_transitive, lits);
      stack_apply(lits, DAG_free);
      stack_free(lits);
    }
  return tmp;
}
#else
static Tlist
collect_equalities(TDAG DAG0, TDAG DAG1)
{
  Tlist tmp;
  assert(DAG_sort(DAG0) != SORT_BOOLEAN);
  if (DAG0 == DAG1) /* PF reflexivity */
    return NULL;
  tmp = collect_tr_equalities(DAG0, DAG1);
  assert(tmp);
  return tmp;
}
#endif
#endif /* EXPLAIN_CLASSIC */

#ifndef EXPLAIN_CLASSIC

static Tstack_DAG explain_pending;
static Tstack_clue explain_result;

/*--------------------------------------------------------------*/

/**
   \brief computes the nearest ancestor of DAG0 and DAG1
   \param DAG0 a term
   \param DAG1 a term in the same congruence class as DAG0
   \return the lowest DAG ancestor of DAG0 and DAG1 in the tree relation
   stored in the "next" field of DAGs */
static inline TDAG
explain_nearest_ancestor(TDAG DAG0, TDAG DAG1)
{
  TDAG D0, D1;
  assert(DAG0);
  assert(DAG1);
  DAG_tmp_reserve();
  D0 = DAG0;
  D1 = DAG1;
  while (!DAG_tmp_bool[D0])
    {
      DAG_tmp_bool[D0] = 1;
      D0 = CC[D0].next;
      if (D1)
	SWAP(TDAG, D0, D1);
      assert(D0);
    }
  assert(D0);
  while (DAG0 && DAG_tmp_bool[DAG0])
    {
      DAG_tmp_bool[DAG0] = 0;
      DAG0 = CC[DAG0].next;
    }
  while (DAG1 && DAG_tmp_bool[DAG1])
    {
      DAG_tmp_bool[DAG1] = 0;
      DAG1 = CC[DAG1].next;
    }
  DAG_tmp_release();
  return D0;
}

/*--------------------------------------------------------------*/

/**
   \brief stores in explain_pending the pairs of DAGs for which to
   compute congruence
   \param DAG0 a term
   \param DAG1 a term congruent to DAG0 */
static inline void
explain_congruence(TDAG DAG0, TDAG DAG1)
{
  unsigned i;
  assert(DAG_symb(DAG0) == DAG_symb(DAG1));
  assert(DAG_arity(DAG0) == DAG_arity(DAG1));
  for (i = 0; i < DAG_arity(DAG0); i++)
    {
      stack_push(explain_pending, DAG_arg(DAG0, i));
      stack_push(explain_pending, DAG_arg(DAG1, i));
    }
}

/*--------------------------------------------------------------*/

static TDAG DAG_delay = DAG_NULL;

/**
   \brief collect all clues from DAG0 to DAG1 in explain_result
   \param DAG0 a term
   \param DAG1 a term in the same congruence class as DAG0
   \remark the congruence leading to DAG1 in the path are not recorded but the
   first congruent term in the path congruent to DAG1 is stored in DAG_delay */
static inline void
explain_path(TDAG DAG0, TDAG DAG1)
{
  while (DAG0 != DAG1)
    {
      TDAG parent = CC[DAG0].next;
      if (CC[DAG0].clue)
	{
	  if (DAG_delay)
	    {
	      explain_congruence(DAG_delay, DAG0);
	      DAG_delay = DAG_NULL;
	    }
	  stack_push(explain_result, CC[DAG0].clue);
	}
      else if (!DAG_delay)
	DAG_delay = DAG0;
      DAG0 = parent;
    }
}

/*--------------------------------------------------------------*/

#ifndef PROOF
/**
   \brief collect all clues to explain that DAG0 = DAG1 in explain_result
   \param DAG0 a term
   \param DAG1 a term in the same congruence class as DAG0 */
static Tlist
collect_equalities(TDAG DAG0, TDAG DAG1)
{
  unsigned i;
  Tlist tmp = NULL;
  stack_push(explain_pending, DAG0);
  stack_push(explain_pending, DAG1);
  while (stack_size(explain_pending))
    {
      TDAG ancestor;
      TDAG tmp;
      DAG1 = stack_pop(explain_pending);
      DAG0 = stack_pop(explain_pending);
      ancestor = explain_nearest_ancestor(DAG0, DAG1);
      explain_path(DAG0, ancestor);
      tmp = DAG_delay;
      DAG_delay = DAG_NULL;
      explain_path(DAG1, ancestor);
      if (DAG_delay)
	{
	  explain_congruence(DAG_delay, tmp ? tmp : ancestor);
	  DAG_delay = DAG_NULL;
	}
      else if (tmp)
	explain_congruence(tmp, ancestor);
    }
#ifdef PEDANTIC
#warning temporary
#endif
  for (i = 0; i < stack_size(explain_result); i++)
    tmp = list_cons(stack_get(explain_result, i), tmp);
  stack_reset(explain_result);
  return tmp;
}

/*--------------------------------------------------------------*/

#else /* PROOF */

static Tlist
collect_equalities(TDAG DAG0, TDAG DAG1, Tproof_id * proof)
{
  if (DAG0 == DAG1) /* PF reflexivity */
    {
      *proof = proof_clause(eq_reflexive, 1, DAG_dup(DAG_eq(DAG0, DAG1)));
      return NULL;
    }  
#error NOT IMPLEMENTED
  return NULL;
}
#endif

static void
explain_init(void)
{
  stack_INIT(explain_pending);
  stack_INIT(explain_result);
}

/*--------------------------------------------------------------*/

static void
explain_done(void)
{
  stack_free(explain_pending);
  stack_free(explain_result);
}

#endif /* EXPLAIN_CLASSIC_UNDEF */

/*--------------------------------------------------------------*/

/* TODO: one too much function in the two next */

/* PF find the DAG that has its value set directly */
static TDAG
get_pred_value(TDAG DAG)
{
  DAG = class[DAG];
  while (DAG)
    if (CC[DAG].clue_pred)
      return DAG;
    else
      DAG = class_info[DAG].elem;
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

/* PF find the DAG that has its value set directly */
static Tclue
get_pred_value2(Tclass class0)
{
  TDAG tmp = class0;
  assert(tmp);
  while (tmp)
    if (CC[tmp].clue_pred)
      return CC[tmp].clue_pred;
    else
      tmp = class_info[tmp].elem;
  return NULL;
}

/*--------------------------------------------------------------*/

#ifdef PROOF
/**
   \brief gets all clues that imply the equalities (negated) in lits.
   As a side effect, resolve clause of id proof to eliminate those lits
   if no clue corresponding to it is given in the output.
   \author David Deharbe and Pascal Fontaine
   \param lits literals
   \param proof proof id of the clause
   \return the list of all clues that imply those literals by CC
   \remarks there may be repetitions
   \remarks only transitivity is used, there may be congruence clues in
   the result
   \remark the congruence clues should be resolved later (either in CC or in NO)
*/
static Tlist
CC_proof_resolve_congruence(Tstack_DAG lits, Tproof_id * proof)
{
  unsigned i, j;
  Tlist tmp;
  /* PF use lits again to get a list of non-redundant resolvers */
  DAG_tmp_reserve();
  for (i = 0, j = 0; i < lits->size; i++)
    {
      TDAG DAG = lits->data[i];
      if (DAG_tmp_bool[DAG])
	{
	  DAG_free(DAG);
	  continue;
	}
      DAG_tmp_bool[DAG] = 1;
      lits->data[j++] = lits->data[i];
    }
  assert(j);
  lits->size = j;
  for (i = 0; i < lits->size; i++)
    {
      assert(DAG_tmp_bool[lits->data[i]]);
      DAG_tmp_bool[lits->data[i]] = 0;
    }
  DAG_tmp_release();
  tmp = NULL;
  for (i = 0; i < lits->size; i++)
    {
      TDAG DAG = DAG_arg0(lits->data[i]);
      Tproof_id clause = 0;
      Tlist tmp2 = collect_equalities(DAG_arg0(DAG), DAG_arg1(DAG), &clause);
      tmp = list_merge(tmp, tmp2);
      if (clause)
	*proof = proof_bin_resolve(*proof, clause);
    }
  stack_apply(lits, DAG_free);
  stack_free(lits);
  return tmp;
}
#endif

/*--------------------------------------------------------------*/

static bool
clue_is_congruent_notmisc(Tclue clue)
{
  if (clue->type != CLUE_CONGRUENT || clue->misc == 1)
    return false;
  clue->misc = 1;
  return true;
}

/*--------------------------------------------------------------*/

static bool
clue_is_congruent_misc(Tclue clue)
{
  assert(clue->type != CLUE_CONGRUENT || clue->misc);
  return clue->type == CLUE_CONGRUENT;
}

/*--------------------------------------------------------------*/

#ifdef PROOF
/**
   \brief gets the list of non-congruent clues that imply all
   congruences in the given clues, and resolve clause with proof_id to
   eliminate those clues
   \author David Déharbe and Pascal Fontaine
   \param clues the list of clues
   \param proof_id pointer to the proof_id of the clause to eliminate clues
   \return the list of non-congruent clues that imply the given clues
   \remark after this function, the clause only has to be resolved
   with clauses from outside CC
*/
static Tlist
CC_remove_congruences(Tlist clues, Tproof_id * proof_id)
{
  Tlist congruences = NULL;
  if (!clues)
    return NULL;
  congruences = list_filter(clues, (TFtest) clue_is_congruent_notmisc);
  clues = list_remove_all(clues, (TFtest) clue_is_congruent_misc);

  while (congruences)
    {
      /* PF congruences with misc bit set will be resolved */
      Tclue clue = list_car(congruences);
      Tstack_DAG lits;
      Tlist tmp;
      unsigned i;
      Tproof_id proof_id2;
      stack_INIT(lits);
      assert(clue->type == CLUE_CONGRUENT && clue->misc &&
	      DAG_arity(clue->DAG[0]) == DAG_arity(clue->DAG[1]) &&
	      DAG_symb(clue->DAG[0]) == DAG_symb(clue->DAG[1]));
      for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
	stack_push(lits, DAG_dup(DAG_neq(DAG_arg(clue->DAG[0], i),
					DAG_arg(clue->DAG[1], i))));
      stack_push(lits, DAG_dup(DAG_eq(clue->DAG[0], clue->DAG[1])));
      proof_id2 = proof_clause_stack(eq_congruent, lits);
      DAG_free(stack_pop(lits));
      tmp = CC_proof_resolve_congruence(lits, &proof_id2);
      congruences =
	list_merge(congruences,
		   list_filter(tmp, (TFtest) clue_is_congruent_notmisc));
      clues =
	list_merge(clues,
		   list_remove_all(tmp, (TFtest) clue_is_congruent_misc));
      if (!*proof_id)
	*proof_id = proof_id2;
      else if (proof_id2)
	*proof_id = proof_bin_resolve(*proof_id, proof_id2);
      clue->misc = 0;
      congruences = list_remove(congruences);
    }
  return clues;
}
#else
static Tlist
CC_remove_congruences(Tlist clues)
{
  Tlist congruences = NULL;
  if (!clues)
    return NULL;
  congruences = list_filter(clues, (TFtest) clue_is_congruent_notmisc);
  clues = list_remove_all(clues, (TFtest) clue_is_congruent_misc);

  while (congruences)
    {
      /* PF congruences with misc bit set will be resolved */
      Tclue clue = list_car(congruences);
      Tlist tmp = NULL;
      unsigned i;
      assert(clue->type == CLUE_CONGRUENT && clue->misc &&
	      DAG_arity(clue->DAG[0]) == DAG_arity(clue->DAG[1]) &&
	      DAG_symb(clue->DAG[0]) == DAG_symb(clue->DAG[1]));
      for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
	tmp = list_merge(tmp, collect_equalities(DAG_arg(clue->DAG[0], i),
						 DAG_arg(clue->DAG[1], i)));
      congruences =
	list_merge(congruences,
		   list_filter(tmp, (TFtest) clue_is_congruent_notmisc));
      clues =
	list_merge(clues,
		   list_remove_all(tmp, (TFtest) clue_is_congruent_misc));
      clue->misc = 0;
      congruences = list_remove(congruences);
    }
  return clues;
}
#endif

/*--------------------------------------------------------------*/

static Tlist
CC_proof_abstract_term(Tclue clue)
{
  Tlist clues;
  assert(clue->type == CLUE_ABSTRACT_TERM);
  if (!class[clue->DAG[0]])
    {
      TDAG mid = sig_query(clue->DAG[0]);
      Tclue clue_congruent = clue_new_congruent(clue->DAG[0], mid);
#ifdef PROOF
      Tproof_id clause, clause2, clause3;
      clause = clause2 = clause3 = 0;
#endif
      assert(mid);
      assert(mid != clue->DAG[0]);
      assert(DAG_symb(mid) == DAG_symb(clue->DAG[0]));
      assert(DAG_arity(mid) == DAG_arity(clue->DAG[0]));
      assert(CC_abstract(mid) == CC_abstract(clue->DAG[1]));
      clues = list_one(clue_congruent);
      /* PF if this is not done here, I lose the oportunity to free the clue */
      clues = CC_remove_congruences(clues OPTC_PROOF(&clause));
      clue_free(clue_congruent);
      if (mid != clue->DAG[1])
	{
	  Tlist clues2 =
	    collect_equalities(mid, clue->DAG[1] OPTC_PROOF(&clause2));
#ifdef PROOF
	  Tstack_DAG lits;
	  stack_INIT(lits);
	  stack_push(lits,DAG_dup(DAG_neq(clue->DAG[0], mid)));
	  stack_push(lits, DAG_dup(DAG_neq(mid, clue->DAG[1])));
	  stack_push(lits, DAG_dup(DAG_eq(clue->DAG[0], clue->DAG[1])));
	  clause3 = proof_clause_stack(eq_transitive, lits);
	  clause = proof_bin_resolve(clause3, clause);
	  if (clause2)
	    clause = proof_bin_resolve(clause, clause2);
	  stack_apply(lits, DAG_free);
	  stack_free(lits);
#endif
	  clues = list_merge(clues, clues2);
	}
#ifdef PROOF
      clue->proof_id = clause;
#endif
      return clues;
    }
  if (clue->DAG[0] != clue->DAG[1])
    return collect_equalities(clue->DAG[0], clue->DAG[1]
			      OPTC_PROOF(&clue->proof_id));
  return NULL;
}

/*--------------------------------------------------------------*/

#define DAG_pol(A, B) ((A)?B:DAG_not(B))

#ifdef PROOF
static Tlist
CC_proof_abstract_pred(Tclue clue)
{
  unsigned i;
  Tlist tmp = NULL;
  Tstack_DAG lits;
  Tproof_id clause = 0;
  assert(clue->type == CLUE_ABSTRACT_PRED && !DEAD_NODE(clue->DAG[0]));
  assert(DAG_symb(clue->DAG[0]) == DAG_symb(clue->DAG[1]) &&
	  DAG_arity(clue->DAG[0]) == DAG_arity(clue->DAG[1]));
  if (clue->DAG[0] != clue->DAG[1])
    {
      stack_INIT(lits);
      for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
	stack_push(lits, DAG_dup(DAG_neq(DAG_arg(clue->DAG[0], i),
					 DAG_arg(clue->DAG[1], i))));
      stack_push(lits, DAG_dup(DAG_pol(1 - clue->polarity, clue->DAG[1])));
      stack_push(lits, DAG_dup(DAG_pol(clue->polarity, clue->DAG[0])));
      clause = proof_clause_stack(eq_congruent_pred, lits);
      DAG_free(stack_pop(lits));
      DAG_free(stack_pop(lits));
      tmp = CC_proof_resolve_congruence(lits, &clause);
    }
  clue->proof_id = clause;
  tmp = list_cons(clue->proof.clue, tmp);
  return tmp;
}
#else
static Tlist
CC_proof_abstract_pred(Tclue clue)
{
  unsigned i;
  Tlist tmp = NULL;
  assert(clue->type == CLUE_ABSTRACT_PRED && !DEAD_NODE(clue->DAG[0]));
  assert(DAG_symb(clue->DAG[0]) == DAG_symb(clue->DAG[1]) &&
	 DAG_arity(clue->DAG[0]) == DAG_arity(clue->DAG[1]));
  if (clue->DAG[0] != clue->DAG[1])
    for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
      tmp = list_merge(tmp, collect_equalities(DAG_arg(clue->DAG[0], i),
					       DAG_arg(clue->DAG[1], i)));
  tmp = list_cons(clue->proof.clue, tmp);
  return tmp;
}
#endif

/*--------------------------------------------------------------*/

static void
CC_proof_abstract_quant_aux(TDAG DAG1, TDAG DAG2, 
			    Tlist clues OPTC_PROOF(Tproof_id * Pproof))
{
  unsigned i;
  if (DAG1 == DAG2)
    return;
  if (symb_type(DAG_symb(DAG1)) == SYMB_VARIABLE)
    my_error("CC_proof_abstract_quant_aux: internal error\n");
  if (quantifier(DAG_symb(DAG1)))
    {
      assert(DAG_symb(DAG1) == DAG_symb(DAG2) &&
	     DAG_arity(DAG1) == DAG_arity(DAG2));
      CC_proof_abstract_quant_aux(DAG_argn(DAG1), DAG_argn(DAG2),
				  clues OPTC_PROOF(Pproof));
      return;
    }
  if (boolean_connector(DAG_symb(DAG1)) || DAG_symb(DAG1) == PREDICATE_EQ)
    {
      assert(DAG_symb(DAG1) == DAG_symb(DAG2) &&
	     DAG_arity(DAG1) == DAG_arity(DAG2));
      for (i = 0; i < DAG_arity(DAG1); i++)
	CC_proof_abstract_quant_aux(DAG_arg(DAG2, i), DAG_arg(DAG2, i),
				    clues OPTC_PROOF(Pproof));
      return;
    }
  if (DAG_ground(DAG1) && !DAG_quant(DAG1) && DAG_sort(DAG1) != SORT_BOOLEAN)
    {
      assert(DAG_ground(DAG2) && !DAG_quant(DAG2) &&
	     DAG_sort(DAG2) != SORT_BOOLEAN);
      list_merge(clues, collect_equalities(DAG1, DAG2
					   OPTC_PROOF(Pproof)));
      return;
    }
  assert(DAG_symb(DAG1) == DAG_symb(DAG2) &&
	 DAG_arity(DAG1) == DAG_arity(DAG2));
  for (i = 0; i < DAG_arity(DAG1); i++)
    CC_proof_abstract_quant_aux(DAG_arg(DAG1, i), DAG_arg(DAG2, i), clues
				 OPTC_PROOF(Pproof));
}

/*--------------------------------------------------------------*/

#ifdef PROOF
static Tlist
CC_proof_abstract_quant(Tclue clue)
{
  Tlist tmp;
  Tproof_id clause = 0;
  assert(clue->type == CLUE_ABSTRACT_QUANT);
  tmp = list_one(clue->proof.clue);
  CC_proof_abstract_quant_aux(clue->DAG[0], clue->DAG[1], tmp, &clause);
  clue->proof_id = clause;
  return tmp;
}
#else
static Tlist
CC_proof_abstract_quant(Tclue clue)
{
  Tlist tmp;
  assert(clue->type == CLUE_ABSTRACT_QUANT);
  tmp = list_one(clue->proof.clue);
  CC_proof_abstract_quant_aux(clue->DAG[0], clue->DAG[1], tmp);
  return tmp;
}
#endif

/*--------------------------------------------------------------*/

static Tlist
CC_proof_merge(Tclue clue)
{
  assert(clue->type == CLUE_MERGE);
  assert(class[clue->DAG[1]]);
  assert(CC_abstract(clue->DAG[0]) == CC_abstract(clue->DAG[1]));
  return collect_equalities(clue->DAG[0], clue->DAG[1]
			    OPTC_PROOF(&clue->proof_id));
}

/*--------------------------------------------------------------*/

static Tlist
CC_proof_implied_inequality(Tclue clue)
{
  Tclue clue2 = clue->proof.clue;
#ifdef PROOF
  Tstack_DAG lits;
  stack_INIT(lits);
  stack_push(lits, DAG_pol(1 - clue2->polarity, clue2->DAG[0]));
  stack_push(lits, DAG_neq(clue->DAG[0], clue->DAG[1]));
  clue->proof_id = proof_clause_stack(dl_generic, lits);
  stack_free(lits);
#endif
  return list_one(clue2);
}

/*--------------------------------------------------------------*/

static Tlist
CC_proof_inequality(Tclue clue)
{
#ifdef PROOF
  Tproof_id proof_id1, proof_id2;
  Tstack_DAG lits;
#endif
  Tclue clue2 = clue->proof.clue;
  Tlist tmp, tmp2;
  tmp = list_one(clue2);
  tmp2 = collect_equalities(clue2->DAG[0], clue->DAG[0]
			     OPTC_PROOF(&proof_id1));
  tmp = list_merge(tmp, tmp2);
  tmp2 = collect_equalities(clue2->DAG[1], clue->DAG[1]
			     OPTC_PROOF(&proof_id2));
  tmp = list_merge(tmp, tmp2);
#ifdef PROOF
  if (clue2->DAG[0] == clue->DAG[0] &&
      clue2->DAG[1] == clue->DAG[1])
    {
      assert(list_cdr(tmp) == tmp && list_car(tmp) == clue2);
      clue->proof_id = 0;
      return tmp;
    }
  stack_INIT(lits);
  stack_push(lits, DAG_dup(DAG_neq(clue2->DAG[0], clue->DAG[0])));
  stack_push(lits, DAG_dup(DAG_neq(clue->DAG[0], clue->DAG[1])));
  stack_push(lits, DAG_dup(DAG_neq(clue->DAG[1], clue2->DAG[1])));
  stack_push(lits, DAG_dup(DAG_eq(clue2->DAG[0], clue2->DAG[1])));
  clue->proof_id = proof_clause_stack(eq_transitive, lits);
  if (proof_id1)
    clue->proof_id = proof_bin_resolve(clue->proof_id, proof_id1);
  if (proof_id2)
    clue->proof_id = proof_bin_resolve(clue->proof_id, proof_id2);
#endif
  return tmp;
}

/*
  --------------------------------------------------------------
  Backtrack prototypes
  --------------------------------------------------------------
*/

static void backtrack_union(Tclass class0, Tclass class1, Tclue clue,
			    unsigned dp_mask, Tboolean_value boolean_value);
static void backtrack_anti_merge(Tclue clue);
static void backtrack_watch_eq(Tclue clue);
static void backtrack_DAG_add(TDAG DAG);
static void backtrack_sig_delete(TDAG DAG);
static void backtrack_sig_enter(TDAG DAG);
static void backtrack_predicate(Tclue clue);
static void backtrack_predicate_undef(Tclue clue);
static void backtrack_conflict_predicate(Tclue clue);
static void backtrack_dp_mask(TDAG DAG, unsigned mask);
static void backtrack_dp_mask_symb(Tsymb symb, unsigned mask);
static void backtrack_store_quantified(void);
static void backtrack_status(void);

/*
  --------------------------------------------------------------
  Conflicts
  --------------------------------------------------------------
*/

/* PF
   there may be 3 types of conflict detected by CC
   1. An inequality is found with both members in the same class (INEQ)
   2. Two predicate classes with different polarities are merged (COMP) 
   3. A predicate class is set to the opposite polarity (PRED)
*/

typedef enum Tconflict_type {NONE, INEQ, COMP, PRED} Tconflict_type;

static struct Tconflict
{
  Tconflict_type type;
  Tclue clue;
  Tclue clue2;
} conflict;

/*--------------------------------------------------------------*/

static void
conflict_inequality(Tclue clue)
{
  conflict.type = INEQ;
  conflict.clue = clue;
  status = UNSAT;
  backtrack_status();
}

/*--------------------------------------------------------------*/

static void
conflict_complementary(Tclue clue1, Tclue clue2)
{
  assert(clue1 && clue2 && clue1 != clue2);
  conflict.type = COMP;
  conflict.clue = clue1;
  conflict.clue2 = clue2;
  status = UNSAT;
  backtrack_status();
}

/*--------------------------------------------------------------*/

static void
conflict_set_predicate(Tclue clue)
{
  conflict.type = PRED;
  conflict.clue = clue;
  status = UNSAT;
  backtrack_status();
}

/*--------------------------------------------------------------*/

static Tlist
conflict_analyse_ineq(OPT_PROOF(Tproof_id * Pproof))
{
#if PROOF
  if (conflict.clue->DAG[0] == conflict.clue->DAG[1])
    {
      *Pproof = proof_clause(eq_reflexive, 1,
			     DAG_dup(DAG_eq(conflict.clue->DAG[0],
					    conflict.clue->DAG[0])));
      return list_one(conflict.clue);
    }
#endif
  return list_cons(conflict.clue,
		   collect_equalities(conflict.clue->DAG[0],
				      conflict.clue->DAG[1]
				      OPTC_PROOF(Pproof)));
}

/*--------------------------------------------------------------*/

static Tlist
conflict_analyse_pred(OPT_PROOF(Tproof_id * Pproof))
{
  Tclue clue = conflict.clue;
  unsigned i;
  Tlist tmp;
  TDAG DAG1;
  assert(!clue->DAG[1]);
  /* PF there should be an equality linking to another DAG with same sig */
#ifdef EXPLAIN_CLASSIC
  assert(stack_size(CC[clue->DAG[0]].stack_eq));
#endif
  
  tmp = list_one(clue);
  /* PF CC should not get both polarities of the same DAG */
  assert(!CC[clue->DAG[0]].clue_pred);
  DAG1 = get_pred_value(clue->DAG[0]);

  tmp = list_cons(CC[DAG1].clue_pred, tmp);
#ifdef PROOF
  {
    Tstack_DAG lits;
    stack_INIT(lits);
    for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
      stack_push(lits, DAG_dup(DAG_neq(DAG_arg(clue->DAG[0], i),
				       DAG_arg(DAG1, i))));
    stack_push(lits, DAG_dup(DAG_pol(1 - clue->polarity,
				     clue->DAG[0])));
    stack_push(lits, DAG_dup(DAG_pol(clue->polarity, DAG1)));
    *Pproof = proof_clause_stack(eq_congruent_pred, lits);
    DAG_free(stack_pop(lits));
    DAG_free(stack_pop(lits));
    tmp = list_merge(tmp, CC_proof_resolve_congruence(lits, Pproof));
  }
#else
  for (i = 0; i < DAG_arity(clue->DAG[0]); i++)
    tmp = list_merge(tmp, collect_equalities(DAG_arg(clue->DAG[0], i),
					     DAG_arg(DAG1, i)));
#endif
  return tmp;
}

/*--------------------------------------------------------------*/

#ifdef PROOF
static Tlist
conflict_analyse_comp(OPT_PROOF(Tproof_id * Pproof))
{
  TDAG DAG0, DAG1;
  Tclue clue;
  Tlist tmp;
  Tstack_DAG lits;
  unsigned i;
  /* PF CC should not get two complementary predicates */
  assert(conflict.clue->DAG[0] != conflict.clue2->DAG[0]);
  DAG0 = conflict.clue->DAG[0];
  DAG1 = conflict.clue2->DAG[0];
  stack_INIT(lits);
  for (i = 0; i < DAG_arity(DAG0); i++)
    stack_push(lits, DAG_dup(DAG_neq(DAG_arg(DAG0, i),
				     DAG_arg(DAG1, i))));
  tmp = list_new_args(CC[DAG0].clue_pred, CC[DAG1].clue_pred, NULL);
  clue = list_car(tmp);
  stack_push(lits, DAG_dup(DAG_pol(1 - clue->polarity, clue->DAG[0])));
  clue = list_car(list_cdr(tmp));
  stack_push(lits, DAG_dup(DAG_pol(1 - clue->polarity, clue->DAG[0])));
  *Pproof = proof_clause_stack(eq_congruent_pred, lits);
  DAG_free(stack_pop(lits));
  DAG_free(stack_pop(lits));
  /* PF conflict_analyse_comp may have been broken in rev 1632 */
  tmp = list_merge(tmp, CC_proof_resolve_congruence(lits, Pproof));
  return tmp;
}
#else
static Tlist
conflict_analyse_comp(void)
{
  unsigned i;
  TDAG DAG0, DAG1;
  Tlist tmp;
  /* PF CC should not get two complementary predicates */
  assert(conflict.clue->DAG[0] != conflict.clue2->DAG[0]);
  DAG0 = conflict.clue->DAG[0];
  DAG1 = conflict.clue2->DAG[0];
  tmp = list_cons(CC[DAG0].clue_pred, list_one(CC[DAG1].clue_pred));
  for (i = 0; i < DAG_arity(DAG0); i++)
    tmp = list_merge(tmp, collect_equalities(DAG_arg(DAG0, i),
					     DAG_arg(DAG1, i)));
  return tmp;
}
#endif /* PROOF */

/*--------------------------------------------------------------*/

static Tlist
conflict_analyse(OPT_PROOF(Tproof_id * Pproof))
{
  Tlist tmp;
  switch (conflict.type)
    {
    case INEQ:
      tmp = conflict_analyse_ineq(OPT_PROOF(Pproof));
      break;
    case COMP:
      tmp = conflict_analyse_comp(OPT_PROOF(Pproof));
      break;
    case PRED:
      tmp = conflict_analyse_pred(OPT_PROOF(Pproof));
      break;
    default:
      my_error("conflict_analyse: internal error\n");
      return NULL;
    }
  return CC_remove_congruences(tmp OPTC_PROOF(Pproof) );
}

/*--------------------------------------------------------------*/

static void
conflict_init(void)
{
  conflict.type = NONE;
  conflict.clue = NULL;
}

/*--------------------------------------------------------------*/

static void
conflict_done(void)
{
}

/*
  --------------------------------------------------------------
  Watch
  --------------------------------------------------------------
*/

static void
hint_eq(Tclue clue)
{
  bool_hint_add(clue->proof.lit);
}

/*--------------------------------------------------------------*/

static void
hint_pred(Tclass class0, Tboolean_value boolean_value)
{
  TDAG tmp = class0;
  while (tmp)
    {
      Tlit lit = DAG_to_lit(tmp);
      bool_hint_add((boolean_value == TRUE)?lit:lit_neg(lit));
      tmp = class_info[tmp].elem;
    }
}

/*--------------------------------------------------------------*/

static void
hint_pred_except(Tclass class0, Tboolean_value boolean_value, TDAG src)
{
  TDAG tmp = class0;
  while (tmp)
    {
      Tlit lit = DAG_to_lit(tmp);
      if (tmp != src)
	bool_hint_add((boolean_value == TRUE)?lit:lit_neg(lit));
      tmp = class_info[tmp].elem;
    }
}

/*--------------------------------------------------------------*/

static void
CC_watch_pred(TDAG DAG, Tlit lit)
{
  assert(DAG_to_lit(DAG) == lit);
}

/*--------------------------------------------------------------*/

static void
CC_watch_eq(Tclue clue)
{
  Tclass_info *Pclass0, *Pclass1;
  if (class[clue->DAG[0]] == class[clue->DAG[1]])
    hint_eq(clue);
  Pclass0 = CC_find(clue->DAG[0]);
  Pclass1 = CC_find(clue->DAG[1]);
  Pclass0->watch_eq = list_cons(clue, Pclass0->watch_eq);
  Pclass0->watch_eq_nb++;
  Pclass1->watch_eq = list_cons(clue, Pclass1->watch_eq);
  Pclass1->watch_eq_nb++;
  backtrack_watch_eq(clue);
}

/*--------------------------------------------------------------*/

static void
CC_dewatch_eq(Tclue clue)
{
  Tclass_info *Pclass = CC_find(clue->DAG[0]);
  assert(Pclass->watch_eq);
  assert(((Tclue)list_car(Pclass->watch_eq)) == clue);
  Pclass->watch_eq = list_remove(Pclass->watch_eq);
  Pclass->watch_eq_nb--;
  Pclass = CC_find(clue->DAG[1]);
  assert(Pclass->watch_eq);
  assert(((Tclue)list_car(Pclass->watch_eq)) == clue);
  Pclass->watch_eq = list_remove(Pclass->watch_eq);
  Pclass->watch_eq_nb--;
  clue_free(clue);
}

/*
  --------------------------------------------------------------
  Congruence classes functions
  --------------------------------------------------------------
*/

/* PF Merges classes for clue->DAG[0] and clue->DAG[1]
   returns the list of requested congruence applications */
static Tlist
CC_union(Tclue clue)
{
  Tlist tmp;
  Tlist combine;
  TDAG tmp_DAG;
  Tclass_info *Pclass0, *Pclass1;
  Tclass class0, class1;
  unsigned tmp_mask;
  class0 = class[clue->DAG[0]];
  class1 = class[clue->DAG[1]];
  Pclass0 = CC_find(clue->DAG[0]);
  Pclass1 = CC_find(clue->DAG[1]);
  assert(CC_find(Pclass0->DAG) == Pclass0);
  assert(CC_find(Pclass1->DAG) == Pclass1);
#ifdef DEBUG_CC
  my_message("CC: CC_union %p - %p\n", Pclass0, Pclass1);
  class_print(class0);
  class_print(class1);
  my_message("END\n", Pclass0, Pclass1);
  assert(Pclass0->pred_nb == list_length(Pclass0->pred));
  tmp = Pclass0->pred;
  LIST_LOOP_BEGIN(tmp, TDAG, DAG);
  assert(sig_query(DAG));
  LIST_LOOP_END(tmp);
  assert(Pclass1->pred_nb == list_length(Pclass1->pred));
  tmp = Pclass1->pred;
  LIST_LOOP_BEGIN(tmp, TDAG, DAG);
  assert(sig_query(DAG));
  LIST_LOOP_END(tmp);
#endif

  /* PF in case of predicates, check if same polarity */
  if (Pclass0->boolean_value != Pclass1->boolean_value)
    {
      if (Pclass0->boolean_value == UNDEFINED)
	hint_pred(class0, Pclass1->boolean_value);
      else if (Pclass1->boolean_value == UNDEFINED)
	hint_pred(class1, Pclass0->boolean_value);
      else
	conflict_complementary(get_pred_value2(class0),
			       get_pred_value2(class1));
    }
  /* PF check if union does not make inequality unsatisfiable */
  tmp = ((Pclass0->ineq_nb < Pclass1->ineq_nb)?Pclass0:Pclass1)->ineq;
  LIST_LOOP_BEGIN(tmp, Tclue, ineq);
  {
    Tclass class0b = class[ineq->DAG[0]];
    Tclass class1b = class[ineq->DAG[1]];
    if (((class0b == class0) && (class1b == class1)) ||
	((class1b == class0) && (class0b == class1)))
      conflict_inequality(ineq);
  }
  LIST_LOOP_END(tmp);

  /* PF check if union does not make watch equality true */
  tmp = ((Pclass0->watch_eq_nb < Pclass1->watch_eq_nb)?Pclass0:Pclass1)->watch_eq;
  LIST_LOOP_BEGIN(tmp, Tclue, watch_eq);
  {
    Tclass class0b = class[watch_eq->DAG[0]];
    Tclass class1b = class[watch_eq->DAG[1]];
    if (((class0b == class0) && (class1b == class1)) ||
	((class1b == class0) && (class0b == class1)))
      hint_eq(watch_eq);
  }
  LIST_LOOP_END(tmp);

  /* PF Pclass0 is the largest class */
  if (Pclass0->elem_nb < Pclass1->elem_nb)
    {
      SWAP(Tclass_info *, Pclass0, Pclass1);
      SWAP(Tclass, class0, class1);
    }

#ifndef EXPLAIN_CLASSIC
  {
    TDAG orig = clue->DAG[0];
    TDAG next = clue->DAG[1];
    Tclue clue2 = clue;
    if (class[orig] == class0)
      SWAP(TDAG, orig, next);
    do
      {
	TDAG tmp;
	SWAP(Tclue ,clue2, CC[orig].clue);
	tmp = CC[orig].next;
	CC[orig].next = next;
	next = orig;
	orig = tmp;
      }
    while (orig);
  }
#endif

  /* PF remove signatures of the smallest predecessors list */
  tmp = ((Pclass0->pred_nb < Pclass1->pred_nb) ? Pclass0 : Pclass1)->pred;
  LIST_LOOP_BEGIN_DAG(tmp, DAG0);
  {
    TDAG DAG = sig_query(DAG0);
    if (DAG)
      {
	sig_delete(DAG);
	backtrack_sig_delete(DAG);
      }
  }
  LIST_LOOP_END_DAG(tmp);

  /* PF update class for every element in Pclass1 */
  tmp_DAG = class1;
  while (tmp_DAG)
    {
      class[tmp_DAG] = class0;
      if (!class_info[tmp_DAG].elem)
	break;
      tmp_DAG = class_info[tmp_DAG].elem;
    }
  Pclass0->elem_nb += Pclass1->elem_nb;
  class_info[tmp_DAG].elem = Pclass0->elem;
  Pclass0->elem = class1;

  CLASS_LIST_RM(class1);

  /* PF With merge, inequalities of Pclass1 may now be relevant for new dps */
  tmp_mask = CC_mask & Pclass0->dp_mask & ~Pclass1->dp_mask;
  if (tmp_mask && status != UNSAT)
    {
      tmp = Pclass1->ineq; 
      LIST_LOOP_BEGIN(tmp, Tclue, ineq);
      {
	/* DD The merged class is Pclass0 */
	Tclass_info *Pclass0b = CC_find(ineq->DAG[0]);
	Tclass_info *Pclass1b = CC_find(ineq->DAG[1]);
	/* DD exactly one of Pclass0b or Pclass1b is merged class */
	assert((Pclass0b == Pclass0 && Pclass1b != Pclass0) ||
		(Pclass0b != Pclass0 && Pclass1b == Pclass0));
	if (Pclass1b == Pclass0)
	  SWAP(Tclass_info *, Pclass0b, Pclass1b);
	/* DD Pclass0b is merged class */
	assert(Pclass0b == Pclass0);
	/* DD Pclass1b is different from representative of merged class */
	tmp_mask = CC_mask & Pclass0->dp_mask & ~Pclass1->dp_mask &
	  Pclass1b->dp_mask & ~(1u << ineq->origin);
	if (tmp_mask)
	  CC_notify_inequality(Pclass0->DAG, Pclass1b->DAG, ineq, tmp_mask);
      }
      LIST_LOOP_END(tmp);
    }
  /* PF the other case */
  tmp_mask = CC_mask & Pclass1->dp_mask & ~Pclass0->dp_mask;
  if (tmp_mask && status != UNSAT)
    {
      tmp = Pclass0->ineq;
      LIST_LOOP_BEGIN(tmp, Tclue, ineq);
      {
	/* DD The merged class is Pclass0 */
	Tclass_info *Pclass0b = CC_find(ineq->DAG[0]);
	Tclass_info *Pclass1b = CC_find(ineq->DAG[1]);
	/*	  my_DAG_message("handling inequality\n");
		  clue_print2(ineq); */
	/* DD exactly one of Pclass0b or Pclass1b is merged class */
	assert((Pclass0b == Pclass0 && Pclass1b != Pclass0) ||
		(Pclass0b != Pclass0 && Pclass1b == Pclass0));
	if (Pclass1b == Pclass0)
	  SWAP(Tclass_info *, Pclass0b, Pclass1b);
	/* DD Pclass0b is merged class */
	assert(Pclass0b == Pclass0);
	tmp_mask = CC_mask & Pclass1->dp_mask & ~Pclass0->dp_mask &
	  Pclass1b->dp_mask & ~(1u << ineq->origin);
	if (tmp_mask)
	  CC_notify_inequality(Pclass1->DAG, Pclass1b->DAG, ineq, tmp_mask);
      }
      LIST_LOOP_END(tmp);
    }

  Pclass0->ineq_nb += Pclass1->ineq_nb;
  Pclass0->ineq = list_merge(Pclass0->ineq, Pclass1->ineq);
  Pclass0->watch_eq_nb += Pclass1->watch_eq_nb;
  Pclass0->watch_eq = list_merge(Pclass0->watch_eq, Pclass1->watch_eq);
#ifdef EXPLAIN_CLASSIC
  clue_store(clue);
#endif
  backtrack_union(class0, class1, clue,
		  Pclass0->dp_mask, Pclass0->boolean_value);

  /* PF reenter signatures of the smaller predecessors list */
  /* PF   first ensure Pclass0 has largest predecessor list */
  if (Pclass0->pred_nb < Pclass1->pred_nb)
    {
      SWAP(TDAG, Pclass0->DAG, Pclass1->DAG);
      SWAP(unsigned, Pclass0->pred_nb, Pclass1->pred_nb);
      SWAP(Tlist, Pclass0->pred, Pclass1->pred);
      tmp_mask = CC_mask & Pclass0->dp_mask & ~Pclass1->dp_mask;
    }
  else
    tmp_mask = CC_mask & Pclass1->dp_mask & ~Pclass0->dp_mask;
  if (tmp_mask)
    CC_notify_merge(Pclass1->DAG, Pclass0->DAG, tmp_mask);

  if (Pclass0->boolean_value == UNDEFINED)
    Pclass0->boolean_value = Pclass1->boolean_value;
  /* PF inform DPs, if not second order equality */
  tmp_mask = CC_mask & Pclass0->dp_mask & Pclass1->dp_mask;
  if (clue->type != CLUE_MODEL_EQUALITY)
    tmp_mask &= ~(1u << clue->origin);
  if (DAG_sort(Pclass0->DAG) != SORT_BOOLEAN && tmp_mask)
    CC_notify_merge(Pclass1->DAG, Pclass0->DAG, tmp_mask);

  Pclass0->dp_mask |= Pclass1->dp_mask;

  /* PF   then inspect every predecessor; */
  tmp = Pclass1->pred;
  combine = NULL;
  LIST_LOOP_BEGIN_DAG(tmp, DAG1);
  {
    TDAG DAG2 = sig_query(DAG1);
    if (DAG2)
      {
	if (class[DAG1] != class[DAG2])
	  combine = list_add(combine, clue_new_congruent(DAG1, DAG2));
      }
    else
      {
	sig_enter(DAG1);
	backtrack_sig_enter(DAG1);
      }
  }
  LIST_LOOP_END_DAG(tmp);
  Pclass0->pred_nb += Pclass1->pred_nb;
  Pclass0->pred = list_merge(Pclass0->pred, Pclass1->pred);

  assert(CC_find(Pclass0->DAG) == Pclass0);
#ifdef DEBUG_CC
  tmp = Pclass0->pred;
  LIST_LOOP_BEGIN(tmp, TDAG, DAG);
  assert(sig_query(DAG));
  LIST_LOOP_END(tmp);
  my_message("CC: CC_union Final\n", Pclass0, Pclass1);
  class_print(class0);
  my_message("END\n", Pclass0, Pclass1);
#endif
  return combine;
}

/*--------------------------------------------------------------*/

static void
CC_desunion(Tclass class0, Tclass class1, Tclue clue,
	    unsigned dp_mask, Tboolean_value boolean_value)
{
  unsigned i, j;
  bool switched;
  TDAG tmp_DAG;
  Tclass_info * Pclass0 = class_info + class0;
  Tclass_info * Pclass1 = class_info + class1;
  assert(class[Pclass0->DAG] == class0);
  assert(class[clue->DAG[0]] == class0);
  assert(Pclass0->elem_nb >= Pclass1->elem_nb);
#ifdef DEBUG_CC
  my_message("CC_desunion: initial:\n");
  class_print(class0);
  class_print(class1);
  assert(Pclass1->elem_nb <= list_length(Pclass1->elem));
  list = Pclass1->elem;
  for (i = 0, j = Pclass1->elem_nb; i < j; i++, list = list_cdr(list))
    my_DAG_message("CC: class %d->%d - %D\n", class0, class1,
		   DAG_of_ptr(list_car(list)));
#endif
  assert(class_info[class0].elem = class1);
  tmp_DAG = class1;
  i = 0;
  j = Pclass1->elem_nb;
  while (1)
    {
      class[tmp_DAG] = class1;
      i++;
      if (i == j)
	break;
      tmp_DAG = class_info[tmp_DAG].elem;
    }
  CLASS_LIST_ADD(class1);
  assert(Pclass0->elem_nb > Pclass1->elem_nb);
  Pclass0->elem_nb -= Pclass1->elem_nb;
  Pclass0->elem = class_info[tmp_DAG].elem;
  class_info[tmp_DAG].elem = DAG_NULL;

  Pclass0->ineq_nb -= Pclass1->ineq_nb;
  Pclass0->ineq = list_anti_merge(Pclass0->ineq, Pclass1->ineq);
  Pclass0->watch_eq_nb -= Pclass1->watch_eq_nb;
  Pclass0->watch_eq = list_anti_merge(Pclass0->watch_eq, Pclass1->watch_eq);

#ifdef EXPLAIN_CLASSIC
  clue_unstore(clue);
#else
  i = (CC[clue->DAG[0]].next != clue->DAG[1]);
  assert(CC[clue->DAG[i]].next == clue->DAG[!i]);
  CC[clue->DAG[i]].next = 0;
  CC[clue->DAG[i]].clue = NULL;
  clue_free(clue);
#endif

  /* PF switch classes to minimalize future work */
  if (class[Pclass0->DAG] == class1)
    {
      SWAP(TDAG, Pclass0->DAG, Pclass1->DAG);
      switched = true;
    }
  else
    switched = false;

  assert(Pclass0->pred_nb >= Pclass1->pred_nb);
  Pclass0->pred_nb -= Pclass1->pred_nb;
  Pclass0->pred = list_anti_merge(Pclass0->pred, Pclass1->pred);
  assert((unsigned)list_length(Pclass0->pred) == Pclass0->pred_nb);
  assert((unsigned)list_length(Pclass1->pred) == Pclass1->pred_nb);
  if (switched)
    {
      SWAP(unsigned, Pclass0->pred_nb, Pclass1->pred_nb);
      SWAP(Tlist, Pclass0->pred, Pclass1->pred);
    }
  Pclass0->dp_mask = dp_mask;
  Pclass0->boolean_value = boolean_value;
  assert(Pclass0 != Pclass1);
  assert(class[Pclass0->DAG] == class0);
  assert(class[Pclass1->DAG] == class1);
#ifdef DEBUG_CC
  my_message("final:\n");
  class_print(class0);
  class_print(class1);
  my_message("CC: CC_desunion %p - %p\n", Pclass0, Pclass1);
#endif
}

/*
  --------------------------------------------------------------
  Main functions
  --------------------------------------------------------------
*/

static void
CC_merge(Tclue clue)
{
  Tlist combine;
  Tclass class0, class1;
  assert(clue->type == CLUE_LITERAL ||
	  clue->type == CLUE_MERGE ||
	  clue->type == CLUE_MODEL_EQUALITY ||
	  clue->type == CLUE_CONGRUENT);
  combine = list_one(clue);
  while (combine != NULL && status != UNSAT)
    {
      clue = list_car(combine);
      combine = list_remove(combine);
      assert(clue->DAG[1] && clue->polarity);
      class0 = class[clue->DAG[0]];
      class1 = class[clue->DAG[1]];
      assert(class0);
      assert(class1);
      if (class0 == class1)
	clue_free(clue);
      else
	combine = list_merge(combine, CC_union(clue));
    }
  while (combine)
    {
      assert(status == UNSAT);
      clue_free(list_car(combine));
      combine = list_remove(combine);
    }
}

/*--------------------------------------------------------------*/

static void
CC_anti_merge(Tclue clue)
{
  Tclass_info *Pclass0 = CC_find(clue->DAG[0]);
  Tclass_info *Pclass1 = CC_find(clue->DAG[1]);
  if (Pclass0 == Pclass1)
    conflict_inequality(clue);
  else if (CC_mask & Pclass0->dp_mask & Pclass1->dp_mask &
	   ~(1u << clue->origin))
    CC_notify_inequality(Pclass0->DAG,
			 Pclass1->DAG,
			 clue,
			 CC_mask & Pclass0->dp_mask &
			 Pclass1->dp_mask & ~(1u << clue->origin));
  Pclass0->ineq = list_cons(clue, Pclass0->ineq);
  Pclass0->ineq_nb++;
  Pclass1->ineq = list_cons(clue, Pclass1->ineq);
  Pclass1->ineq_nb++;
  backtrack_anti_merge(clue);
}

/*--------------------------------------------------------------*/

static void
CC_desanti_merge(Tclue clue)
{
  Tclass_info *Pclass0 = CC_find(clue->DAG[0]);
  assert(Pclass0->ineq);
  assert(((Tclue)list_car(Pclass0->ineq)) == clue);
  Pclass0->ineq = list_remove(Pclass0->ineq);
  Pclass0->ineq_nb--;
  Pclass0 = CC_find(clue->DAG[1]);
  assert(Pclass0->ineq);
  assert(((Tclue)list_car(Pclass0->ineq)) == clue);
  Pclass0->ineq = list_remove(Pclass0->ineq);
  Pclass0->ineq_nb--;
  clue_free(clue);
}

/*--------------------------------------------------------------*/

static void
CC_set_predicate(Tclue clue)
{
  Tclass_info * Pclass0 = CC_find(clue->DAG[0]);
  assert(clue->type == CLUE_LITERAL && !clue->DAG[1]);
  if (Pclass0->boolean_value == UNDEFINED)
    {
      Pclass0->boolean_value = clue->polarity ? TRUE : FALSE;
      hint_pred_except(class[clue->DAG[0]],
		       clue->polarity == 0 ? FALSE : TRUE, 
                       clue->DAG[0]);
      clue_store_pred(clue);
      if (CC_mask & Pclass0->dp_mask)
	/* PF inform DPs of new predicate (with polarity) */
	CC_notify_abstract_pred(CC_abstract_DAG(clue->DAG[0]),
				clue->DAG[0],
				clue->polarity,
				clue,
				CC_mask & Pclass0->dp_mask);
      backtrack_predicate_undef(clue);
      return;
    }
  /* PF: TODO We can discard the clue here, but this does not hurt
     Is the supplementary information useful? */
  if ((clue->polarity && CC_find(clue->DAG[0])->boolean_value == TRUE) ||
      (!clue->polarity && CC_find(clue->DAG[0])->boolean_value == FALSE))
    {
      clue_store_pred(clue);
      backtrack_predicate(clue);
      return;
    }
  if ((clue->polarity && CC_find(clue->DAG[0])->boolean_value == FALSE) ||
      (!clue->polarity && CC_find(clue->DAG[0])->boolean_value == TRUE))
    {
      conflict_set_predicate(clue);
      backtrack_conflict_predicate(clue);
    }
}

/*--------------------------------------------------------------*/

static void
CC_unset_predicate(Tclue clue)
{
  clue_unstore_pred(clue);
}

/*--------------------------------------------------------------*/

static void
CC_unset_predicate_undef(Tclue clue)
{
  CC_find(clue->DAG[0])->boolean_value = UNDEFINED;
  clue_unstore_pred(clue);
}

/*
  --------------------------------------------------------------
  Add DAGs in the game
  --------------------------------------------------------------
*/

static void DAG_add(TDAG DAG);

/**
 \brief Sets bit to the masks of the classes of (largest) ground terms nested in quantified 
 formulas and to function and predicate symbols that are directly or indirectly applied to 
 quantified variables.
 \note Backtrackable
 */
static void
DAG_add_q(TDAG DAG)
{
  unsigned i;
  if (symb_type(DAG_symb(DAG)) == SYMB_VARIABLE)
    return;
  if (quantifier(DAG_symb(DAG)))
    {
      DAG_add_q(DAG_argn(DAG));
      return;
    }
  if (boolean_connector(DAG_symb(DAG)) || DAG_symb(DAG) == PREDICATE_EQ)
    {
      for (i = 0; i < DAG_arity(DAG); i++)
	DAG_add_q(DAG_arg(DAG, i));
      return;
    }
  if (DAG_ground(DAG) && !DAG_quant(DAG) && DAG_sort(DAG) != SORT_BOOLEAN)
    {
      Tclass_info * Pclass0;
      DAG_add(DAG);
      Pclass0 = CC_find(DAG);
      if (CC_mask_quantified & ~Pclass0->dp_mask)
	{
	  backtrack_dp_mask(class[DAG], Pclass0->dp_mask);
	  Pclass0->dp_mask |= CC_mask_quantified;
	}
      return;
    }
  /* term with quantified subterms and/or quantified vars */
  if (~symb_dp_mask(DAG_symb(DAG)) & CC_mask_quantified)
    {
      backtrack_dp_mask_symb(DAG_symb(DAG), symb_dp_mask(DAG_symb(DAG)));
      symb_dp_mask(DAG_symb(DAG)) |= CC_mask_quantified;
      assert(!(CC_mask & CC_mask_quantified));
#ifdef DEBUG_CC
      my_DAG_message("CC: DAG add q (mask, DAG) : %d %D\n", symb_dp_mask(DAG_symb(DAG)), DAG);
#endif
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_add_q(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

static void
DAG_add(TDAG DAG)
{
  unsigned i;
  assert(DAG);
  assert(symb_type(DAG_symb(DAG)) != SYMB_VARIABLE);
  if (class[DAG])
    return;
  /* PF exclude some things from congruence closure computation */
  if (binder(DAG_symb(DAG)) || DAG_symb(DAG) == FUNCTION_ITE)
    my_error("Strange symbol in congruence closure\n");
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_add(DAG_arg(DAG, i));
  /* PF TODO: perhaps look for propositions,
     that can simply be discarded??? */
  class_info[DAG].elem_nb = 1;
  class_info[DAG].elem = DAG_NULL;
  assert(class_info[DAG].DAG = DAG);
  class_info[DAG].dp_mask = symb_dp_mask(DAG_symb(DAG));
  class[DAG] = DAG;
  CLASS_LIST_ADD(DAG);
  /* DD+PF avoid redundant sending of information:
     predicate are sent with polarity in CC_set_predicate */
  if (DAG_sort(DAG) != SORT_BOOLEAN && (symb_dp_mask(DAG_symb(DAG)) & CC_mask))
    CC_notify_abstract_term(CC_abstract_DAG(DAG), CC_abstract(DAG),
			    symb_dp_mask(DAG_symb(DAG)) & CC_mask);
  if (DAG_arity(DAG) && !DEAD_NODE(DAG))
    {
      TDAG DAG2;
      /* TODO: is it really necessary to add in parent lists,
	 in case there already exists a DAG with the same signature? */
      for (i = 0; i < DAG_arity(DAG); i++)
	{
	  Tclass_info * Pclass0 = CC_find(DAG_arg(DAG, i));
	  assert(Pclass0);
	  Pclass0->pred_nb++;
	  Pclass0->pred = list_cons(DAG_ptr_of(DAG), Pclass0->pred);
	  if (symb_dp_mask(DAG_symb(DAG)) & ~Pclass0->dp_mask)
	    {
	      unsigned dp_mask = symb_dp_mask(DAG_symb(DAG)) &
                ~Pclass0->dp_mask;
	      Tlist tmp;
	      backtrack_dp_mask(class[DAG_arg(DAG, i)], Pclass0->dp_mask);
	      Pclass0->dp_mask |= symb_dp_mask(DAG_symb(DAG));
	      tmp = Pclass0->ineq;
	      LIST_LOOP_BEGIN(tmp, Tclue, ineq);
	      {
		Tclass_info *Pclass0b = CC_find(ineq->DAG[0]);
		Tclass_info *Pclass1b = CC_find(ineq->DAG[1]);
		if (CC_mask & dp_mask & Pclass0b->dp_mask &
		    Pclass1b->dp_mask & ~(1u << ineq->origin))
		  CC_notify_inequality
		    (Pclass0b->DAG, Pclass1b->DAG, ineq,
		     Pclass0b->dp_mask & Pclass1b->dp_mask &
		     dp_mask & CC_mask & ~(1u << ineq->origin));
	      }
	      LIST_LOOP_END(tmp);
	    }
	}
      backtrack_DAG_add(DAG);
      if ((DAG2 = sig_query(DAG)))
	CC_merge(clue_new_congruent(DAG, DAG2));
      else
	{
	  backtrack_sig_enter(DAG);
	  sig_enter(DAG);
	}
    }
  /* DD+PF TODO: certainly there exists a cleaner test */
  else if (!DAG_arity(DAG))
    {
      stack_push(zero_arity, DAG);
      backtrack_DAG_add(DAG);
    }
  /* DD TODO: collapse the last two branches */
  else if (DAG_sort(DAG) == SORT_BOOLEAN && DEAD_NODE(DAG))
    backtrack_DAG_add(DAG);
  else
    backtrack_DAG_add(DAG);
}

/*--------------------------------------------------------------*/

static void
DAG_remove(TDAG DAG)
{
  unsigned i;
  Tclass_info *Pclass;
  assert(class[DAG]);
  if (!DEAD_NODE(DAG))
    for (i = 0; i < DAG_arity(DAG); i++)
      {
	Pclass = CC_find(DAG_arg(DAG, i));
	assert(Pclass->pred_nb && DAG_of_ptr(list_car(Pclass->pred)) == DAG);
	Pclass->pred_nb--;
	Pclass->pred = list_remove(Pclass->pred);
      }
  CLASS_LIST_RM(DAG);
  Pclass = CC_find(DAG);
  assert(Pclass->elem_nb == 1);
  assert(Pclass->elem == DAG_NULL);
  assert(Pclass->pred_nb == 0);
  assert(!Pclass->pred);
  assert(Pclass->ineq_nb == 0);
  assert(Pclass->watch_eq_nb == 0);
  Pclass->elem_nb = 0;
  Pclass->dp_mask = 0;
  class[DAG] = 0;
  if (!DAG_arity(DAG))
    {
      assert(stack_top(zero_arity) == DAG);
      stack_dec(zero_arity);
    }
  DAG_free(DAG);
}

/*
  --------------------------------------------------------------
  Backtracking functions
  --------------------------------------------------------------
*/

enum {CC_UNION = UNDO_CC,
      CC_ANTI_MERGE,
      CC_WATCH_EQ,
      CC_DAG_ADD,
      CC_SIG_DEL,
      CC_SIG_ENTER,
      CC_PRED,
      CC_PRED_UNDEF,
      CC_CONFLICT_PRED,
      CC_DP_MASK,
      CC_DP_MASK_SYMB,
      CC_STORE_QUANTIFIED,
      CC_STATUS};

/* TODO
   backtrack_union (Tclass_info * Pclass0, Tclass_info * Pclass1, Tclue clue, unsigned dp_mask)
   -->
   backtrack_union (Tclass_info * Pclass1, Tclue clue, unsigned dp_mask)
   since Pclass0 can be deduced from clue,
   and reuse 1 word
*/
typedef struct TBTcell
{
  union {
    TDAG DAG;
    Tsymb symb;
  } info[2];
  Tclue clue;
  unsigned mask;
  Tboolean_value boolean_value;
} TBTcell;

/*--------------------------------------------------------------*/

static void
backtrack_union(Tclass class0, Tclass class1, Tclue clue,
		unsigned mask, Tboolean_value boolean_value)
{
  TBTcell *PBTcell = (TBTcell *)undo_push(CC_UNION);
  PBTcell->info[0].DAG = class0;
  PBTcell->info[1].DAG = class1;
  PBTcell->clue = clue;
  PBTcell->mask = mask;
  PBTcell->boolean_value = boolean_value;
}

/*--------------------------------------------------------------*/

static void
backtrack_anti_merge(Tclue clue)
{
  (*(Tclue *)undo_push(CC_ANTI_MERGE)) = clue;
}

/*--------------------------------------------------------------*/

static void
backtrack_watch_eq(Tclue clue)
{
  (*(Tclue *)undo_push(CC_WATCH_EQ)) = clue;
}

/*--------------------------------------------------------------*/

static void
backtrack_DAG_add(TDAG DAG)
{
  /* TODO do not understand the idea of having DAG_dup here.
     Does not seem logical */
  (*(TDAG *)undo_push(CC_DAG_ADD)) = DAG_dup(DAG);
}

/*--------------------------------------------------------------*/

static void
backtrack_sig_delete(TDAG DAG)
{
  (*(TDAG *)undo_push(CC_SIG_DEL)) = DAG;
}

/*--------------------------------------------------------------*/

static void
backtrack_sig_enter(TDAG DAG)
{
  (*(TDAG *)undo_push(CC_SIG_ENTER)) = DAG;
}

/*--------------------------------------------------------------*/

static void
backtrack_predicate(Tclue clue)
{
  (*(Tclue *)undo_push(CC_PRED)) = clue;
}

/*--------------------------------------------------------------*/

static void
backtrack_predicate_undef(Tclue clue)
{
  (*(Tclue *)undo_push(CC_PRED_UNDEF)) = clue;
}

/*--------------------------------------------------------------*/

static void
backtrack_conflict_predicate(Tclue clue)
{
  (*(Tclue *)undo_push(CC_CONFLICT_PRED)) = clue;
}

/*--------------------------------------------------------------*/

static void
backtrack_dp_mask(TDAG DAG, unsigned mask)
{
  TBTcell *PBTcell = (TBTcell *)undo_push(CC_DP_MASK);
  PBTcell->info[0].DAG = DAG;
  PBTcell->mask = mask;
#ifdef DEBUG
  PBTcell->info[1].DAG = DAG_NULL;
  PBTcell->clue = NULL;
#endif
}

/*--------------------------------------------------------------*/

static void
backtrack_dp_mask_symb(Tsymb symb, unsigned mask)
{
  TBTcell *PBTcell = (TBTcell *)undo_push(CC_DP_MASK_SYMB);
  PBTcell->info[0].symb = symb;
  PBTcell->mask = mask;
#ifdef DEBUG
  PBTcell->info[1].DAG = DAG_NULL;
  PBTcell->clue = NULL;
#endif
}

/*--------------------------------------------------------------*/

static void
backtrack_store_quantified(void)
{
  undo_push(CC_STORE_QUANTIFIED);
}

/*--------------------------------------------------------------*/

static void
backtrack_status(void)
{
  undo_push(CC_STATUS);
}

/*--------------------------------------------------------------*/

static void
CC_hook_union(TBTcell * PBTcell)
{
  CC_desunion(PBTcell->info[0].DAG, PBTcell->info[1].DAG,
	      PBTcell->clue, PBTcell->mask, PBTcell->boolean_value);
}

/*--------------------------------------------------------------*/

static void
CC_hook_anti_merge(Tclue * Pclue)
{
  CC_desanti_merge(*Pclue);
}

/*--------------------------------------------------------------*/

static void
CC_hook_watch_eq(Tclue * Pclue)
{
  CC_dewatch_eq(*Pclue);
}

/*--------------------------------------------------------------*/

static void
CC_hook_DAG_add(TDAG * PDAG)
{
  DAG_remove(*PDAG);
}

/*--------------------------------------------------------------*/

static void
CC_hook_sig_del(TDAG * PDAG)
{
  sig_enter(*PDAG);
}

/*--------------------------------------------------------------*/

static void
CC_hook_sig_add(TDAG * PDAG)
{
  sig_delete(*PDAG);
}

/*--------------------------------------------------------------*/

static void
CC_hook_set_predicate(Tclue * Pclue)
{
  CC_unset_predicate(*Pclue);
}

/*--------------------------------------------------------------*/

static void
CC_hook_set_predicate_undef(Tclue * Pclue)
{
  CC_unset_predicate_undef(*Pclue);
}

/*--------------------------------------------------------------*/

static void
CC_hook_conflict_pred(Tclue * Pclue)
{
  clue_free(*Pclue);
}

/*--------------------------------------------------------------*/

static void
CC_hook_dp_mask(TBTcell * PBTcell)
{
  assert(class[PBTcell->info[0].DAG] == PBTcell->info[0].DAG);
  CC_find(PBTcell->info[0].DAG)->dp_mask = PBTcell->mask;
}

/*--------------------------------------------------------------*/

static void
CC_hook_symb_dp_mask(TBTcell * PBTcell)
{
  symb_dp_mask(PBTcell->info[0].symb) = PBTcell->mask;
}

/*--------------------------------------------------------------*/

static void
CC_hook_store_quantified(void)
{
  DAG_free(stack_pop(CC_quantified));
}

/*--------------------------------------------------------------*/

static void
CC_hook_status(void)
{
  status = SAT;
}

/*--------------------------------------------------------------*/

static void
backtrack_init(void)
{
  undo_set_hook(CC_UNION, (Tundo_hook)CC_hook_union, sizeof(TBTcell));
  undo_set_hook(CC_ANTI_MERGE, (Tundo_hook)CC_hook_anti_merge, sizeof(Tclue));
  undo_set_hook(CC_WATCH_EQ, (Tundo_hook)CC_hook_watch_eq, sizeof(Tclue));
  undo_set_hook(CC_DAG_ADD, (Tundo_hook)CC_hook_DAG_add, sizeof(TDAG));
  undo_set_hook(CC_SIG_DEL, (Tundo_hook)CC_hook_sig_del, sizeof(TDAG));
  undo_set_hook(CC_SIG_ENTER, (Tundo_hook)CC_hook_sig_add, sizeof(TDAG));
  undo_set_hook(CC_PRED, (Tundo_hook)CC_hook_set_predicate, sizeof(Tclue));
  undo_set_hook(CC_PRED_UNDEF, (Tundo_hook)CC_hook_set_predicate_undef, sizeof(Tclue));
  undo_set_hook(CC_CONFLICT_PRED, (Tundo_hook)CC_hook_conflict_pred, sizeof(Tclue));
  undo_set_hook(CC_DP_MASK, (Tundo_hook)CC_hook_dp_mask, sizeof(TBTcell));
  undo_set_hook(CC_DP_MASK_SYMB, (Tundo_hook)CC_hook_symb_dp_mask, sizeof(TBTcell));
  undo_set_hook(CC_STORE_QUANTIFIED, (Tundo_hook)CC_hook_store_quantified, 0);
  undo_set_hook(CC_STATUS, (Tundo_hook)CC_hook_status, 0);
}

/*--------------------------------------------------------------*/

static void
backtrack_done(void)
{
}

/*
  --------------------------------------------------------------
  Resize
  --------------------------------------------------------------
*/

static void
CC_DAG_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  TDAG i;
  for (i = new_alloc; i < old_alloc; i++)
    {
#if defined(DEBUG) || defined(EXPLAIN_CLASSIC)
      TCC *PCC = CC + i;
#endif
#ifdef DEBUG
      Tclass_info *Pclass = class_info + i;
      assert(!class[i]);
#ifdef EXPLAIN_CLASSIC
      assert(!stack_size(PCC->stack_eq));
#else
      assert(!PCC->next);
      assert(!PCC->clue);
#endif
      assert(!PCC->clue_pred);
      assert(!Pclass->elem_nb);
      assert(!Pclass->elem);
      assert(!Pclass->pred_nb);
      assert(!Pclass->pred);
      assert(Pclass->DAG == i);
      assert(!Pclass->ineq_nb);
      assert(!Pclass->ineq);
      assert(!Pclass->watch_eq_nb);
      assert(!Pclass->watch_eq);
      assert(!Pclass->dp_mask);
      assert(Pclass->boolean_value == UNDEFINED);
#ifdef CC_CLASS_LIST
      assert(!in_class_list[i]);
#endif
#endif
#ifdef EXPLAIN_CLASSIC
      stack_free(PCC->stack_eq);
#endif
    }
  MY_REALLOC(class, new_alloc * sizeof(TCC));
  for (i = old_alloc; i < new_alloc; i++)
    class[i] = 0;
  MY_REALLOC(CC, new_alloc * sizeof(TCC));
  for (i = old_alloc; i < new_alloc; i++)
    {
      TCC *PCC = CC + i;
#ifdef EXPLAIN_CLASSIC
      stack_INIT_s(PCC->stack_eq, 1);
#else
      PCC->clue = NULL;
      PCC->next = DAG_NULL;
#endif
      PCC->clue_pred = NULL;
    }
  MY_REALLOC(class_info, new_alloc * sizeof(Tclass_info));
  for (i = old_alloc; i < new_alloc; i++)
    {
      Tclass_info *Pclass = class_info + i;
      Pclass->elem_nb = 0;
      Pclass->elem = DAG_NULL;
      Pclass->pred_nb = 0;
      Pclass->pred = NULL;
      Pclass->DAG = i;
      Pclass->ineq_nb = 0;
      Pclass->ineq = NULL;
      Pclass->watch_eq_nb = 0;
      Pclass->watch_eq = NULL;
      Pclass->boolean_value = UNDEFINED;
      Pclass->dp_mask = 0;
    }
#ifdef CC_CLASS_LIST
  MY_REALLOC(in_class_list, new_alloc * sizeof(Tdll_DAG));
  for (i = old_alloc; i < new_alloc; i++)
    in_class_list[i] = DLL_DAG_NULL;
#endif
}

/*
  --------------------------------------------------------------
  Interface
  --------------------------------------------------------------
*/

Tstatus
CC_status(void)
{
  return status;
}

/*--------------------------------------------------------------*/

void
CC_push(Tclue clue)
{
#ifdef DEBUG_CC
  my_message("CC: CC_push: \n");
  clue_print2(clue);
#endif
  if (!clue)
    return;
  if (status == UNSAT)
    {
      clue_free(clue);
      return;
    }
  if (!clue->DAG[1])
    {
      if (DAG_quant(clue->DAG[0]))
	{
	  DAG_add_q(clue->DAG[0]);
	  stack_push(CC_quantified, DAG_dup(clue->DAG[0]));
	  backtrack_store_quantified();
	  clue_free(clue);
	  return;
	}
      DAG_add(clue->DAG[0]);
      CC_set_predicate(clue);
      /* PF TODO this is a hack...
	 is it necessary (efficiency, completeness)?
	 where is it best located? */
      if (clue->type == CLUE_LITERAL &&
	  ((clue->polarity == 0 && DAG_symb(clue->DAG[0]) == PREDICATE_LEQ) ||
	   (clue->polarity == 1 && DAG_symb(clue->DAG[0]) == PREDICATE_LESS)))
	{
	  clue = clue_new_implied_inequality(clue);
	  CC_anti_merge(clue);
	}
      return;
    }
  DAG_add(clue->DAG[0]);
  DAG_add(clue->DAG[1]);
  if (clue->polarity)
    CC_merge(clue);
  else
    CC_anti_merge(clue);
}

/*--------------------------------------------------------------*/

void
CC_watch(Tclue clue)
{
  /*  int i;
  for (i = 0; i < DAG_arity(DAG); i++)
  DAG_add(DAG_arg(DAG, i)); */
  if (!clue)
    return;
  assert(lit_pol(clue->proof.lit));
  if (status == UNSAT)
    {
      clue_free(clue);
      return;
    }
  if (!clue->DAG[1])
    {
      if (DAG_quant(clue->DAG[0]))
	{
	  clue_free(clue);
	  return;
	}
      CC_watch_pred(clue->DAG[0], clue->proof.lit);
      DAG_add(clue->DAG[0]);
      clue_free(clue);
      return;
    }
  DAG_add(clue->DAG[0]);
  DAG_add(clue->DAG[1]);
  CC_watch_eq(clue);
}

/*
  --------------------------------------------------------------
  Public functions for instantiation
  --------------------------------------------------------------
*/

static Tstack_DAG CC_get_sig_aux_stack;
static Tsymb CC_get_sig_aux_symb;
static void
CC_get_sig_aux(TDAG DAG)
{
  if (DAG_symb(DAG) == CC_get_sig_aux_symb)
    stack_push(CC_get_sig_aux_stack, DAG);
}

/*--------------------------------------------------------------*/

Tstack_DAG
CC_get_sig(Tsymb symb)
{
  Tstack_DAG result;
  stack_INIT(result);
  CC_get_sig_aux_symb = symb;
  CC_get_sig_aux_stack = result;
  hash_apply(sig_hash, (TFapply) CC_get_sig_aux);
  result = CC_get_sig_aux_stack;
  return result;
}

/*--------------------------------------------------------------*/

Tstack_DAG
CC_get_sig_DAG(Tsymb symb, TDAG DAG)
{
  unsigned i;
  Tstack_DAG result;
  stack_INIT(result);
  for (i = CC_find(DAG)->elem_nb; i-- > 0; DAG = class_info[DAG].elem)
    if (DAG_symb(DAG) == symb)
      stack_push(result, DAG);
  return result;
}

/*--------------------------------------------------------------*/

Tstack_DAG
CC_get_sort_classes(Tsort sort)
{
  unsigned i;
  Tstack_DAG result;
  stack_INIT(result);
  DAG_tmp_reserve();
  for (i = 1; i < stack_size(DAG_table); i++)
    if (class[i] && !DAG_tmp_bool[class[i]] && DAG_sort(class[i]) == sort)
      {
	stack_push(result, class[i]);
	DAG_tmp_bool[class[i]] = 1;
      }
  for (i = 0; i < stack_size(result); i++)
    DAG_tmp_bool[stack_get(result, i)] = 0;
  DAG_tmp_release();
  return result;
}

/*
  --------------------------------------------------------------
  Public functions: DPs
  --------------------------------------------------------------
*/

TDAG
CC_abstract(TDAG DAG)
{
  return CC_find(DAG)->DAG;
}

/*
  --------------------------------------------------------------
  Public functions: proof
  --------------------------------------------------------------
*/

#ifdef PROOF

Tlist
CC_conflict(Tproof_id * Pproof_id)
{
  return conflict_analyse(Pproof_id);
}

#else

Tlist
CC_conflict(void)
{
  return conflict_analyse();
}

#endif /* PROOF */

/*--------------------------------------------------------------*/

Tlist
CC_premisses(Tclue clue)
{
  Tlist tmp;
  switch (clue->type)
    {
    case CLUE_ABSTRACT_TERM :
      tmp = CC_proof_abstract_term(clue);
      break;
    case CLUE_ABSTRACT_PRED :
      tmp = CC_proof_abstract_pred(clue);
      break;
    case CLUE_ABSTRACT_QUANT :
      tmp = CC_proof_abstract_quant(clue);
      break;
    case CLUE_IMPLIED_INEQUALITY :
      tmp = CC_proof_implied_inequality(clue);
      break;
    case CLUE_INEQUALITY :
      tmp = CC_proof_inequality(clue);
      break;
    case CLUE_MERGE :
      tmp = CC_proof_merge(clue);
      break;
    default :
      my_error("CC_premisses: strange clue\n");
      return NULL;
    }
  return CC_remove_congruences(tmp OPTC_PROOF(&clue->proof_id));
}

/*
  --------------------------------------------------------------
  Model output
  --------------------------------------------------------------
*/

static Ttable * model_symb = NULL;

static void
CC_model_aux(TDAG DAG)
{
  Ttable table_sig = NULL;
  table_sig = model_symb[DAG_symb(DAG)];
  if (table_sig == NULL)
    {
      table_sig = table_new(4, 4);
      model_symb[DAG_symb(DAG)] = table_sig;
    }
  table_push(table_sig, DAG_ptr_of(DAG));
}

/*--------------------------------------------------------------*/

static unsigned class_id = 0;

static unsigned
CC_model_get_class_id(TDAG DAG)
{
  TDAG DAG2 = CC_find(DAG)->DAG;
  if (!DAG_tmp_unsigned[DAG2]) 
    DAG_tmp_unsigned[DAG2] = ++class_id;
  return DAG_tmp_unsigned[DAG2];
}

/*--------------------------------------------------------------*/

static void
CC_model_reset_class_id(TDAG DAG)
{
  TDAG DAG2 = CC_find(DAG)->DAG;
  DAG_tmp_unsigned[DAG2] = 0;
}

/*--------------------------------------------------------------*/

void
CC_model(void (out) (char *format, ...))
{
  Tsymb symb;
  unsigned i, t = 0;
  class_id = 0;
  MY_MALLOC(model_symb, sizeof(*model_symb) * stack_size(DAG_symb_stack));
  bzero(model_symb, sizeof(*model_symb) * stack_size(DAG_symb_stack));
  DAG_tmp_reserve();
  out("(");
  for (i = 0; i < stack_size(zero_arity); i++)
    {
      TDAG DAG = stack_get(zero_arity, i);
      out("%s(%s cc_%d)\n",t++?" ":"", symb_name(DAG_symb(DAG)),
	  CC_model_get_class_id(DAG));
    }
  hash_apply(sig_hash, (TFapply) CC_model_aux);
  for (symb = 1; symb < stack_size(DAG_symb_stack); symb++)
    {
      unsigned j;
      Ttable table_sig = model_symb[symb];
      TDAG DAG;
      if (table_sig == NULL) continue;
      DAG = DAG_of_ptr(table_get(table_sig, 0));
      out("%s(%s ",t++?" ":"", symb_name(DAG_symb(DAG)));
      for (j = 0; j < table_length(table_sig); j++)
	{
	  TDAG DAG = DAG_of_ptr(table_get(table_sig, j));
	  unsigned k;
	  out("\n   (");
	  for (k = 0; k < DAG_arity(DAG); k++)
	    out(k?" cc_%d":"cc_%d", CC_model_get_class_id(DAG_arg(DAG, k)));
	  if (symb_type(DAG_symb(DAG)) == SYMB_PREDICATE)
	    {
	      if (CC_find(DAG)->boolean_value == true)
		out(" true)");
	      else
		out(" false)");
	    }
	  else
	    out(" cc_%d)", CC_model_get_class_id(DAG));
	}
      out(")\n");
    }
  out(")\n");
  for (symb = 1; symb < stack_size(DAG_symb_stack); symb++)
    {
      unsigned j;
      Ttable table_sig = model_symb[symb];
      if (table_sig == NULL) continue;
      for (j = 0; j < table_length(table_sig); j++)
	{
	  TDAG DAG = DAG_of_ptr(table_get(table_sig, j));
	  unsigned k;
	  for (k = 0; k < DAG_arity(DAG); k++)
	    CC_model_reset_class_id(DAG_arg(DAG, k));
	  CC_model_reset_class_id(DAG);
	}
      table_free(&table_sig);
    }
  free(model_symb);
  for (i = 0; i < stack_size(zero_arity); i++)
    CC_model_reset_class_id(stack_get(zero_arity, i));
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
CC_init(const unsigned id)
{
  CC_id = id;
  status = SAT;
  sig_hash = hash_new(2048, (TFhash)sig_hash_function,
		      (TFequal)sig_hash_equal, NULL);
  stack_INIT(zero_arity);
  stack_INIT(CC_buffer);
  backtrack_init();
  conflict_init();
  stack_INIT(CC_quantified);
#ifdef DEBUG_CC
  sig_hash_n = 0;
#endif
  DAG_set_hook_resize(CC_DAG_hook_resize);
#ifndef EXPLAIN_CLASSIC
  explain_init();
#endif
}

/*--------------------------------------------------------------*/

void
CC_done(void)
{
  assert(!stack_size(CC_quantified));
  stack_free(CC_quantified);
  stack_free(CC_buffer);
#ifndef EXPLAIN_CLASSIC
  explain_done();
#endif
  conflict_done();
  backtrack_done();
#ifdef CC_STAT
  my_message("Congruence closure signature table stats:\n");
  hash_print_stats(sig_hash);
#endif
  stack_free(zero_arity);
  hash_free(&sig_hash);
}

/*
  --------------------------------------------------------------
  Lemma generation
  --------------------------------------------------------------
*/

void
CC_lemmas(Tstack_DAG * Plemmas)
{
#ifdef PEDANTIC
  if (*Plemmas)
    *Plemmas = NULL;
#endif
}

/*--------------------------------------------------------------*/

bool
CC_has_lemma(void)
{
  return false;
}
