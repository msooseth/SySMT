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
  Instantiation engine
  --------------------------------------------------------------
*/
#include <limits.h>

#include "config.h"
#include "general.h"
#include "hash.h"
#include "stack.h"

#include "options.h"
#include "statistics.h"

#include "DAG.h"
#include "DAG-prop.h"
#include "DAG-tmp.h"
#include "DAG-ptr.h"
#include "DAG-subst.h"
#include "pre.h"
#include "qnt-trigger.h"
#include "recursion.h"
#include "congruence.h"

#include "inst.h"

/* TODO include */
extern TDAG CC_abstract(TDAG);
extern Tstack_DAG CC_quantified;

/* #define DEBUG_EMATCH */
/* #define DEBUG_EMATCH2 */
/* #define DEBUG_INST */

#ifdef DEBUG_EMATCH
#include "DAG-print.h"
#include "dbg-trigger.h"
#endif

unsigned inst_mask;
static Thash  inst_hash = NULL;

#ifdef PROOF
typedef struct TDAG_proof {
  TDAG DAG;
  Tproof_id proof; } TDAG_proof;
TSstack(_DAG_proof, TDAG_proof);
static Tstack_DAG_proof inst_new_table = NULL;
#else
static Tstack_DAG inst_new_table = NULL;
#endif


/** \brief matchings performed with triggers */
static unsigned inst_stats_match;
/** \brief instances generated with triggers */
static unsigned stats_trigger;
/** \brief instances generated with sorts */
static unsigned inst_stats_sort;
/** \brief redundant instances */
static unsigned inst_stats_redundant;
/** \brief total time in instances generation */
static unsigned inst_stats_time;
/** \brief attach to each sort the set of CC classes */
static Tstack_DAG *sort_classes;
/*
  --------------------------------------------------------------
  Options
  --------------------------------------------------------------
*/
/**
   \addtogroup arguments_user

   - --inst_depth_threshold

   Modifies the computation of substitutions used to build instances
   of quantified formulas. When this option is set, the depth of the
   terms chosen to form such substitutions increased between each
   matching round that are not separated by the activation of new
   terms. If new terms are activated, the maximal depth for the chosen
   terms is reestablished to one.

   The default behaviour is to generate instances with substitutions
   formed with terms of depth up to the value of THRESHOLD */
static bool inst_depth_threshold; 

/*
  --------------------------------------------------------------
  Misc
  --------------------------------------------------------------
*/

/**
   \author David Deharbe & Pascal Fontaine
   \brief marks the top-symbol of the node as being relevant for ematching
   \param DAG the node
*/
static void 
inst_mark_symb_node(TDAG DAG)
{
  if (DAG_symb_type(DAG_symb(DAG)) == SYMB_VARIABLE)
    return;
  if (DAG_symb_dp_mask(DAG_symb(DAG)) & inst_mask)
    return;
  DAG_symb_dp_mask(DAG_symb(DAG)) |= inst_mask;
  /* #warning DD please review this */
  /* PF
     This function may be called through NO_pre because of new instances
     I changed the assert to a test because in such cases symbols may
     not be known.  Before, the assert was not even there, and this could
     simply erase the information linked to symb, generating later mistakes.
     What worries me now is the effect of having symbols that suddenly
     become relevant for ematch.  I am sure the information from CC is not
     transfered as it should.
  */
#ifdef DEBUG_EMATCH
  my_DAG_message("inst_mark_symb: %D\n",DAG);
#endif
}

/*--------------------------------------------------------------*/

/**
   \author David Deharbe & Pascal Fontaine
   \brief marks the all symbols (except vars) in the pattern as
   relevant for ematching
   \param DAG the pattern
*/
static void
inst_mark_symb(TDAG DAG)
{
  structural_recursion_void(DAG, inst_mark_symb_node);
}

/*--------------------------------------------------------------*/

/**
   \author David Deharbe & Pascal Fontaine
   \brief inspects the whole formula, adds trigger to every quantified
   formula without triggers, and ensures the triggers are on the
   formula itself, not on the body
   \param DAG the formula
*/
static void
inst_add_triggers(TDAG src)
{
  unsigned i;
  Tstack_DAGstack *Pannot;
  Tstack_DAGstack annot;

  if (!DAG_quant(src)) return;

  if (DAG_symb_type(DAG_symb(src)) == SYMB_BOOLEAN) 
    {
      for (i = 0; i < DAG_arity(src); ++i)
	inst_add_triggers(DAG_arg(src, i));
    }
  if (!quantifier(DAG_symb(src)))
    return;
  Pannot = DAG_prop_get(src, DAG_PROP_TRIGGER);
  if (!Pannot)
    {
      annot = qnt_triggers(src);
      if (annot)
	DAG_prop_set(src, DAG_PROP_TRIGGER, &annot);
    }
  Pannot = DAG_prop_get(src, DAG_PROP_TRIGGER);
  if (Pannot)
    {
      unsigned i;
      for (i = 0; i < stack_size(*Pannot); ++i)
	{
	  Tstack_DAG trigger = stack_get(*Pannot, i);
	  unsigned j;
	  for (j = 0; j < stack_size(trigger); ++j)
	    inst_mark_symb(stack_get(trigger, j));
	}
    }
#ifdef DEBUG_EMATCH2
  my_DAG_message("inst_add_triggers\n");
  dbg_trigger_print(src);
#endif
}

/*
  --------------------------------------------------------------
  E-matching
  --------------------------------------------------------------
*/

static unsigned THRESHOLD_MAX = INT_MAX; /**< max depth for substituted terms */
static unsigned THRESHOLD_MIN = 0;       /**< initial value */
static unsigned THRESHOLD = 5;           /**< current value */

/*--------------------------------------------------------------*/

/**
   \brief generates an instantiation lemma, given a total substitution
   on quantified variables
   \param DAG a quantified formula
   \pre DAG_tmp_DAG for quantified variables records a substitution
   \return the instance of the body of DAG according to the
   substitution recorded in DAG_tmp_DAG
   \post DAG_tmp_DAG left unchanged
   \remarks uses DAG_tmp_DAG for DAG and its sub-DAGs */
static inline TDAG
inst_qnt_DAG_total(TDAG DAG)
{
  TDAG  dest;
  unsigned   i;
  TDAG *PDAG;
  MY_MALLOC(PDAG, (DAG_arity(DAG) - 1u) * sizeof(TDAG));
  /* backs up the DAG_tmp_DAG of variables to restore them later */
  for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
    PDAG[i] = DAG_tmp_DAG[DAG_arg(DAG, i)];
  DAG_tmp_subst(DAG_argn(DAG));
  dest = DAG_tmp_DAG[DAG_argn(DAG)];
  /* eliminates all DAG_tmp_DAG */
  DAG_tmp_reset_DAG(DAG_argn(DAG));
  /* restore the DAG_tmp_DAG of variables */
  for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
    DAG_tmp_DAG[DAG_arg(DAG, i)] = PDAG[i];
  free(PDAG);
  return dest;
}

/*--------------------------------------------------------------*/

#if 0

/**
   \brief generates an instantiation lemma, given a partial substitution
   of quantified variables.
   \param DAG a quantified formula
   \pre DAG_tmp_DAG for quantified variables records a substitution
   \return the instance of DAG according to the substitution recorded in 
   DAG_tmp_DAG
   \post DAG_tmp_DAG left unchanged
   \remarks uses DAG_tmp_DAG for DAG and its sub-DAGs */
static inline TDAG
inst_qnt_DAG_partial(TDAG DAG)
{
  int arity;
  TDAG  dest;
  TDAG *PDAG1, *PDAG2;
  int   i, j;

  /* computes arity of result */
  for (arity = 1, i = 0; i < DAG_arity(DAG) - 1; ++i)
    arity += !DAG_tmp_DAG[DAG_arg(DAG, i)];
  if (arity ==  1 || /* substitution is total and has been produced elsewhere */
      arity == DAG_arity(DAG)) /* no substitution */
    return DAG_NULL;

  /* backs up the DAG_tmp_DAG of variables to restore them later */
  MY_MALLOC(PDAG1, (DAG_arity(DAG) - 1) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
    PDAG1[i] = DAG_tmp_DAG[DAG_arg(DAG, i)];

  /* allocates and fills array of result's arguments */
  MY_MALLOC(PDAG2, arity * sizeof(TDAG));
  for (i = j = 0; i < DAG_arity(DAG) - 1; ++i)
    if (!PDAG1[i])
      PDAG2[j++] = DAG_arg(DAG, i);

  DAG_tmp_subst(DAG_argn(DAG));
  PDAG2[j] = DAG_tmp_DAG[DAG_argn(DAG)];
  DAG_tmp_reset_DAG(DAG_argn(DAG));
  /* restore the DAG_tmp_DAG of variables */
  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
    DAG_tmp_DAG[DAG_arg(DAG, i)] = PDAG1[i];
  free(PDAG1);
  dest = DAG_new(DAG_symb(DAG), arity, PDAG2);
  return dest;
}

#endif

/*--------------------------------------------------------------*/

/**
   \brief generates the instance of the body of DAG according to the
   substitution recorded in Pflags, checks if it is new or redundant
   and stores it in the corresponding hash tables.
   \param DAG a quantified formula
   \param total records if the instantiation must be over all
   quantified variables or not
   \pre the Pflag attributes of quantified variable records a substitution
   \post the Pflag attributes are left unchanged
   \remarks uses the Pflag attribute of DAG and its sub-DAGs.
   \return true if a new lemma was generated, false otherwise

   \note The proof producing version differs by applying formula
   pre-processing and trigger detection to the whole lemma (instead of
   applying only such processing to the instance only) .
*/
static bool
inst_DAG(TDAG DAG)
{
  TDAG lemma = inst_qnt_DAG_total(DAG);
#ifdef PROOF
  TDAG * PDAG;
  unsigned i;
#endif
  if (lemma == DAG_NULL || lemma == DAG)
    return false;
  if (DAG_symb(DAG) == QUANTIFIER_FORALL)
    lemma = DAG_dup(DAG_or2(DAG_not(DAG), lemma));
  else
    lemma = DAG_dup(DAG_or2(DAG, DAG_not(lemma)));
  if (hash_lookup(inst_hash, DAG_ptr_of(lemma)))
    {
      DAG_free(lemma);
      return false;
    }
  hash_insert(inst_hash, DAG_ptr_of(DAG_dup(lemma)));
#ifdef PROOF
  MY_MALLOC(PDAG, (DAG_arity(DAG) - 1) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
    PDAG[i] = DAG_tmp_DAG[DAG_arg(DAG, i)];
  stack_inc(inst_new_table);
  stack_top(inst_new_table).DAG = lemma;
  stack_top(inst_new_table).proof =
    ((DAG_symb(DAG) == QUANTIFIER_FORALL)? proof_add_forall_inst_lemma:
     proof_add_exists_inst_lemma)(lemma, DAG_arity(DAG) - 1, PDAG);
  free(PDAG);
#else
  stack_push(inst_new_table, lemma);
#endif
  return true;
}

/*
  --------------------------------------------------------------
  DAG depth
  --------------------------------------------------------------
*/
/* TODO: THIS IS VERY MUCH TEMPORARY.  IT MIXES TWO USES OF DAG_TMP
   SHOULD BE SAFE, BUT PRETTY DIRTY */

/*--------------------------------------------------------------*/

static unsigned
DAG_depth_aux(TDAG DAG)
{
  unsigned i, j;
  if (DAG_arity(DAG))
    return 1;
  if (!DAG_tmp_unsigned[DAG])
    {
      for (i = 0, j = 0; i < DAG_arity(DAG); i++)
	{
	  unsigned k = DAG_depth_aux(DAG_arg(DAG, i));
	  if (k > j) j = k;
	}
      DAG_tmp_unsigned[DAG] = j + 1;
    }
  return DAG_tmp_unsigned[DAG];
}

/*--------------------------------------------------------------*/

static unsigned
DAG_depth(TDAG DAG)
{
  unsigned res = DAG_depth_aux(DAG);
  DAG_tmp_reset_unsigned(DAG);
  return res;
}

/*
  --------------------------------------------------------------
  E matching
  --------------------------------------------------------------
*/

static void inst_ematch_patt_list(Tstack_DAG trigger, unsigned i, TDAG DAG);

/*--------------------------------------------------------------*/

/**
   \param Pjobs pointer to a stack with all patterns and patterns bits
   to be matched, interleaved with CC class representants or
   sub-terms.
   \param job next pattern in jobs to be matched
   \param trigger is a list of patterns to be instantiated
   \param next is the index of the next pattern to be instantiated in trigger
   \param DAG the DAG to be instantiated.

   The function returns and the matcher backtracks when matching fails.

   The elements "jobs" represent patterns to be processed by the matcher, 
   implemented in this function.  When all jobs, the next pattern is
   instantiated.
*/
static void
inst_ematch_args(Tstack_DAG * Pjobs, unsigned job,
		 Tstack_DAG trigger, unsigned next, TDAG DAG)
{
  TDAG   p, t;
  unsigned i;
  Tstack_DAG terms;

  if (job == stack_size(*Pjobs)) /* the pattern has been processed */
    {
      inst_ematch_patt_list(trigger, next, DAG); /* process next pattern */
      return;
    }
  p = stack_get(*Pjobs, job);
  t = stack_get(*Pjobs, job+1);
  if (DAG_symb_type(DAG_symb(p)) == SYMB_VARIABLE)
    {
      if (DAG_depth(t) > THRESHOLD)
	/* TODO */
	return;
      if (!DAG_tmp_DAG[p])
	{
	  DAG_tmp_DAG[p] = t;
	  inst_ematch_args(Pjobs, job+2, trigger, next, DAG);
	  DAG_tmp_DAG[p] = DAG_NULL;
	}
      else if (CC_abstract(DAG_tmp_DAG[p]) == CC_abstract(t))
	inst_ematch_args(Pjobs, job + 2, trigger, next, DAG);
      return;
    }
  if (DAG_arity(p) == 0)
    {
      /* TODO horrible patch by PF.  DD, we should really think
	 about how to do this nicely */
      if (CC_abstract(p) && CC_abstract(p) == CC_abstract(t))
	inst_ematch_args(Pjobs, job + 2, trigger, next, DAG);
      return;
    }
  terms = CC_get_sig_DAG(DAG_symb(p), t);
  if (stack_size(terms) > 0)
    {
      unsigned offset = stack_size(*Pjobs);
      for (i = 0; i < DAG_arity(p); ++i)
	{
	  stack_push(*Pjobs, DAG_arg(p, i));
	  stack_push(*Pjobs, DAG_NULL);
	}
      for (i = 0; i < stack_size(terms); ++i)
	{
	  unsigned j, k;
	  TDAG term = stack_get(terms, i);
	  assert(DAG_symb(term) == DAG_symb(p));
	  assert(DAG_arity(term) == DAG_arity(p));
	  for (j = 0, k = offset + 1; j < DAG_arity(p); ++j, k+=2)
	    stack_set(*Pjobs, k, DAG_arg(term, j));
	  inst_ematch_args(Pjobs, job + 2, trigger, next, DAG);
	}
      stack_dec_n(*Pjobs, 2 * DAG_arity(p));
    }
  stack_free(terms);
}

/*--------------------------------------------------------------*/

/**
   \param list a list of patterns forming a trigger

   \param endl the successor of the last node of the trigger (list),
   or NULL for the first call; used to detect in the recursion that
   the list has been completely inspected.

   \param DAG a quantified formula associated with this trigger
*/
static void
inst_ematch_patt_list(Tstack_DAG trigger, unsigned i, TDAG DAG)
{
  if (i == stack_size(trigger))
    {
      if (inst_DAG(DAG))
	stats_counter_inc(stats_trigger);
      else
	stats_counter_inc(inst_stats_redundant);
    }
  else
    {
      TDAG pat = stack_get(trigger, i);
      Tstack_DAG terms = CC_get_sig(DAG_symb(pat));
      if (stack_size(terms) > 0)
	{
	  Tstack_DAG jobs;
	  unsigned j, k;
	  stack_INIT(jobs);
	  for (j = 0; j < DAG_arity(pat); ++j)
	    {
	      stack_push(jobs, DAG_arg(pat, j));
	      stack_push(jobs, DAG_NULL);
	    }
	  for (j = 0; j < stack_size(terms); ++j)
	    {
	      TDAG term = stack_get(terms, j);
	      assert(DAG_symb(term) == DAG_symb(pat));
	      assert(DAG_arity(term) == DAG_arity(pat));
	      for (k = 0; k < DAG_arity(pat); ++k)
		stack_set(jobs, 2*k+1, DAG_arg(term, k));
	      inst_ematch_args(&jobs, 0, trigger, i+1, DAG);
	    }
	  stack_free(jobs);
	}
      stack_free(terms);
    }
}

/*--------------------------------------------------------------*/

/**
   \brief generates the instance of DAG that match the trigger
   (i.e. the list of patterns) in list
   \param DAG a quantified formula
   \param list a trigger for DAG.
 */
static void
inst_trigger_one(TDAG DAG, Tstack_DAG trigger)
{
#ifdef DEBUG_EMATCH2
  my_DAG_message("inst_trigger\n");
  my_DAG_message("\tDAG = %D\n", DAG);
  my_DAG_message("\ttrigger = \n");
  {
    unsigned i;
    for (i = 0; i < stack_size(trigger); ++i)
      my_DAG_message("\t\t%D\n", stack_get(trigger, i));
  }
#endif
  DAG_tmp_reserve();
  inst_ematch_patt_list(trigger, 0, DAG);
  DAG_tmp_release();
}

/*--------------------------------------------------------------*/
/* tests if some top-most symbols in trigger is interpreted */
static int
inst_trigger_interpreted(Tstack_DAG trigger)
{
  unsigned i;
  for (i = 0;i < stack_size(trigger); ++i)
    {
      TDAG DAG = stack_get(trigger, i);
      if (DAG_symb_interpreted(DAG_symb(DAG)))
	return 1;
    }
  return 0;
}

/*--------------------------------------------------------------*/

/*
  DAG has a trigger i.e. it has a list of set of instantiation patterns.
  inst_trigger is applied to each such pattern.
*/
static void
inst_trigger(TDAG DAG)
{
  Tstack_DAGstack *Pannot;
  unsigned i;
  unsigned count1, count2;
#ifdef DEBUG_EMATCH2
  my_DAG_message("inst_trigger %D\n", DAG);
#endif
  if (!DAG_prop_check(DAG, DAG_PROP_TRIGGER))
    return;
  Pannot = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
  count1 = stack_size(inst_new_table);
  for (i = 0; i < stack_size(*Pannot); ++i)
    {
      Tstack_DAG trigger = stack_get(*Pannot, i);
      if (!inst_trigger_interpreted(trigger))
	inst_trigger_one(DAG, trigger);
    }
  count2 = stack_size(inst_new_table);
  assert(count2 >= count1);
#ifdef DEBUG_EMATCH2
  if (count2 > count1)
    my_DAG_message("inst_trigger uninterpreted: %d\n", count2 - count1);
#endif
  if (count2 > count1)
    return;
  for (i = 0; i < stack_size(*Pannot); ++i)
    {
      Tstack_DAG trigger = stack_get(*Pannot, i);
      if (inst_trigger_interpreted(trigger))
	inst_trigger_one(DAG, trigger);
    }
#ifdef DEBUG_EMATCH2
  if (stack_size(inst_new_table) > count1)
    my_DAG_message("inst_trigger interpreted: %d\n",
		   stack_size(inst_new_table) - count1);
#endif
}

/*
  --------------------------------------------------------------
  Sort-based instantiation
  --------------------------------------------------------------
*/

static void
inst_sort(TDAG DAG)
{
  unsigned i = 0;
  unsigned *j;
  unsigned n = DAG_arity(DAG) - 1u;
  MY_MALLOC(j, n * sizeof(unsigned));
  for (i = 0; i < n; i++)
    {
      Tsort sort = DAG_sort(DAG_arg(DAG, i));
      if (!sort_classes[sort])
	sort_classes[sort] = CC_get_sort_classes(sort);
      j[i] = 0;
    }
  DAG_tmp_reserve();
  i = 0;
  while (1)
    {
      Tsort sort = DAG_sort(DAG_arg(DAG, i));
      if (j[i] == stack_size(sort_classes[sort]))
	{
	  j[i] = 0;
	  if (!i) break;
	  i--;
	  continue;
	}
      DAG_tmp_DAG[DAG_arg(DAG, i)] = stack_get(sort_classes[sort], j[i]++);
      if (i == n - 1)
	{
	  inst_DAG(DAG);
	  continue;
	}
      i++;
    }
  for (i = 0; i < n; i++)
    DAG_tmp_DAG[DAG_arg(DAG, i)] = DAG_NULL;
  free(j);
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
inst_init(void)
{
  inst_hash = hash_new(32, (TFhash) DAG_hash,
		       (TFequal) DAG_equal, (TFfree) DAG_free);
  stack_INIT(inst_new_table);

  inst_stats_match =
    stats_counter_new("instances/rounds",
		      "number of matching rounds using triggers",
		      "%6d");

  stats_trigger =
    stats_counter_new("instances/trigger",
		      "number of different instances of quantified formulas"
		      "generated with triggers",
		      "%6d");
  inst_stats_sort =
    stats_counter_new("instances/sort",
		      "number of different instances of quantified formulas"
		      "generated with sorts",
		      "%6d");
  inst_stats_redundant =
    stats_counter_new("instances/redundant",
		      "number of redundant instances of quantified formula",
		      "%6d");
  inst_stats_time =
    stats_timer_new("inst_time", "Instantiation time", "%7.2f",
		    STATS_TIMER_ALL);

  options_new(0, "dynamic-depth-threshold",
	      "Instances of quantified formulas are computed from substitutions"
	      "with terms of increasing depth.  ",
	      &inst_depth_threshold);
  sort_classes = NULL;
}

/*--------------------------------------------------------------*/

void
inst_pre(TDAG src)
{
#ifdef DEBUG_EMATCH
  my_DAG_message("ematch_pre\n", src);
#endif
  DAG_symb_dp_mask(QUANTIFIER_EXISTS) |= inst_mask;
  DAG_symb_dp_mask(QUANTIFIER_FORALL) |= inst_mask;
  inst_add_triggers(src);
}

/*--------------------------------------------------------------*/

void
inst_done(void)
{
#ifdef DEBUG_EMATCH
  my_message("ematch_done\n");
#endif
  stack_free(inst_new_table);
  hash_free(&inst_hash);
}

/*--------------------------------------------------------------*/

void    
inst_solve(void)
{
  unsigned i;
  if (QUANTIFIER_FORALL == DAG_SYMB_NULL)
    return;
  stats_counter_inc(inst_stats_match);
  stats_timer_start(inst_stats_time);

  if (inst_depth_threshold && THRESHOLD > 1) 
    THRESHOLD = THRESHOLD_MIN;
  stack_apply(CC_quantified, inst_trigger);
#ifdef DEBUG_INST
  my_message("inst_solve: quantified formulas with triggers\n");
  for (i = 0; i < stack_size(CC_quantified); ++i)
    dbg_trigger_print(stack_get(CC_quantified, i));
  my_message("inst_solve: THRESHOLD: %d\n",THRESHOLD);
  my_message("inst_solve: instances found %d\n", stack_size(inst_new_table));  
#endif
  if (inst_depth_threshold)
    while (stack_size(inst_new_table) != 0 && THRESHOLD < THRESHOLD_MAX) 
      {
	++THRESHOLD;
	stack_apply(CC_quantified, inst_trigger);
      }
  if (!stack_size(inst_new_table))
    {
      /* no instance yet: try total sort-based instances */
      MY_MALLOC(sort_classes, DAG_sort_stack->size * sizeof(Tstack_DAG));
      for (i = 0; i < DAG_sort_stack->size; ++i)
	sort_classes[i] = NULL;
      
      for (i = 0; i < stack_size(CC_quantified); ++i)
	inst_sort(stack_get(CC_quantified, i));
      
      for (i = 0; i < DAG_sort_stack->size; ++i)
	if (sort_classes[i])
	  stack_free(sort_classes[i]);
      free(sort_classes);
      sort_classes = NULL;
    }
  stats_timer_stop(inst_stats_time);
}

/*--------------------------------------------------------------*/

bool
inst_has_lemma(void)
{
  return stack_size(inst_new_table) != 0;
}

/*--------------------------------------------------------------*/

void
inst_lemmas(Tstack_DAG * Plemmas)
{
  while (stack_size(inst_new_table) != 0)
    {
      TDAG lemma;
#ifdef PROOF
      Tproof_id proof;
      lemma = stack_top(inst_new_table).DAG;
      proof = stack_top(inst_new_table).proof;
      stack_dec(inst_new_table);
#else
      lemma = stack_pop(inst_new_table);
#endif
#ifdef DEBUG_EMATCH
      my_DAG_message("New instantiation lemma (raw):\n%D\n", lemma);
#endif
      lemma = pre_process_instance(lemma OPTC_PROOF(&proof));
#ifdef DEBUG_EMATCH
      my_DAG_message("New instantiation lemma (simplified):\n%D\n", lemma);
#endif
#ifdef PROOF
      proof_set_lemma_id(lemma, proof);
#endif
      inst_add_triggers(lemma);
      stack_push(*Plemmas, lemma);
    }
}
