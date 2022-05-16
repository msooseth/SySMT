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
  Nelson-Oppen Module

  Classical schema of Nelson Oppen
  --------------------------------
  Let L be a set of literals, with symbols from several decision procedures
  DPi (i=0, 1, ..., n-1) over theories Ti.
  If we want the combination scheme to be complete (btw, it is always sound)
  we require that:
  - the decision procedures work on disjoint signatures
  - the corresponding theories are stably infinite
  Notice that, 2 DPs on non-disjoint signatures are acceptable (for instance
  DP1 and DP2), if one theory has the other as a consequence (e.g. T1 |= T2)

  Given a set of literals Li, each decision procedure DPi may return
  either unsatisfiable or satisfiable. In the latter case, the
  decision procedure shall be able to produce variable equalities (or
  disjunctions of such equalities) that are logical consequences of
  Li.

  The schema is divided into two main steps: purification, and reasoning.
  Given L, purification yields an equisatisfiable set of literals L' such
  that L' is partitioned into L0, L1, ... Ln-1, where each Li contains only
  literals built with the signature of DPi.

  Abstractly, the reasoning is a loop that
  - invokes each DPi on the corresponding Li to check for satisfiability
  - if the outcome is unsatisfiable, then the reasoning halts
  - if some variable equalities have been deduced, they are given to
  the other DPs, enlarging the set of already handled
  literals, and a new iteration is started.
  - if disjunctions of equalities have been deduced, case split
  occurs on the literals in the clause: every equality in the clause
  is successively considered as true (cf. previous case)
  - When no variable equality is deduced, then L is satisfiable
  (when the completeness conditions discussed above are fulfilled) and
  the reasoning halts.

  Use cases, and requirements
  ---------------------------

  The Nelson-Oppen schema (NO) is intended to be used conjunctively
  with a propositional reasoner (at the time: BDDs, and SAT
  solvers). The propositional reasoner produces propositional models
  and NO will be invoked to check satisfiability modulo theories on
  such models.

    Incrementality
    --------------

    The propositional engine produces the models incrementally, and NO
    might be called before a full model is built. This implies that
    often, NO will successively have to handle very similar lists of
    literals, with a large common prefix

    Thus, NO may have to be used incrementally, with backtracking
    capabilities

    Conflicts clauses
    -----------------

    The number of propositional models is usually very large.  It is
    unpractical to check all of them with NO.  A simple and useful
    technique is to use NO to generate so-called conflict clauses for
    the propositional engine to reduce the space of propositional
    models.

    In case NO decides a given set of literals is undecidable, it will
    have not only to return this information to the propositional
    engine, but also a conflict clause, i.e. an unsatisfiable subset
    of literals of the given set.

    For efficiency reasons, the smaller the conflict clause is, the
    larger is the reduction of the search space for the propositional
    engine, and the better it is.  In practice, it is very valuable to
    spend much time trying to reduce the size of the conflict clause.

    Lemmas
    ------

    Whatever NO decides (SAT, UNSAT,...), it may have lemmas that may
    be of some use for the propositional reasoner.  These formulas may
    have a complex boolean structure, and may introduce new literals.

    Lemma generation is also useful to tackle case splitting in NO. To
    handle clauses generated by DPs, two approaches are possible:
    using a recursive NO implementation with case splitting at the NO
    level, or handling the case split at the propositional level.  In
    this case, whenever a clause is generated by a DP, the NO reasoner
    may halt and produce a lemma representing this clause.  The
    different cases will then be handled by the propositional
    reasoner.

    Another possible application of lemma generation is instantiation
    of quantified formulas: a DP (e.g. a resolution-based automated
    deduction engine or a Herbrand-based instantiation module) might
    be able to generate instances of quantified formulas. It is also
    possible to envision that the NO schema involves not only decision
    procedures but other kinds of reasoning engines to generate
    lemmas.  In the following, when we refer to "decision procedure"
    it can be more generally interpreted as "reasoning engine".

    In conclusion, using lemmas avoids to handle case-splitting
    directly in the NO engine.  Also, lemmas may be used to build an
    overall complete reasoning system out of reasoning engines that
    are not decision procedures (i.e. quantifier instantiation).

    Proofs
    ------

    To check consistency of the answer of an SMT solver, or to include
    the SMT solver inside a certified proof environnement (proof
    assistant), it is required to give some information about the
    deductions that occur.  This means outputing a proof for each
    conflict clause and each lemma.

    (Dis)Activation of DPs
    ----------------------

    Some DPs are more expensive than others, and some are
    prohibitively expensive.  It should thus be possible to
    disactivate a DP, and activate it at will.  When a DP is inactive,
    it is unavailable and does not use computer time (just as if it
    were not implemented).

    When a DP becomes active, it receives all the relevant
    information.  While active, it keeps being updated with relevant
    information.  Keeping a DP disactivated and later activating it is
    overall cheaper than keeping it active all along.

    When a DP becomes inactive, its internal state is reset, and all
    pending information for this DP is erased.

    When a DP is active, disactivating and activating is only worth
    when it is not useful to maintain it active in the meantime.  This
    tradeoff depends on various factors and finding the best solution
    is the subject of further study.

  Purification / Flattening
  -------------------------

  NO relies on purification to ensure that DPs do not have to deal
  with symbols outside their signature.  Purification abstracts the
  sub-terms that are not built with symbols of the DP with
  (purification) variables.  DPs generate (disjunctions of) equalities
  of terms.  There should exist a purification variable for every term
  that may occur as a member of an equality so generated.

  Flattening is a simple way to achieve purification: every relevant
  term for a DP has a corresponding purification variable.  It ensures
  that the generated equalities can always be written as an equality
  between variables.  Flattening is simple and cheap, but may involve
  much work for the DPs, as they need to handle a large number of
  variables and literals.

  A more efficient approach would be to avoid introducing purification
  variables that will never be required in exchanged facts.

  We propose the following purification algorithm, for a DP with
  signature S:
  - if a term has its top most symbol s in S, a variable v_t is
    introduced and a (defining) equality
      v_t = pp(S, t)
    is given to the DP, where pp is the purification function, i.e.
    pp(S, t) with t = s(t_1, ... t_n) is:
    - s(pp(S, t_1),... pp(S, t_n)), if s is in S
    - a variable abstracting t otherwise.  The subterms of t are flattened too.
  - else the subterms of t are flattened.

  When an offline DP is activated, the whole stack of (user) literals
  is examined, and abstracted, modulo congruence.  One must only
  create an abstraction variable if no such variable has already been
  created for the same signature (see comments on congruence closure
  for clarifications on the concept of signature).  No equality has to
  be sent.  Sending inequalities is an option (interesting in the case
  of the E prover).

  Congruence closure maintains the purification variables associated
  to (classes of) terms, and marks the class of a term as interesting
  for a DP iff there exists an abstraction variable for a term in the
  class.

    Handling predicates
    -------------------

    A literal l, with l = s(t_1,... t_n) or l = neg s(t_1,.... t_n),
    where s a predicate in S, is handed over to DPs
    as s(pp(S, t_1),... pp(S, t_n)) (resp. neg s(pp(S, t_1),... pp(S, t_n)))

    When an offline DP is activated, s is handed to the DP iff no
    predicate with the same signature has already been sent to the DP.

    Handling equalities and inequalities
    ------------------------------------

    For equality and inequality literals, both members are purified.
    Congruence closure is responsible for generating equalities and
    dispatching them to relevant DPs.

  Congruence Closure (CC)
  ------------------

  Congruence Closure (CC) is a DP for equality and uninterpreted
  symbols.  Its theory is thus entailed by every other theory.  As a
  consequence, every symbol can be handled by its own DP, and also by
  congruence closure.  We use this fact to make the congruence closure
  module responsible for managing terms and dispatching them to the
  different decision procedures.

  In this module CC has id 0!

  The different roles fullfilled by CC are:
  - maintaining a database of all terms, in classes of equal terms
  - centralising all the deduced equalities
  - gathering new equalities from other DP
  - dispatching equality information to active and interested dps
    (according to signatures)
  - select and send all accumulated information to the DPs when
    they are activated.
  - realize congruence closure
  - purification

  Information input:
  - include a new term
  - take an equality between terms into account (with the justification-proof)
  - signature for each dp
  - active DPs (i.e. those dp that are ready to get information about
    new terms and equalities)

  Scheduling decision procedures
  ------------------------------

  The scheduling scheme (2007/12/12) is simply:
  - there are incremental decision procedures
  - there are procedures that are expensive, and thus called on the
    complete model
  - some decision procedures may also have both behaviour (having a
    light incremental job, and an expensive, non incremental one)

  For instance:
  - Difference logic is incremental, but non incremental (2007/12/12)
    for equality generation
  - Congruence closure is incremental, but includes also Herbrand
    instanciation that is not incremental

  While scheduling, the dp with the lowest index is taken first.

  Exchanging information
  ----------------------

  The NO schema requires exchanging information between different
  components:
  - the user gives literals, and gets conflict sets and lemmas;
  - CC gets literals (from user) and equalities (from DPs) and
  produces term definitions (for DPs) through purification,
  equalities (for DPs) through congruence, conflict sets and lemmas;
  - DPs get terms and congruences (from CC), and produce equalities
  (for CC), conflict sets and lemmas.

  All information is exchanged through clues, some being issued
  directly from literals (literal-clues), other being deduced.  Clues
  store their origin, and information for conflict and proof
  production.

  To purify terms, variables are associated to terms.  Congruence
  closure partitions terms into classes.  Each class is represented by
  a unique term, more precisely, by a pointer (DAG) to this term.
  Propagated equalities are between those representative terms.

  Congruence closure changes class representatives.  Such changes need
  to be reflected at the level of DPs: if a DP is interested into a
  term t and the representative of this term changes, DP must know
  about this, since future equalities will refer to the new
  representative.

  Internally, each DP maintains a hash table that associates the
  successive term representatives to the internal variable of the DP.
  It also maintains a vector that associates the internal variables to
  a term representative.

  Efficiency constraints and consequences
  ---------------------------------------

  Backtracking
  ------------

  NO has backtracking capabilities: literals may be popped in LIFO
  style. To implement this feature, we define a concept of levels. Each
  time a literal is pushed, a new level is created.  All the
  information thus produced and exchanged is associated to this level
  and maintained into a history stack.

  When a push occurs, incremental DPs receive information from
  congruence closure.  When the corresponding pop is called, this
  information needs to be removed from the knowledge base of these
  decision procedures, and congruence closure needs to remove all
  information related to this literal.  The history stack maintains
  the number of push operations for each DP as well as CC.  A NO_pop
  implies the corresponding number of pop for each DP and CC.

  Proof producing
  ---------------

  Conflict production
  -------------------

  All information is exchanged through clues, some being issued
  directly from literals (literal-clues) and other being deduced.
  Clues store their origin, and information for conflict and proof
  production.

  To build the conflict, the DP thats lead to UNSAT has to produce the
  clues that lead to UNSAT.  For each non literal-clue C, collect
  recursively the premisses, i.e. the clues that allowed DP to deduce
  C.  Eventually, all clues will be literal-clues.

  Future research
  ---------------

  - Consider the impact of flattening strategies, i.e., maximal
    flattening, vs. the purification method we describe in the
    "Purification" section.  Furthermore, it would be helpful to have
    a clear presentation of how to purify, in an efficient, complete,
    and clean way.  It is also related to the central role of CC,
    since only the minimal information for CC to regenerate all
    deduction has to be exchanged.

  - Write a presentation on the implication of CC in NO, how it can be
    useful as a central knowledge base.

  - Study the practical consequences of different scheduling strategies

  - Study the effect of making some DPs non-incremental rather than
    incremental.

  - Study the effect activating, and keeping activated, or rather
    desactivate for a while and reactivate one DP.

  - See how NO can decide if UNSAT or UNDEF.

  Draft
  -----
  Literal vs. clues: literals could be converted to clues either in CC
  or in NO: temporary satisfactory solution: clues handles by CC.

  --------------------------------------------------------------
*/
/* #define DEBUG_NO */
#include <limits.h>
#include <stdbool.h>

#include "config.h"

#include "general.h"
#include "types.h"
#include "stack.h"
#include "table.h"

#include "clue.h"
#include "congruence.h"
#include "NO.h"
#include "bool.h"
#include "veriT-status.h"

#include "undo.h"

#include "arith.h"
#include "inst.h"

#ifdef PROOF
#include "proof.h"
#endif

#ifdef DEBUG
extern void veriT_dump_literals(void);
#endif

#ifdef DEBUG_NO
#include "DAG-print.h"
#include "DAG-ptr.h"
#endif

#define symb_dp_mask(s) DAG_symb_dp_mask(s)

#ifdef DEBUG_NO
char * status_name [] = {"sat", "unsat", "undec", "open"};
#endif

/* DD+PF There is an implicit bijection from DPs to
   [0..n-1], where n is the number of dp, n <= DP_MAX (minimum word length
   to run veriT), yielding a unique identifier.
*/
typedef struct TSNO_dp
{
  /* DD+PF user friendly name of the DP */
  char * name;
  /* DD+PF identifies the procedure in the combination */
  unsigned index;
  void (* init) (const unsigned id);
  void (* done) (void);
  void (* pre) (TDAG);
  /* DD+PF DP solve functions takes as input an integer
     indicating the complexity of algorithms it may employ */
  Tstatus (* solve) (void);
  Tstatus (* status) (void);

  void (* push) (Tclue);

  /* DD+PF those two functions are needed for conflict clause generation */
  /* DD+PF returns the set of clues that lead to the conflict */
  /* PF with PROOF, the integer passed received the proof id of the conflict */
#ifdef PROOF
  Tlist   (* conflict) (Tproof_id *);
#else
  Tlist   (* conflict) (void);
#endif
  Tlist   (* premisses) (const Tclue clue);

  /* DD this function may be called to push lemma DAGs on given table */
  void    (* lemmas) (Tstack_DAG * Plemmas);
  bool    (* has_lemma) (void);

  bool    (* eq_queue_empty) (void);
  Tclue   (* eq_queue_pop) (void);

  bool    (* model_eq_queue_empty) (void);
  Tclue   (* model_eq_queue_pop) (void);


  void    (* print) (FILE *);
} * TNO_dp;

static TNO_dp CC;
static TNO_dp arith;

#ifdef DEBUG_NO
static void
NO_dp_print(TNO_dp dp)
{
  fprintf(stderr, "name = %s, index = %i\n", dp->name, dp->index);
}
#endif


/*--------------------------------------------------------------*/

TSstack(_dp, TNO_dp);

/* DD+PF stores all DPs and is such that
   forall i s.t. 0 <= i < n, stack_get(NO_dp_table, i)->index = i; */
static Tstack_dp NO_dp_table;

#define GET_DP(i) stack_get(NO_dp_table, (i))

/* DD+PF general status of the NO framework */
static Tstatus NO_status;

#define NO_DP_NONE UINT_MAX

/* DD+PF identifier of the DP that detected conflict first */
static unsigned conflict_dp;

/*--------------------------------------------------------------*/
#ifdef DEBUG_NO
static void
dp_table_print(void)
{
  int i;
  fprintf(stderr, "NO_dp_table - length = %u.\n", stack_size(NO_dp_table));
  for (i = 0; i < stack_size(NO_dp_table); ++i)
    {
      fprintf(stderr, "NO_dp_table[%u]: \n", i);
      NO_dp_print(GET_DP(i));
    }
}
#endif

static bool
always_true(void)
{
  return true;
}

/*
  --------------------------------------------------------------
  Backtracking functions
  --------------------------------------------------------------
*/

enum {NO_PUSH_HINT = UNDO_NO,
      NO_UNSAT};

/*
  --------------------------------------------------------------
  
  --------------------------------------------------------------
*/

/* DC+PF
   remember if model equality generation has been stacked */
static int model_equality_generation = 0;

/*--------------------------------------------------------------*/

#ifdef DEBUG_NO

static void
NO_print(void)
{
  my_message("NO: Nelson & Oppen state information.\n");
  dp_table_print();
}

static void
NO_check_empty_CC_buffers(void)
{
  assert(!stack_size(CC_buffer));
}
#endif

/*--------------------------------------------------------------*/

static void
backtrack_unsat(void)
{
  undo_push(NO_UNSAT);
}

/*--------------------------------------------------------------*/

static void
backtrack_unsat_hook(void * P)
{
  NO_status = UNDEF;
  conflict_dp = NO_DP_NONE;
#ifdef PEDANTIC
  printf("%p\n", P);
#endif
}

/*--------------------------------------------------------------*/

static void
backtrack_push_hint(void)
{
  (*(unsigned *)undo_push(NO_PUSH_HINT)) = bool_hint_last;
}

/*--------------------------------------------------------------*/

static void
backtrack_push_hint_hook(unsigned * Phint_last)
{
  bool_hint_last = *Phint_last;
  if (bool_hint_first > bool_hint_last)
    bool_hint_first = bool_hint_last;
}

/*--------------------------------------------------------------*/

static inline void
NO_dp_flush_clues(void)
{
  unsigned i;
#ifdef DEBUG_NO
  my_message("NO: in NO_dp_flush_clues(%s)\n", arith->name);
#endif
  for (i = 0; i < stack_size(CC_buffer); i++)
    arith->push(stack_get(CC_buffer, i));
  stack_reset(CC_buffer);
}

/*--------------------------------------------------------------*/

static inline void
NO_handle_UNSAT(TNO_dp dp)
/* DD+PF put NO in an acceptable state after UNSAT has been found */
{
  unsigned i;
#ifdef DEBUG_NO
  my_message("NO: in NO_handle_UNSAT(%lu)\n", dp->index);
#endif
  for (i = 0; i < stack_size(CC_buffer); i++)
    clue_free(stack_get(CC_buffer, i));
  stack_reset(CC_buffer);
  while (!arith->eq_queue_empty())
    clue_free(arith->eq_queue_pop());
  /*  while (!arith->model_eq_queue_empty())
      clue_free(arith->model_eq_queue_pop());*/
  conflict_dp = dp->index;
  backtrack_unsat();
  NO_status = UNSAT;
}

/*--------------------------------------------------------------*/

Tstatus
NO_solve(void)
{
#ifdef DEBUG_NO
  my_message("NO: in NO_solve\n");
#endif
  if (NO_status == UNSAT) return UNSAT;
 
handle_equalities:
  arith->push(NULL);
  arith->solve();
  if (arith->status() == UNSAT)
    {
      NO_handle_UNSAT(arith);
      return UNSAT;
    }
  if (!arith->eq_queue_empty())
    {
      do
	{
	  CC_push(arith->eq_queue_pop());
	}
      while (!arith->eq_queue_empty());
      if (CC_status() == UNSAT)
	{
	  NO_handle_UNSAT(CC);
	  return UNSAT;
	}
      if (stack_size(CC_buffer))
	{
	  unsigned i;
	  for (i = 0; i < stack_size(CC_buffer); i++)
	    arith->push(stack_get(CC_buffer, i));
	  stack_reset(CC_buffer);
	  goto handle_equalities;
	}
    }

  if (!model_equality_generation)
    {
      undo_level_new();
      arith_push(NULL);
      model_equality_generation = 1;
      backtrack_push_hint();
    }
  if (!arith->model_eq_queue_empty())
    {
      do
	{
	  CC_push(arith->model_eq_queue_pop());
	}
      while (!arith->model_eq_queue_empty());
      if (CC_status() == UNSAT)
	{
	  NO_handle_UNSAT(CC);
	  return UNSAT;
	}
      if (stack_size(CC_buffer))
	{
	  unsigned i;
	  for (i = 0; i < stack_size(CC_buffer); i++)
	    arith->push(stack_get(CC_buffer, i));
	  stack_reset(CC_buffer);
	  goto handle_equalities;
	}
    }

  assert(model_equality_generation);
  model_equality_generation = 0;

  inst_solve();

  undo_level_del();
#ifdef DEBUG_NO
  my_message("NO: ou NO_solve\n");
  NO_print();
#endif
  return NO_status;
}

/*--------------------------------------------------------------*/

Tstatus
NO_push(Tlit lit)
{
  TDAG DAG;
#ifdef DEBUG_NO
  NO_check_empty_CC_buffers();
  if (lit)
    my_DAG_message("NO: in NO_push %s%D   status=%d\n",
		   !lit_pol(lit)? "not" : "", var_to_DAG(lit_var(lit)),
		   NO_status);
  else
    my_DAG_message("NO: in NO_push NULL   status=%d\n",
		   NO_status);
#endif
  if (model_equality_generation)
    {
      model_equality_generation = 0;
      undo_level_del();
    }
  /* if current status is UNSAT, just increment literal counter and return */
  /* push literal in the input queue of CC */
  undo_level_new();
  backtrack_push_hint();
  if (!lit)
    {
      CC_push(NULL);
    }
  if (NO_status == UNSAT || !lit)
    {
#ifdef DEBUG_NO
      NO_check_empty_CC_buffers();
#endif
      return NO_status;
    }
  DAG = var_to_DAG(lit_var(lit));
  if (boolean_connector(DAG_symb(DAG)))
    return NO_status;
  /* DD+PF here begins the new level */
  CC_push(clue_new_literal(lit));
  while (CC_status() != UNSAT)
    {
      NO_dp_flush_clues();
      if (arith->status() == UNSAT)
	{
	  NO_handle_UNSAT(arith);
	  return UNSAT;
	}
      /* NO_dp->status() may put equalities in CC input queue */
      if (arith->eq_queue_empty())
	return NO_status;
      do
	{
	  CC_push(arith->eq_queue_pop());
	}
      while (!arith->eq_queue_empty());
    }
  NO_handle_UNSAT(CC);
#ifdef DEBUG_NO
  NO_check_empty_CC_buffers();
  my_message("NO: ou NO_push\n");
  NO_print();
#endif
  return NO_status;
}

/*--------------------------------------------------------------*/

void
NO_watch(Tlit lit)
{
  TDAG DAG;
  if (NO_status == UNSAT)
    return;
  DAG = var_to_DAG(lit_var(lit));
  if (boolean_connector(DAG_symb(DAG)))
    return;
  CC_watch(clue_new_literal(lit));
  while (CC_status() != UNSAT)
    {
      NO_dp_flush_clues();
      if (arith->status() == UNSAT)
	{
	  NO_handle_UNSAT(arith);
	  return;
	}
      if (arith->eq_queue_empty())
	return;
      while (!arith->eq_queue_empty())
	{
	  CC_push(arith->eq_queue_pop());
	}
    }
  return;
}

/*--------------------------------------------------------------*/

void
NO_pop(void)
{
  if (model_equality_generation)
    {
#ifdef DEBUG_NO
      my_message("NO: NO_pop: model_equality backtracked\n");
#endif
      model_equality_generation = 0;
      undo_level_del();
    }
  undo_level_del();
#ifdef DEBUG_NO
  my_message("NO: NO_pop\n");
  NO_print();
#endif
  /* TODO check that the clue created to represent this literal
     has indeed been destroyed */
}

/*--------------------------------------------------------------*/

int
NO_quiet(void)
{
  assert(!stack_size(CC_buffer));
  assert(arith->eq_queue_empty());
  return !arith->has_lemma() && !inst_has_lemma();
}

/*--------------------------------------------------------------*/

int
NO_will_backtrack(void)
{
  return NO_status == UNSAT && !model_equality_generation;
}

/*--------------------------------------------------------------*/

#ifdef DEBUG_CONFLICT_CLAUSE
static void
list_clues_fprint(FILE * file, Tlist clues)
{
  if (clues == NULL)
    {
      fprintf(file, "NULL\n");
    }
  else
    {
      Tlist ptr;
      ptr = clues;
      do
	{
	  Tclue clue = (Tclue) list_car(ptr);
	  clue_fprint(file, clue);
	  fprintf(file, "\n");
	  ptr = list_cdr(ptr);
	} while (ptr != clues);
    }
}
#endif

/*--------------------------------------------------------------*/

#ifdef PROOF

static Tproof_id * resolution_chain = NULL;
static unsigned resolution_chain_size = 0;
static unsigned resolution_chain_allocated = 0;

static void
resolution_chain_add(Tproof_id proof_id)
{
  if (resolution_chain_allocated < resolution_chain_size + 1)
    {
      resolution_chain_allocated *= 2;
      MY_REALLOC(resolution_chain, resolution_chain_allocated * sizeof(int));
    }
  resolution_chain[resolution_chain_size++] = proof_id;
}

/*--------------------------------------------------------------*/

static Tproof_id
resolution_chain_close(void)
{
  Tproof_id proof_id;
  proof_id = proof_resolve_array(resolution_chain_size, resolution_chain);
  resolution_chain_size = 0;
  return proof_id;
}

/*--------------------------------------------------------------*/

static int
clue_misc_is_set(Tclue clue)
{
  if (clue->misc)
    return 1;
  clue->misc = 1;
  return 0;
}

/*--------------------------------------------------------------*/

static void
clue_unset_proof_id(Tclue clue)
{
  clue->proof_id = 0;
}

#endif

/*--------------------------------------------------------------*/

static void
clue_unset_misc(Tclue clue)
{
  clue->misc = 0;
}

/*--------------------------------------------------------------*/

/* DD+PF In case a conflict has been found by a DP, add to the set
   given as argument (which should be empty) the literals that took
   part in the reasoning leading to the conflict */
#ifdef PROOF

static Tclause
NO_conflict_clause(void)
{
  Tlist clues, tmp;
  Tclause clause = clause_new(0);
  Tproof_id proof_id = 0;
  clues = GET_DP(conflict_dp)->conflict(&proof_id);
  assert(clues);
  if (proof_id)
    resolution_chain_add(proof_id);
#ifdef DEBUG_CONFLICT_CLAUSE
  my_message("NO: conflict clause detected by %s\n",
	     GET_DP(conflict_dp)->name);
  list_clues_fprint(stderr, clues);
#endif
  tmp = clues;
  /* PF remove duplicates since they should not be resolved twice */
  do
    {
      Tclue clue = list_car(tmp);
      if (clue->misc)
	tmp = list_remove(tmp);
      else
	{
	  clue->misc = 1;
	  tmp = list_cdr(tmp);
	}
    }
  while (tmp != clues);
  assert(clues);
  do
    {
      Tclue clue = list_car(tmp);
      Tlist premisses = NULL;
      assert(clue);
      assert(clue->type == CLUE_MERGE ||
	     (clue->origin == DP_MAX && clue->type == CLUE_LITERAL) ||
	     (!clue->origin && (clue->type == CLUE_INEQUALITY ||
				clue->type == CLUE_IMPLIED_INEQUALITY ||
				clue->type == CLUE_ABSTRACT_TERM || 
				clue->type == CLUE_ABSTRACT_PRED ||
				clue->type == CLUE_ABSTRACT_QUANT)) ||
	     (clue->origin && clue->origin < DP_MAX &&
	      clue->type == CLUE_MODEL_EQUALITY));
#ifdef DEBUG_CONFLICT_CLAUSE
      my_message("NO: Processing clue : \n");
      clue_print2(clue);
      fprintf(stderr,"\n");
#endif
      if (clue->type == CLUE_LITERAL ||
	  clue->type == CLUE_MODEL_EQUALITY)
	clause_add_literal(clause, lit_neg(clue_literal(clue)));
      else
	{
	  premisses = GET_DP(clue->origin)->premisses(clue);
	  premisses = list_remove_all(premisses, (TFtest)clue_misc_is_set);
	  clues = list_merge(clues, premisses);
	  if (clue->proof_id)
	    resolution_chain_add(clue->proof_id);
	}

      tmp = list_cdr(tmp);
    }
  while (tmp != clues);

  list_apply(clues, (TFapply) clue_unset_misc);
  list_apply(clues, (TFapply) clue_unset_proof_id);
  list_free(&clues);
  clause->proof_id = resolution_chain_close();
  return clause;
}
#else
static Tclause
NO_conflict_clause(void)
{
  Tlist clues, tmp;
  Tclause clause = clause_new(0);
  clues = GET_DP(conflict_dp)->conflict();
  assert(clues);
#ifdef DEBUG_CONFLICT_CLAUSE
  my_message("NO: conflict clause detected by %s\n",
	     GET_DP(conflict_dp)->name);
  list_clues_fprint(stderr, clues);
#endif
  tmp = clues;
  do
    {
      Tclue clue = list_car(tmp);
      assert(clue);
      assert(clue->type == CLUE_MERGE ||
	     (clue->origin == DP_MAX && clue->type == CLUE_LITERAL) ||
	     (!clue->origin && (clue->type == CLUE_INEQUALITY ||
				clue->type == CLUE_IMPLIED_INEQUALITY ||
				clue->type == CLUE_ABSTRACT_TERM || 
				clue->type == CLUE_ABSTRACT_PRED ||
				clue->type == CLUE_ABSTRACT_QUANT)) ||
	     (clue->origin && clue->origin < DP_MAX &&
	      clue->type == CLUE_MODEL_EQUALITY));
#ifdef DEBUG_CONFLICT_CLAUSE
      my_message("NO: Processing clue : \n");
      clue_print2(clue);
      fprintf(stderr,"\n");
#endif
      if (clue->misc)
	{
	  tmp = list_cdr(tmp);
	  continue;
	}
      clue->misc = 1;
      if (clue->type == CLUE_LITERAL ||
	  clue->type == CLUE_MODEL_EQUALITY)
	clause_add_literal(clause, lit_neg(clue_literal(clue)));
      else
	clues = list_merge(clues,
			   GET_DP(clue->origin)->premisses(clue));
      tmp = list_cdr(tmp);
#ifdef DEBUG_CONFLICT_CLAUSE
      my_message("NO: list of clues\n");
      list_clues_fprint(stderr, clues);
#endif
    }
  while (tmp != clues);

  list_apply(clues, (TFapply) clue_unset_misc);
  list_free(&clues);
  return clause;
}
#endif

/*--------------------------------------------------------------*/

void
NO_clauses(Tstack_clause * Pclauses)
{
  if (NO_status == UNSAT)
    stack_push(*Pclauses, NO_conflict_clause());
}

/*--------------------------------------------------------------*/

void
NO_lemmas(Tstack_DAG * Plemmas)
{
  arith->lemmas(Plemmas);
  inst_lemmas(Plemmas);
#ifdef DEBUG_NO
  {
    int i;
    my_message("NO_lemmas: \n");
    for (i = 0; i < stack_size(*Plemmas); ++i)
      {
	my_DAG_message("%D\n", stack_get(*Plemmas, i));
      }
  }
#endif
}

/*--------------------------------------------------------------*/

/* DD + PF refer to the TNO_dp data structure for the meaning of arguments */
static TNO_dp
NO_dp_register(char * name,
	       void (* init) (const unsigned),
	       void (* done) (void),
	       void (* pre) (TDAG),
	       Tstatus (* solve) (void),
	       Tstatus (* status) (void),
	       void (* push) (Tclue),
#ifdef PROOF
	       Tlist   (* conflict) (Tproof_id *),
#else
	       Tlist   (* conflict) (void),
#endif
	       Tlist   (* premisses) (const Tclue clue),
	       void    (* lemmas) (Tstack_DAG * Plemmas),
	       bool    (* has_lemma) (void),
	       bool    (* eq_queue_empty) (void),
	       Tclue   (* eq_queue_pop) (void),
	       bool    (* model_eq_queue_empty) (void),
	       Tclue   (* model_eq_queue_pop) (void),
	       void    (* print) (FILE *))
{
  TNO_dp record;
  unsigned index = stack_size(NO_dp_table);
  MY_MALLOC(record, sizeof(struct TSNO_dp));
  record->name = strmake(name);
  record->index = index;
  record->init = init;
  record->done = done;
  record->pre = pre;
  record->solve = solve;
  record->status = status;
  record->push = push;
  record->conflict = conflict;
  record->premisses = premisses;
  record->lemmas = lemmas;
  record->has_lemma = has_lemma;
  record->eq_queue_empty = eq_queue_empty ? eq_queue_empty : always_true;
  record->eq_queue_pop = eq_queue_pop;
  record->model_eq_queue_empty = model_eq_queue_empty;
  record->model_eq_queue_pop = model_eq_queue_pop;
  record->print = print;
  stack_push(NO_dp_table, record);

  return record;
}

/*--------------------------------------------------------------*/
/* static unsigned E_index; */

void
NO_init(void)
{
  unsigned i;
  stack_INIT(NO_dp_table);
  /* DD The scheduler should not schedule CC on push, as it is already called */
  CC = 
    NO_dp_register("Congruence closure",
		   CC_init, CC_done, (void (*) (TDAG)) NULL,
		   (Tstatus (*) (void)) NULL, CC_status,
		   CC_push,
		   CC_conflict, CC_premisses,
		   CC_lemmas, CC_has_lemma,
		   (bool (*) (void)) NULL, (Tclue (*) (void)) NULL,
		   (bool (*) (void)) NULL, (Tclue (*) (void)) NULL,
		   (void (*) (FILE *)) NULL);

  arith =
    NO_dp_register("Arithmetics",
		   arith_init, arith_done, (void (*) (TDAG)) NULL,
		   arith_solve, arith_status,
		   arith_push,
		   arith_conflict, arith_premisses,
		   arith_lemmas, arith_has_lemma,
		   arith_eq_queue_empty, arith_eq_queue_pop,
		   arith_model_eq_queue_empty, arith_model_eq_queue_pop,
		   arith_print);
  dp_mask_arith = 1u << arith->index;
  CC_mask = dp_mask_arith;

  inst_mask = 1u << (arith->index + 1);

  for (i = 0; i < stack_size(NO_dp_table); ++i)
    GET_DP(i)->init(i);
  inst_init();

  /* DD 20072008 : double check!!! */
  conflict_dp = NO_DP_NONE;
  NO_status = UNDEF;
  undo_init();
  undo_set_hook(NO_UNSAT, (Tundo_hook) backtrack_unsat_hook, 0);
  undo_set_hook(NO_PUSH_HINT, (Tundo_hook) backtrack_push_hint_hook, 
		sizeof(unsigned));
#ifdef PROOF
  resolution_chain_size = 0;
  resolution_chain_allocated = 1;
  MY_MALLOC(resolution_chain, sizeof(int));
#endif
}

/*--------------------------------------------------------------*/

void
NO_pre(TDAG DAG)
{
  unsigned i;
#ifdef DEBUG_NO
  my_DAG_message("NO_pre:1\n");
#endif
  for (i = 0; i < stack_size(NO_dp_table); ++i)
    {
      void (*pre) (TDAG) = GET_DP(i)->pre;
      if (pre) pre(DAG);
    }
  inst_pre(DAG);
}

/*--------------------------------------------------------------*/

void
NO_logic(char * logic)
{
#ifdef DEBUG_NO
  my_message("Setting up the NO module for logic %s.\n", logic);
#endif
  if (logic == NULL ||
      strcmp(logic, "AUFLIA") == 0 ||
      strcmp(logic, "AUFLIRA") == 0 ||
      strcmp(logic, "AUFNIRA") == 0 ||
      strcmp(logic, "QF_AUFLIA") == 0 ||
      strcmp(logic, "QF_IDL") == 0 ||
      strcmp(logic, "QF_LIA") == 0 ||
      strcmp(logic, "QF_LRA") == 0 ||
      strcmp(logic, "QF_NIA") == 0 ||
      strcmp(logic, "QF_RDL") == 0 ||
      strcmp(logic, "QF_UFIDL") == 0 ||
      strcmp(logic, "QF_UFLIA") == 0 ||
      strcmp(logic, "QF_UFLRA") == 0 ||
      strcmp(logic, "UNKNOWN") == 0)
    {
      symb_dp_mask(FUNCTION_SUM) |= dp_mask_arith;
      symb_dp_mask(FUNCTION_PROD) |= dp_mask_arith;
      symb_dp_mask(FUNCTION_UNARY_MINUS) |= dp_mask_arith;
      symb_dp_mask(FUNCTION_UNARY_MINUS_ALT) |= dp_mask_arith;
      symb_dp_mask(FUNCTION_MINUS) |= dp_mask_arith;
      symb_dp_mask(FUNCTION_DIV) |= dp_mask_arith;
      symb_dp_mask(PREDICATE_LESS) |= dp_mask_arith;
      symb_dp_mask(PREDICATE_LEQ) |= dp_mask_arith;

      /*
      if (logic == NULL)
	{
	  symb_dp_mask(FUNCTION_SELECT) |= E_mask;
	  symb_dp_mask(FUNCTION_STORE) |= E_mask;
	}
      */
    }

  /*
  if (logic != NULL &&
      (strcmp(logic, "AUFLIRA") == 0 ||
       strcmp(logic, "AUFNIRA") == 0))
    {
      symb_dp_mask(FUNCTION_SELECT) |= E_mask;
      symb_dp_mask(FUNCTION_STORE) |= E_mask;
    }
  */
}

/*--------------------------------------------------------------*/

void
NO_done(void)
{
  unsigned i, j;
#ifdef PROOF
  resolution_chain_size = 0;
  resolution_chain_allocated = 0;
  free(resolution_chain);
#endif
  model_equality_generation = 0;
  while (undo_level)
    undo_level_del();
  inst_done();
  for (i = 0, j = stack_size(NO_dp_table); i < j; i++) {
    GET_DP(i)->done();
    free(GET_DP(i)->name);
    free(GET_DP(i));
  }
  undo_done();
  stack_free(NO_dp_table);
}

/*----------------------------------------------------------------*/

void
NO_reset(void)
{
  my_error("not implemented");
}
