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
  Implementation of private interface for veriT
  --------------------------------------------------------------
*/

#define VERIT_HASH_SIZE 100

#include "general.h"
#include "hash.h"
#include "statistics.h"
#include "response.h"
#include "dll.h"

#include "config.h"
#include "complete.h"
#define CC_ADD_ALL_DAGS_BEFORE
#include "congruence.h"
#include "DAG.h"
#ifdef DEBUG
#define DIRTY_PRINT
#ifdef DIRTY_PRINT
#include "DAG-graph-py-out.h"
#endif
#endif
#include "DAG-saucy-out.h"
#include "DAG-tmp.h"
#include "DAG-ptr.h"
#include "DAG-print.h"
#include "clue.h"
#include "arith.h"
#include "number.h"
#include "ite-elim.h"
#include "NO.h"
#include "pre.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "bool.h"
#include "global.h"
#include "veriT.h"
#include "veriT-status.h"
#include "simplify.h"
#include "simp-unit.h"
#ifdef DEBUG
#include "literal.h"
#endif
#include "options.h"
#include "veriT-signal.h"

static Tstatus status = SAT;
static Tstack_DAG table_lemma;
/* PF buffer table for clauses between theory reasoner and SAT solver */
static Tstack_clause clauses;
/* PF buffer table for lemmas between theory reasoner and SAT solver */
static Tstack_DAG lemmas;

#ifdef DEBUG
/**
   \addtogroup arguments_developer

   - --check-deduced

   Generates files with verification conditions in SMT format for each
   conflict clause, model and lemma found. Useful to debug consistency
   of the theory solver (only available when compiled with DEBUG
   defined). */
static bool check_deduced;
/**
   \addtogroup arguments_developer

   - --dump-abstract-models

   Generates files in DIMACS format with the propositional abstraction
   of the model, the lemmas and conflict clauses that have been given
   to the boolean engine. Useful to debug consistency (only available
   when compiled with DEBUG defined). */
static bool dump_abstract_models;
#endif

extern bool option_print_simp_and_exit;
extern char * output_format;

#if STATS_LEVEL > 0
static unsigned stat_total_time;
static unsigned stat_pre_time;
#endif
#if STATS_LEVEL > 1
static unsigned stat_nb_clauses;
static unsigned stat_nb_binary_clauses;
#endif

/*
  --------------------------------------------------------------
  Helpers
  --------------------------------------------------------------
*/

static int
DAG_polarity(TDAG DAG)
/* PF returns the polarity of a literal */
{
  int polarity = 1;
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      DAG = DAG_arg0(DAG);
      polarity = 1 - polarity;
    }
  return polarity;
}

/*--------------------------------------------------------------*/

static TDAG
DAG_atom(TDAG DAG)
/* PF returns the atom of a literal */
{
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    DAG = DAG_arg0(DAG);
  return DAG;
}

/*--------------------------------------------------------------*/
static void
veriT_check_platform (void)
{
  unsigned tmp;
  if (!(DP_MAX <= sizeof(unsigned) * 8))
    veriT_error("Platform not supported (size of unsigned test failed).");
  tmp = 1;
  tmp <<= (DP_MAX - 1);
  tmp >>= (DP_MAX - 1);
  if (tmp != 1)
    veriT_error("Platform not supported (mask test failed).");
}

/*--------------------------------------------------------------*/

static void
veriT_add_watch_aux(TDAG DAG)
/* PF put watch on ground, quantifier-free, lambda, ite-free, atoms */
{
  unsigned i;
  if (DAG_tmp_bool[DAG])
    return;
  DAG_tmp_bool[DAG] = 1;
  if (!boolean_connector(DAG_symb(DAG)))
    {
      if (!DAG_quant(DAG))
	NO_watch(DAG_to_lit(DAG));
      return;
    }  
  for (i = 0; i < DAG_arity(DAG); i++)
    veriT_add_watch_aux(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief adds all quantifier-free atoms to a watch list
   \param DAG the formula
   \remarks Non destructive
   \pre DAG should be lambda and ite free on all quantifier-free atoms.
   This should be the case after going through pre.c (preprocessing)
*/
static void
veriT_add_watch(TDAG DAG)
{
  DAG_tmp_reserve();
  veriT_add_watch_aux(DAG);
  DAG_tmp_reset_bool(DAG);
  DAG_tmp_release();
}

/*--------------------------------------------------------------*/

#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
Tstack_clause recheck_clauses = NULL;
Tstack_DAG recheck_formulas = NULL;

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_store_input(TDAG DAG)
{
  stack_push(recheck_formulas, DAG_dup(DAG));
}

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_store_clauses(Tstack_clause clauses)
{
  unsigned i;
  for (i = 0; i < stack_size(clauses); i++)
    stack_push(recheck_clauses, clause_dup(stack_get(clauses, i)));
}

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_store_lemmas(Tstack_DAG lemmas)
{
  unsigned i;
  for (i = 0; i < stack_size(lemmas); i++)
    stack_push(recheck_formulas, DAG_dup(stack_get(lemmas, i)));
}

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_init(void)
{
  stack_INIT(recheck_clauses);
  stack_INIT(recheck_formulas);
}

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_out(Tstatus status)
{
  bool_recheck("boolean.cnf", status, recheck_formulas, recheck_clauses);
}

/*--------------------------------------------------------------*/

void
veriT_boolean_abstraction_done(void)
{
  while (!stack_is_empty(recheck_clauses))
    clause_free(stack_pop(recheck_clauses));
  stack_free(recheck_clauses);
  while (!stack_is_empty(recheck_formulas))
    DAG_free(stack_pop(recheck_formulas));
  stack_free(recheck_formulas);
}
#endif

/*--------------------------------------------------------------*/

#if STATS_LEVEL > 1
static void
count_binary_clauses(Tclause clause)
{
  if (clause->nb_lits == 2)
    stats_counter_inc(stat_nb_binary_clauses);
}      
#endif
/*
  --------------------------------------------------------------
  Assertion stack
  --------------------------------------------------------------
*/

typedef struct TSassertion_set
{
  unsigned level;
  Tstack_DAG DAG_stack; /**< DAGs pushed at current level */
} Tassertion_set;

TSstack(_assertion_set, Tassertion_set);

static Tstack_assertion_set stack = NULL;
static unsigned current_level = 0;
static unsigned last_checked_level = 0;

/*--------------------------------------------------------------*/

static void
verit_stack_push(void)
{
  if (!stack)
    veriT_error("verit_stack_push: internal error");
  assert(stack_size(stack) == current_level);
  stack_inc(stack);
  stack_top(stack).level = ++current_level;
  stack_INIT(stack_top(stack).DAG_stack);
}

/*--------------------------------------------------------------*/

static void
verit_stack_push_n(unsigned n)
{
  for (; n > 0; n--)
    verit_stack_push();
}

/*--------------------------------------------------------------*/

static void
verit_stack_add(TDAG DAG)
{
  if (!stack || !stack_size(stack))
    veriT_error ("verit_stack_add: internal error");
  assert (stack_size(stack) == current_level);
  stack_push(stack_top(stack).DAG_stack, DAG_dup(DAG));
}

/*--------------------------------------------------------------*/

static void
verit_stack_pop(void)
{
  unsigned i;
  if (!stack || !stack_size(stack))
    veriT_error("empty stack");
  assert (stack_size(stack) == current_level);
  assert (current_level > 0);
  for (i = 0; i < stack_size(stack_top(stack).DAG_stack); i++)
    DAG_free(stack_get(stack_top(stack).DAG_stack, i));
  stack_free(stack_top(stack).DAG_stack);
  stack_dec(stack);
  --current_level;
}

/*--------------------------------------------------------------*/

static void
verit_stack_pop_n(unsigned n)
{
  for (;n > 0; n--)
    verit_stack_pop ();
}

/*--------------------------------------------------------------*/

static unsigned
verit_stack_get_level(unsigned i)
{
  if (!stack || stack_size(stack) <= i)
    veriT_error("verit_stack_get_level: internal error");
  return stack_get(stack, i).level;
}

/*--------------------------------------------------------------*/

static Tstack_DAG
verit_stack_get_assertions(unsigned i)
{
  if (!stack || stack_size(stack) <= i)
    veriT_error("verit_stack_get_assertions: internal error");
  return stack_top(stack).DAG_stack;
}

/*--------------------------------------------------------------*/

static unsigned
verit_stack_length(void)
{
  if (!stack)
    veriT_error("verit_stack_length: internal error");
  return stack_size(stack);
}

/*--------------------------------------------------------------*/

static void
verit_stack_init(void)
{
  if (stack)
    veriT_error("verit_stack_init: internal error");
  stack_INIT(stack);
  verit_stack_push();
}

/*--------------------------------------------------------------*/

static void
verit_stack_done(void)
{
  unsigned i;
  if (!stack)
    veriT_error("verit_stack_done: internal error");
  for (i = stack_size(stack); i-- > 0;)
    verit_stack_pop();
  stack_free(stack);
}

/*
  --------------------------------------------------------------
  veriT main commands
  --------------------------------------------------------------
*/

void
veriT_push(unsigned n)
{
  verit_stack_push_n(n);
}

/*--------------------------------------------------------------*/

void
veriT_pop(unsigned n)
{
  status = OPEN;
  last_checked_level = 0;
  /* TODO RESET EVERYTHING, UNTIL WE CAN DO BETTER */
  veriT_error("unimplemented");
  if (verit_stack_length() <= n)
    veriT_error("pop exceeds sum of pushes");
  verit_stack_pop_n(n);
}

/*--------------------------------------------------------------*/

void
veriT_assert(TDAG DAG)
{
  status = OPEN;
  if (DAG_sort(DAG) != SORT_BOOLEAN)
    veriT_error("asserting a non Boolean term");
  verit_stack_add(DAG);
}

/*--------------------------------------------------------------*/

Tstatus
veriT_check_sat(void)
{
  unsigned i, j;
  TDAG DAG1 = DAG_NULL, DAG2 = DAG_NULL;
  unsigned nb = 0;
  TDAG * PDAG = NULL;
#ifdef PROOF
  Tproof_id *Pproof_id;
#endif
  /* TODO
     Difficult things: pre process:
       where to put and how to handle non-local stuff
       what to do when veriT_pop used
  */
  if (current_level == last_checked_level)
    return status;
  assert(current_level > last_checked_level);
  assert(stack_size(stack) == current_level);

  /* PF Collect assertions */
  for (i = verit_stack_length();
       i-- > 0 && verit_stack_get_level(i) > last_checked_level; )
    {
      unsigned j;
      Tstack_DAG DAGs = verit_stack_get_assertions(i);
      MY_REALLOC(PDAG, (nb + stack_size(DAGs)) * sizeof(TDAG));
      for (j = 0; j < stack_size(DAGs); j++)
	PDAG[nb++] = stack_get(DAGs, j);
    }
  /* PF Eliminate duplicates and find contradictions */
  DAG_tmp_reserve();
  for (i = 0, j = 0; i < nb; i++)
    if (!DAG_tmp_unsigned[DAG1 = DAG_atom(PDAG[i])])
      {
	DAG_tmp_unsigned[DAG1] = (1u << DAG_polarity(PDAG[i])) | (j << 2);
	PDAG[j++] = PDAG[i];
      }
    else if ((1u << DAG_polarity(PDAG[i])) != (DAG_tmp_unsigned[DAG1] & 3))
      {
#ifdef PROOF
	Tproof_id proof_id;
	Tproof_id proof_id2;
	DAG2 = PDAG[DAG_tmp_unsigned[DAG1] >> 2];
	DAG1 = PDAG[i];
#endif
	for (i = 0; i < j; i++)
	  DAG_tmp_unsigned[DAG_atom(PDAG[i])] = 0;
#ifdef PROOF
	proof_id = proof_add_formula(DAG_dup(DAG1));
	proof_id2 = proof_add_formula(DAG_dup(DAG2));
	proof_resolve(2, proof_id, proof_id2);
	proof_unsatisfiable();
#endif
	free(PDAG);
	status = UNSAT;
	DAG_tmp_release();
	return status;
      }
  nb = j;
  for (i = 0; i < nb; i++)
    DAG_tmp_unsigned[DAG_atom(PDAG[i])] = 0;
  DAG_tmp_release();

  if (!nb)
    {
      status = SAT;
#ifdef PROOF
      proof_satisfiable();
#endif     
      return status;
    }

#if STATS_LEVEL > 0
  stats_timer_start(stat_pre_time);
#endif
#ifdef PROOF
  MY_MALLOC(Pproof_id, nb * sizeof(Tproof_id));
  for (i = 0; i < nb; i++)
    Pproof_id[i] = proof_add_formula(DAG_dup(PDAG[i]));
  for (i = 0; i < nb; i++)
    DAG_dup(PDAG[i]);
  pre_process_array(nb, PDAG, Pproof_id);
  for (i = 0; i < nb; i++)
    complete_add(PDAG[i]);
#else
  {
    TDAG * PDAG2;
    MY_MALLOC(PDAG2, nb * sizeof(TDAG));
    for (i = 0; i < nb; i++)
      PDAG2[i] = PDAG[i];
    DAG1 = DAG_dup(DAG_new(CONNECTOR_AND, nb, PDAG2));
  }
#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
  DAG1 = DAG_dup(DAG1);
#endif
  DAG2 = pre_process(DAG1);
  if (option_print_simp_and_exit)
    {
      if (strcmp(output_format, "smtlib2") == 0)
	DAG_fprint_smt2_bench(stdout, DAG2, "unknown");
      else if (strcmp(output_format, "b") == 0)
        DAG_fprint_b(stdout, DAG2);
      else if (strcmp(output_format, "py_graph") == 0)
	DAG_graph_python_out(stdout, DAG2);
      else if (strcmp(output_format, "saucy_graph") == 0)
	DAG_search_automorphisms(DAG2);
    }
  complete_add(DAG2);
#endif

#if STATS_LEVEL > 0
  stats_timer_stop(stat_pre_time);
#endif
#ifdef PROOF
  for (i = 0; i < nb; i++)
    bool_add(PDAG[i], Pproof_id[i]);
  free(Pproof_id);
  NO_push(0);
  for (i = 0; i < nb; i++)
    veriT_add_watch(PDAG[i]);
  for (i = 0; i < nb; i++)
    DAG_free(PDAG[i]);
#else
  bool_add(DAG2);
  if (option_print_simp_and_exit)
    {
      free(PDAG);
      return status = UNDEF;
    }
  /* TODO really here?  Not after add_watch???
     Anyway this is a dirty hack and should not exist */
  NO_push(0);
  veriT_add_watch(DAG2);
#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
  if (check_deduced)
    {
      if (DAG2 != DAG1)
	my_warning("Input formula changed by preprocessing.\n");
      veriT_boolean_abstraction_store_input(DAG2);
    }
  DAG_free(DAG1);
#endif
  DAG_free(DAG2);
#endif

  free(PDAG);
  last_checked_level = current_level;
  bool_prepare();
  /* TODO there should be a pop corresponding to dirty NO_pop();
     above.  I let the module disposal do the work, otherwise model
     does not correspond. */
  return veriT_solve();
}

/*
  --------------------------------------------------------------
  veriT miscellaneous
  --------------------------------------------------------------
*/

int
veriT_complete(void)
{
  return complete_check();
}

/*--------------------------------------------------------------*/

/* TODO make sure it fails if unknown logic */
void
veriT_logic(char * logic)
{
  DAG_smtlib_logic_set(logic);
  NO_logic(logic);
  pre_logic(logic);
  complete_logic(logic);
}

/*--------------------------------------------------------------*/

void
veriT_model(void)
{
  /* TODO this only works partially
     Especially with arithmetics: if a variable is assigned a value by
     the arithmetic module, and if this value is not explicitely present in
     the congruence module, then this function will fail to associate
     the variable and the value */
  CC_model(veriT_out_no_newline);
}

/*
  --------------------------------------------------------------
  public old functions
  --------------------------------------------------------------
*/

#ifdef DEBUG
void
veriT_print_clauses (Tstack_clause clauses)
{
  unsigned i;
  static int conflict_no = 0;
  for (i = 0; i < stack_size(clauses); i++)
    {
      FILE *file;
      char filename[128];
      unsigned j;
      TDAG * PDAG;
      Tclause clause = (Tclause) stack_get(clauses, i);
      sprintf (filename, "conflict-%05d.smt2", ++conflict_no);
      file = fopen (filename, "w");
      MY_MALLOC(PDAG, clause->nb_lits * sizeof(TDAG));
      for (j = 0; j < clause->nb_lits; j++)
	{
	  if (lit_pol(clause->lits[j]))
	    PDAG[j] = DAG_not(var_to_DAG(lit_var(clause->lits[j])));
	  else
	    PDAG[j] = var_to_DAG(lit_var(clause->lits[j]));
	  DAG_dup(PDAG[j]);
	}
      DAG_fprint_smt2_set (file, PDAG, clause->nb_lits, "unsat");
      for (j = 0; j < clause->nb_lits; j++)
	DAG_free(PDAG[j]);
      free(PDAG);
      fclose (file);
      fprintf(stderr, "File %s written.\n", filename);
    }
}
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG
static void
veriT_print_literals(TDAG * literals, unsigned nb,
		     char * filename, char * status)
{
  FILE * file = fopen(filename, "w");
  DAG_fprint_smt2_set(file, literals, nb, status);
  fprintf(stderr, "File %s written.\n", filename);
  fclose(file);
}
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
veriT_dump_literals(char * status)
{
  int i;
  TDAG * dump;
  char filename[128];
  static unsigned count = 0;
  sprintf(filename, "dump-%u.smt2", ++count);
  MY_MALLOC(dump, bool_model_size * sizeof (TDAG));
  for (i = 0; i < bool_model_size; i++)
    {
      int literal = bool_model_Q[i];
      TDAG DAG = var_to_DAG(lit_var(literal));
      dump[i] = lit_pol(literal)? DAG : DAG_not(DAG);
    }
  veriT_print_literals(dump, bool_model_size, filename, status);
  free(dump);
}
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
veriT_print_lemmas(Tstack_DAG lemmas)
{
  unsigned i;
  static int lemma_no = 0;
  for (i = 0; i < stack_size(lemmas); i++)
    {
      FILE *file;
      char filename[128];
      TDAG DAG = stack_get(lemmas, i);
      TDAG DAG2 = DAG_dup(DAG_not(DAG));
      sprintf(filename, "lemma-%d.smt2", ++lemma_no);
      file = fopen(filename, "w");
      DAG_fprint_smt2_bench(file, DAG2, "unsat");
      fprintf(stderr, "File %s written.\n", filename);
      DAG_free(DAG2);
      fclose(file);
    }
}
#endif

/*--------------------------------------------------------------*/

static void
veriT_add_lemma(TDAG lemma)
/* PF add the lemma without preprocessing.  For internal use */
{
  /* PF2DD I think you changed this to table_push(table_lemma, DAG_dup(lemma));
     However, like this, it is inconsistent with the generation from dl.
     I think we need to discuss this issue. */
  stack_push(table_lemma, lemma);
  bool_add(lemma OPTC_PROOF(proof_get_lemma_id (lemma)));
}

/*--------------------------------------------------------------*/

#ifdef DEBUG
static void
veriT_output_model(void)
{
  static unsigned i = 0;
  char filename[128];
  unsigned j, n;
  TDAG * PDAG;
  sprintf(filename, "model-%05d.smt2", ++i);
  veriT_get_model(&n, &PDAG);
  if (!n)
    veriT_print_literals(&DAG_TRUE, 1, filename, "sat");
  else
    veriT_print_literals(PDAG, n, filename, "sat");
  for (j = 0; j < n; j++)
    DAG_free(PDAG[j]);
  free(PDAG);
}
#endif

/*--------------------------------------------------------------*/


#if STATS_LEVEL > 0
#define VERIT_SOLVE_TIMER_START stats_timer_start(stat_total_time);
#define VERIT_SOLVE_TIMER_STOP stats_timer_stop(stat_total_time);
#else
#define VERIT_SOLVE_TIMER_START
#define VERIT_SOLVE_TIMER_STOP
#endif

#ifdef DEBUG
#define VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS				\
  if (status == SAT && check_deduced)					\
    veriT_output_model();						\
  if (dump_abstract_models)						\
    veriT_dump_literals(NO_status == UNSAT ? "unsat" :			\
			(complete_check() ? "sat" : "unknown"));
#define VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS2				\
  if (dump_abstract_models)						\
    veriT_dump_literals(NO_status == UNSAT ? "unsat" :			\
			(complete_check() && NO_quiet() ? "sat" :	\
			 "unknown"));
#define VERIT_SOLVE_CHECK_DEDUCED				\
  if (check_deduced)						\
    {								\
      veriT_print_clauses(clauses);				\
      veriT_print_lemmas(lemmas);				\
    }
#else
#define VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS
#define VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS2
#define VERIT_SOLVE_CHECK_DEDUCED
#endif

#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
#define VERIT_SOLVE_RECHECK_UNSAT				\
  if (check_deduced)						\
    {								\
      veriT_boolean_abstraction_store_clauses(clauses);	        \
      veriT_boolean_abstraction_store_lemmas(lemmas);		\
    }
#else
#define VERIT_SOLVE_RECHECK_UNSAT
#endif


#ifdef BOOL_STAT
#define VERIT_SOLVE_BOOL_STAT						\
  {									\
    int i = 0, j = 0, k;						\
    if (stack_size(clauses) == 1)					\
      {									\
	Tclause clause = stack_get(clauses,0);				\
	i = j = bool_get_level(clause->lits[0]);			\
	/* bool_get_level has been suppressed around rev 1722 */	\
	for (k = 1; k < clause->nb_lits; k++)				\
	  {								\
	    int tmp = bool_get_level(clause->lits[k]);			\
	    if (tmp > i)						\
	      {								\
		j = i;							\
		i = tmp;						\
	      }								\
	    else if (tmp > j)						\
	      j = tmp;							\
	  }								\
      }									\
    for (k = 0; k < bool_model_size && bool_model_Q_level[k] == 0; k++); \
    my_message("Boolean model: same %6d, size %6d, root %6d, dec %6d, max dec %6d," \
	       "Conflict clause: largest depth %6d, forelargest depth %6d," \
	       " largest depth %6d, forelargest depth %6d\n",		\
	       bool_model_same, bool_model_size, k,			\
	       bool_model_same?bool_model_Q_level[bool_model_same - 1]:0, \
	       bool_model_Q_level[bool_model_size - 1],			\
	       i, j,							\
	       i>=0?bool_model_Q_level[i]:0, j>=0?bool_model_Q_level[j]:0); \
  }
#else
#define VERIT_SOLVE_BOOL_STAT
#endif

#if STATS_LEVEL > 0 && defined(OPTION_CHECK_TIME)
#define VERIT_SOLVE_OPTION_CHECK_TIME				\
  if (option_max_time &&					\
      stats_timer_get(stat_total_time) > option_max_time)	\
    my_error("Time exceeded\n");
#else
#define VERIT_SOLVE_OPTION_CHECK_TIME
#endif

#if STATS_LEVEL > 1						
#define VERIT_SOLVE_STAT_BINARY_CLAUSES				\
  stats_counter_add(stat_nb_clauses, stack_size(clauses));	\
  stack_apply(clauses, count_binary_clauses);
#else
#define VERIT_SOLVE_STAT_BINARY_CLAUSES
#endif

/*--------------------------------------------------------------*/

/* DD+PF solve PDPLL_veriT until model found or UNSAT found */
Tstatus
veriT_solve(void)
{
  unsigned i;
  static unsigned bool_model_size_old = 0;
  unsigned n_complete_sat = 5;
  VERIT_SOLVE_TIMER_START;
  while ((status = bool_SAT_to_level(0, n_complete_sat?-1:1)) != UNSAT)
    {
      Tstatus NO_status = UNDEF;
      if (n_complete_sat) n_complete_sat--;
      for (i = bool_model_size_old; i > bool_model_same; i--)
	NO_pop();
      for (i = bool_model_same; i < bool_model_size; i++)
	NO_status = NO_push(bool_model_Q[i]);
      bool_model_size_old = bool_model_size;
      bool_model_same = bool_model_size;
      if (bool_model_complete)
	NO_status = NO_solve();
      if (NO_status == UNDEF && bool_model_complete && NO_quiet())
	{
	  /* DD+PF for termination, it is required that eventually
	     NO clause nor lemma will be generated if the model is SAT
	     or UNDEF */
	  /* DD: if the engine is complete on the current fragment,
	     then the model should be SAT */
	  status = complete_check()?SAT:UNDEF;
	  VERIT_SOLVE_TIMER_STOP;
	  VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS;
#ifdef PROOF
	  if (status != UNSAT)
	    proof_satisfiable();
#endif
	  return status;
	}
      VERIT_SOLVE_OUTPUT_ABSTRACT_MODELS2;

      assert(!bool_model_complete || /* the model has to be completed */
	     (NO_status == UNSAT) || /* there are some conflict clause */
	     (NO_status == UNDEF && !NO_quiet())); /* there are some lemmas */
      assert(stack_size(clauses) == 0);
      assert(stack_size(lemmas) == 0);
      NO_clauses(&clauses);
      if (!NO_quiet()) NO_lemmas(&lemmas);
      VERIT_SOLVE_CHECK_DEDUCED;
      VERIT_SOLVE_STAT_BINARY_CLAUSES;
      VERIT_SOLVE_BOOL_STAT;
      stack_apply(clauses, bool_add_c_conflict);
      stack_reset(clauses);
      stack_apply(lemmas, veriT_add_lemma);
      stack_reset(lemmas);
      VERIT_SOLVE_OPTION_CHECK_TIME;
    }
  VERIT_SOLVE_TIMER_STOP;
#ifdef PROOF
  proof_unsatisfiable();
#endif
  return UNSAT;
}

/*--------------------------------------------------------------*/

/* DD+PF returns status */
Tstatus
veriT_status(void)
{
  return status;
}

/*--------------------------------------------------------------*/

/* DD+PF reset for new formulas */
void
veriT_reset(void)
{
  status = SAT;
  NO_reset();
  bool_reset();
}

/*--------------------------------------------------------------*/

/* DD+PF if status is SAT,
   *Pnb_literals gets nb of literals in model,
   *Pliterals is an array of *Pnb_literals TDAG pointing to FOL literals */
void
veriT_get_model(unsigned *Pnb_literals, TDAG **Pliterals)
{
  unsigned i, j;
  assert(status == SAT);
  MY_MALLOC((*Pliterals), (bool_model_size * sizeof(TDAG)));
  for (i = 0, j = 0; i < bool_model_size; ++i)
    {
      TDAG DAG = var_to_DAG(lit_var(bool_model_Q[i]));
      if (boolean_connector(DAG_symb(DAG)))
	continue;
      (*Pliterals)[j++] =
	DAG_dup(lit_pol(bool_model_Q[i])?DAG:DAG_not(DAG));
    }
  MY_REALLOC((*Pliterals), (j * sizeof(TDAG)));
  *Pnb_literals = j;
}

/*--------------------------------------------------------------*/

void
veriT_init(void)
{
  veriT_check_platform();
  status = SAT;
  stack_INIT(clauses);
  stack_INIT(lemmas);
  stack_INIT(table_lemma);
  veriT_signal_init();
  list_init();
  dll_init();
  response_init();
  options_init();
  DAG_init();
  verit_stack_init();
  complete_init();
  number_init();
  literal_init();
  simplify_init();
  simplify_unit_init();
  symmetry_init();
  pre_init();
  NO_init();
  bool_init();
  ite_elim_init();
#ifdef PROOF
  proof_init();
#endif
#if STATS_LEVEL > 0
  stat_total_time =
    stats_timer_new("total_time", "Total time", "%7.2f", STATS_TIMER_ALL);
  stat_pre_time =
    stats_timer_new("pre_time", "Preprocess time", "%7.2f", STATS_TIMER_ALL);
#endif
#if STATS_LEVEL > 1
  stat_nb_clauses =
    stats_counter_new("clauses", "Number of clauses generated", "%5d");
  stat_nb_binary_clauses =
    stats_counter_new("2cl_c", "Number of binary clauses generated", "%5d");
#endif
#ifdef DEBUG
  check_deduced = false;
  options_new(0, "check-deduced",
	      "Produce SMT files for conflicts, lemmas, and model.  "
	      "Useful for debugging", &check_deduced);
  dump_abstract_models = false;
  options_new(0, "dump-abstract-models",
	      "Produce SMT files for every propositional model.  "
	      "Useful for debugging", &dump_abstract_models);
#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
  veriT_boolean_abstraction_init();
#endif
#endif
}

/*--------------------------------------------------------------*/

void
veriT_done(void)
{
#if defined(DEBUG) && defined(DEBUG_RECHECK_UNSAT)
  if (check_deduced)
    veriT_boolean_abstraction_out(status);
  veriT_boolean_abstraction_done();
#endif
  stack_free(clauses);
  stack_free(lemmas);
#ifdef PROOF
  proof_done();
#endif
  ite_elim_done();
  bool_done();
  NO_done();
  pre_done();
  symmetry_done();
  simplify_unit_done();
  simplify_done();
  literal_done();
  while (!stack_is_empty(table_lemma))
    DAG_free(stack_pop(table_lemma));
  stack_free(table_lemma);
  number_done();
  complete_done();
  verit_stack_done();
  DAG_done();
  response_done();
  list_done();
  dll_done();
}
