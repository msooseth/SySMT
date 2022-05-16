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
  SAT solver interface module
  --------------------------------------------------------------
*/

#include <stdlib.h>
#include <limits.h>
#include <string.h>

#include "config.h"
#include "types.h"
#include "general.h"
#include "options.h"
#include "statistics.h"
#include "DAG-ptr.h"

/* #define DEBUG_BOOL */

#ifdef DEBUG_BOOL
#include "DAG-print.h"
#endif
#include "bool.h"
#include "cnf.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "veriT-status.h"

unsigned bool_model_complete = 0; /* IMPROVE redundant: this can be deduced from status */
/* #define STAT_MIN_MODEL */
#ifdef STAT_MIN_MODEL
static unsigned stat_minimize_time;
static unsigned stat_minimize_lit1a;
static unsigned stat_minimize_lit1b;
static unsigned stat_minimize_lit2a;
static unsigned stat_minimize_lit2b;
static unsigned stat_minimize_lit3a;
static unsigned stat_minimize_lit3b;
static unsigned stat_minimize_lit4a;
static unsigned stat_minimize_lit4b;
static unsigned stat_minimize_lit_origa;
static unsigned stat_minimize_lit_origb;
#endif

/*
  --------------------------------------------------------------
  Hints
  --------------------------------------------------------------
*/

Tlit    *bool_hint = NULL;
unsigned bool_hint_first = 0;
unsigned bool_hint_last = 0;
unsigned bool_hint_size = 0;

/*--------------------------------------------------------------*/

void
bool_hint_add(Tlit lit)
{
  if (bool_hint_last == bool_hint_size)
    {
      bool_hint_size *= 2;
      MY_REALLOC(bool_hint, bool_hint_size * sizeof(Tlit));
    }
  bool_hint[bool_hint_last++] = lit;
#ifdef DEBUG_CC
  my_DAG_message("hint_add %d, %d, %d %D\n",
		 lit, bool_hint_last, bool_hint_first,
		 var_to_DAG(lit_var(lit)));
#endif
}

/*
  --------------------------------------------------------------
  Real things begin here
  --------------------------------------------------------------
*/

void
bool_prepare(void)
{
#if 0
  /* disable SAT solver decision on variables introduced for definitional cnf */
  unsigned i;
  for (i = 1; i < var_max; i++)
    if (boolean_connector(DAG_symb(literal_to_DAG(i))))
      SAT_var_block_decide(i);
#endif
}

/*--------------------------------------------------------------*/

unsigned
bool_get_declev(Tlit lit)
{
  return SAT_lit_level(lit);
}

/*--------------------------------------------------------------*/

unsigned
bool_get_current_declev(void)
{
  return SAT_level;
}

/*--------------------------------------------------------------*/

Tstatus
bool_SAT_to_level(unsigned level, int max_dec)
{
  Tstatus bool_status = UNDEF;
  switch (SAT_solve_2(level, max_dec))
    {
    case SAT_STATUS_UNSAT:
      return UNSAT;
    case SAT_STATUS_UNDEF:
      bool_status = UNDEF;
      break;
    case SAT_STATUS_SAT:
      bool_status = SAT;
      break;
    default:
      my_error("bool_SAT_to_level: unexpected value from SAT solver\n");
    }
  /* PF IMPROVE var_max should come from the SAT solver */
  assert(SAT_literal_stack_n <= (unsigned) var_max);
  bool_model_complete = (SAT_status == SAT_STATUS_SAT);
#ifdef DEBUG_BOOL
  {
    int i;
    my_message("Bool: SAT: ");
    for (i = 0; i < SAT_literal_stack_n; i++)
      fprintf(stderr, "%d ", SAT_literal_stack[i]);
    fprintf(stderr, "\n");
    my_message("Bool: model: ");
    for (i = 0; i < bool_model_size; i++)
      fprintf(stderr, "%d ", bool_model_Q[i]);
    fprintf(stderr, "\n");
  }
#endif
  return bool_status;
}

/*--------------------------------------------------------------*/

int
bool_SAT(void)
{
  return bool_SAT_to_level(0, -1);
}

/*--------------------------------------------------------------*/

void
bool_add(TDAG formula OPTC_PROOF(Tproof_id proof_clause))
{
  Tstack_clause clauses;
  unsigned i;
  stack_INIT(clauses);
  cnf(formula, &clauses OPTC_PROOF(proof_clause));
  for (i = 0; i < stack_size(clauses); ++i)
    bool_add_c(stack_get(clauses, i));
  stack_free(clauses);
}

/*--------------------------------------------------------------*/

void
bool_add_c(Tclause clause)
{
  unsigned i;
  SAT_Tlit * lit;
  clause = clause_clean(clause);
  if (!clause)
    return;
#ifdef DEBUG_BOOL
  printf("bool_add_c : ");
  for (i = 0; i < clause->nb_lits; i++)
    printf("%d ", clause->lits[i]);
  printf("\n");
#endif
  for (i = 0; i < clause->nb_lits; i++)
    SAT_var_new_id(lit_var(clause->lits[i]));
  MY_MALLOC(lit, clause->nb_lits * sizeof(int));
  /* IMPROVE it is a pity to have to duplicate this information */
  memcpy(lit, clause->lits, clause->nb_lits * sizeof(SAT_Tlit));
#ifdef PROOF
  proof_SAT_insert(clause);
#endif
  SAT_clause_new(clause->nb_lits, lit);
  clause_free(clause);
}

/*--------------------------------------------------------------*/

/* IMPROVE bool_add_c vs. bool_add_c_conflict is a dirty quick hack */
void
bool_add_c_conflict(Tclause clause)
{
  unsigned i;
  SAT_Tlit * lit;
  clause = clause_clean(clause);
  if (!clause)
    return;
#ifdef DEBUG_BOOL
  printf("bool_add_c : ");
  for (i = 0; i < clause->nb_lits; i++)
    printf("%d ", clause->lits[i]);
  printf("\n");
#endif
  for (i = 0; i < clause->nb_lits; i++)
    SAT_var_new_id(lit_var(clause->lits[i]));
  MY_MALLOC(lit, clause->nb_lits * sizeof(int));
  /* IMPROVE it is a pity to have to duplicate this information */
  memcpy(lit, clause->lits, clause->nb_lits * sizeof(SAT_Tlit));
#ifdef PROOF
  proof_SAT_insert(clause);
#endif
  SAT_clause_new_conflict(clause->nb_lits, lit);
  clause_free(clause);
}

/*--------------------------------------------------------------*/

void
bool_recheck(char * filename, Tstatus status, 
	     Tstack_DAG formulas, Tstack_clause clauses)
{
  unsigned i, j, var_max = 0;
  Tstack_clause cnf_clauses;
  FILE * file = fopen(filename, "w");
  cnf_reset();
  stack_INIT(cnf_clauses);
  for (i = 0; i < stack_size(formulas); i++)
    cnf(stack_get(formulas, i), &cnf_clauses OPTC_PROOF(0));
  for (i = 0; i < stack_size(clauses); i++)
    stack_push(cnf_clauses, clause_dup(stack_get(clauses, i)));
  for (i = 0; i < stack_size(cnf_clauses); i++)
    {
      Tclause clause = stack_get(cnf_clauses, i);
      for (j = 0; j < clause->nb_lits; j++)
	if ((unsigned)lit_var(clause->lits[j]) > var_max)
	  var_max = lit_var(clause->lits[j]);
    }
  fprintf(file, "p cnf %d %u\n", var_max, stack_size(cnf_clauses));
  fprintf(file, "c s %s\n", status == UNSAT?"UNSATISFIABLE":"SATISFIABLE");
  for (i = 0; i < stack_size(cnf_clauses); i++)
    {
      Tclause clause = stack_get(cnf_clauses, i);
      for (j = 0; j < clause->nb_lits; j++)
	fprintf(file, "%d ", clause->lits[j]);
      fprintf(file, "0\n");
    }
  for (i = 0; i < stack_size(cnf_clauses); i++)
    clause_free(stack_get(cnf_clauses, i));
  stack_free(cnf_clauses);
  fprintf(stderr, "File %s written.\n", filename);
  fclose(file);
}

/*--------------------------------------------------------------*/

void
bool_reset(void)
{
  bool_model_complete = 0;

  SAT_done();
  SAT_init();
#ifdef PROOF
  proof_SAT_reset();
#endif

  cnf_reset();
}

/*--------------------------------------------------------------*/

#ifdef STAT_MIN_MODEL
static int
bool_model_sort_literals(const void * Pvoid1, const void * Pvoid2)
{
  const SAT_Tlit * Plit1 = Pvoid1, * Plit2 = Pvoid2;
  if (boolean_connector(DAG_symb(var_to_DAG(lit_var(*Plit2)))))
    return -1;
  if (boolean_connector(DAG_symb(var_to_DAG(lit_var(*Plit1)))))
    return 1;
  return 0;
}
#endif

/*--------------------------------------------------------------*/

void
bool_stats_model(void)
{
#ifdef STAT_MIN_MODEL
  unsigned i, n = 0, m;
  SAT_Tlit * Plit = NULL;
  if (SAT_status != SAT_STATUS_SAT)
    return;
  n = SAT_literal_stack_n;
  for (i = 0, m = n; i < n; i++)
    if (boolean_connector(DAG_symb(var_to_DAG(lit_var(SAT_literal_stack[i])))))
      m--;
  stats_counter_set(stat_minimize_lit_origa, n);
  stats_counter_set(stat_minimize_lit_origb, m);
  n = 0;
  stats_timer_start(stat_minimize_time);
  /* Basic minimalization */
  SAT_minimal_model(&Plit, &n, 0);
  for (i = 0, m = n; i < n; i++)
    if (boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))))
      m--;
  stats_counter_set(stat_minimize_lit1a, n);
  stats_counter_set(stat_minimize_lit1b, m);
  n = 0; free(Plit); Plit = NULL;
  /* Skip propagated */
  SAT_minimal_model(&Plit, &n, SAT_MIN_SKIP_PROPAGATED);
  for (i = 0, m = n; i < n; i++)
    if (boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))))
      m--;
  stats_counter_set(stat_minimize_lit2a, n);
  stats_counter_set(stat_minimize_lit2b, m);
  n = 0; free(Plit); Plit = NULL;
  /* Use tautologies */
  SAT_minimal_model(&Plit, &n, SAT_MIN_USE_TAUTOLOGIES);
  for (i = 0, m = n; i < n; i++)
    if (boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))))
      m--;
  stats_counter_set(stat_minimize_lit3a, n);
  stats_counter_set(stat_minimize_lit3b, m);
  n = 0; free(Plit); Plit = NULL;
  /* Remove abstract last */
  n = SAT_literal_stack_n;
  MY_MALLOC(Plit, n * sizeof(SAT_Tlit));
  memcpy(Plit, SAT_literal_stack, n * sizeof(SAT_Tlit));
  /* put abstract variables at the end */
  qsort(Plit, n, sizeof(SAT_Tlit), bool_model_sort_literals);
  /* check abstract variables are at the end */
  for (i = 0, m = 0; i < n; i++)
    {
      assert(!m || boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))));
      if (boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))))
	m = 1;
    }
  SAT_minimal_model(&Plit, &n,
		    SAT_MIN_SKIP_PROPAGATED | SAT_MIN_USE_TAUTOLOGIES);
  for (i = 0, m = n; i < n; i++)
    if (boolean_connector(DAG_symb(var_to_DAG(lit_var(Plit[i])))))
      m--;
  stats_counter_set(stat_minimize_lit4a, n);
  stats_counter_set(stat_minimize_lit4b, m);
  n = 0; free(Plit); Plit = NULL;
  stats_timer_stop(stat_minimize_time);
#endif
}

/*--------------------------------------------------------------*/

void
bool_init(void)
{
  bool_model_complete = 0;
  SAT_init();
  cnf_init();
  bool_hint_size = 64;
  MY_MALLOC(bool_hint, 64 * sizeof(Tlit));
#ifdef STAT_MIN_MODEL
  stat_minimize_time =
    stats_timer_new("SAT_lit_min_time", "Model minimizing time", "%7.2f",
		    STATS_TIMER_ALL);
  stat_minimize_lit_origa =
    stats_counter_new("SAT_lit_min0a", "Number of literals in unminimized model", "%5d");
  stat_minimize_lit_origb =
    stats_counter_new("SAT_lit_min0b", "Number of literals in unminimized model", "%5d");
  stat_minimize_lit1a =
    stats_counter_new("SAT_lit_min1a", "Number of literals in minimized model", "%5d");
  stat_minimize_lit1b =
    stats_counter_new("SAT_lit_min1b", "Number of literals in minimized model", "%5d");
  stat_minimize_lit2a =
    stats_counter_new("SAT_lit_min2a", "Number of literals in minimized model", "%5d");
  stat_minimize_lit2b =
    stats_counter_new("SAT_lit_min2b", "Number of literals in minimized model", "%5d");
  stat_minimize_lit3a =
    stats_counter_new("SAT_lit_min3a", "Number of literals in minimized model", "%5d");
  stat_minimize_lit3b =
    stats_counter_new("SAT_lit_min3b", "Number of literals in minimized model", "%5d");
  stat_minimize_lit4a =
    stats_counter_new("SAT_lit_min4a", "Number of literals in minimized model", "%5d");
  stat_minimize_lit4b =
    stats_counter_new("SAT_lit_min4b", "Number of literals in minimized model", "%5d");
#endif
}

/*--------------------------------------------------------------*/

void
bool_done(void)
{
  free(bool_hint);
  bool_hint_size = 0;
  cnf_done();
  SAT_done();
}
