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
  This file is responsible for encapsulating the automated
  deduction capabilities of the SPASS prover in the interface
  of a cooperating decision procedure.
  --------------------------------------------------------------
*/
#include <stdlib.h>

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
#include "veriT-status.h"
#include "simplify.h"

#include "libspass.h"

/** 
    \brief client definable disables ATP-based verification engine
*/
static int atp_options_disable = 0;

/* DD clue counters */
/**
   \brief counts how many clues have been pushed by client
    \sa spass_external_clues_counter
*/
static int atp_external_clues_counter;
/**
   \brief counts how many clues have been actually stacked.
   \sa atp_internal_clues_counter
*/
static int atp_internal_clues_counter;

/**
   \brief the current satisfiability STATUS of ATP
*/
static Tstatus status;

/**
   \brief stores lemmas that have already generated (and need not be repeated).
*/
static Thash atp_lemmas_hash;

/**
   \brief stores generated lemmas that have not been retrieved by the client
*/
static Ttable atp_new_lemmas_table;

/**
   \brief stores the clues that were received
*/
static Ttable atp_clues_table;

/* DD stores the axioms that were printed (clues modulo CC) */
Ttable atp_axioms_table;

/**
   \brief how the decision procedure is identified from the NO schema 
*/
unsigned atp_id;

/**
   \brief mask for ATP prover - used to identify symbols ATP is responsible for
*/
unsigned atp_mask;

/**
   \brief stores the inferences generated by ATP, in the order they were generated.
*/
Ttable atp_inference_table;

/**
   \brief index of the false formula derived by ATP, if any.
*/
int atp_conflict_id;

/**
   \brief set of variable equalities derived by ATP in the last call to solve.
 */
Tset atp_var_eq_set;

/**
   \brief all variable equalities derived by ATP
*/
static Ttable atp_var_eq_table; 

/**
   \brief size of the clue stack when atp_solve was last called.
*/
static int atp_solve_point;

/*--------------------------------------------------------------*/

static SPASS_TERM atp_from_quantifier (TDAG DAG);
static SPASS_TERM atp_from_DAG (TDAG DAG);

/*--------------------------------------------------------------*/

static void
DAG_free_anyway (TDAG DAG)
{
  if (DAG) DAG_free (DAG);
}

/*--------------------------------------------------------------*/

void 
atp_set_status (const Tstatus s)
{
  status = s;
}

/*--------------------------------------------------------------*/

Tstatus 
atp_status (void)
{
  return status;
}

/*--------------------------------------------------------------*/

/** 
    \brief Auxiliary routine that collects symbols and sorts of a term.
    \param DAG is the term
    \param symbs points to the list where symbols are accumulated
    \param sorts points to the list where sorts are accumulated
    
    DAG_flag(DAG) is used to mark visited terms.
    DAG_sort_misc(sort), resp. DAG_symb_misc(symb), are set when sort, resp. symb, are collected.

    \sa atp_pre
*/
static void 
atp_pre_term (TDAG DAG, Tlist * functions, Tlist * predicates, Tlist * sorts)
{
  int i;
  Tsort sort = DAG_SORT_NULL;
  Tsymb symb = DAG_SYMB_NULL;
  assert (DAG_sort (DAG) != SORT_BOOLEAN);
  if (DAG_flag(DAG)) return;
  DAG_set_flag(DAG, 1);
  
  sort = DAG_sort (DAG);
  symb = DAG_symb(DAG);
  if (!(symb->dp_mask & atp_mask)) return;
  if (DAG_sort_is_marked(sort) == 0)
    {
      *sorts = list_cons (sort, *sorts);
      DAG_sort_mark(sort);
    }
  if (DAG_symb_misc(symb) == 0 && symb->type != SYMB_VARIABLE)
    {
      *functions = list_cons (symb, *functions);
      DAG_symb_set_misc(symb) = 1;
    }
  for (i = 0; i < DAG_arity(DAG); ++i)
    atp_pre_term (DAG_arg(DAG, i), functions, predicates, sorts);

}

/*--------------------------------------------------------------*/

/** 
    \brief Auxiliary routine that collects symbols and sorts of a formula.
    \param DAG is a formula.
    \param symbs points to the list where symbols are accumulated.
    \param sorts points to the list where sorts are accumulated.
    
    DAG_flag(DAG) is used to mark visited terms.
    sort is marked and DAG_symb_misc(symb) is set when sort and symb, are collected.

    \sa atp_pre
*/
static void
atp_pre_formula (TDAG DAG, Tlist * functions, Tlist * predicates, Tlist * sorts)
{
  Tsymb symb = DAG_SYMB_NULL;
  if (DAG_flag(DAG)) return;
  DAG_set_flag(DAG, 1);

  symb = DAG_symb(DAG);
  if (boolean_connector(symb))
    {
      int i;
      for (i = 0; i < DAG_arity(DAG); ++i)
	atp_pre_formula (DAG_arg(DAG, i), functions, predicates, sorts);
    }
  else if (quantifier(symb))
    {
      atp_pre_formula (DAG_argn(DAG), functions, predicates, sorts);
    }
  else
    {
      int i;
      assert (DAG_symb_type (symb) == SYMB_PREDICATE);
      if (DAG_symb_misc(symb) == 0 && symb != PREDICATE_EQ)
	{
	  DAG_symb_set_misc(symb, 1);
	  *predicates = list_cons (symb, *predicates);
	}
      for (i = 0; i < DAG_arity(DAG); ++i)
	atp_pre_term (DAG_arg(DAG, i), functions, predicates, sorts);
    }
}

/*--------------------------------------------------------------*/

/** 
    \brief Auxiliary routine that collects symbols and sorts of a clue.
    \param clue is the inspected clue.
    \param symbs points to the list where symbols are accumulated.
    \param sorts points to the list where sorts are accumulated.
    
    DAG_flag(DAG) is used to mark visited terms.
    DAG_sort_misc(sort), resp. DAG_symb_misc(symb), are set when sort, resp. symb, are collected.

    \sa atp_pre
*/
static void
atp_pre_clue (Tclue clue, 
		       Tlist * functions, 
		       Tlist * predicates, 
		       Tlist * sorts, 
		       Tlist * formulas)
{
  if (clue == NULL) return;
  assert (clue->type == CLUE_ABSTRACT_QUANT || clue->type == CLUE_ABSTRACT_PRED || 
	  clue->type == CLUE_ABSTRACT_TERM);
  if (clue->type == CLUE_ABSTRACT_QUANT || clue->type == CLUE_ABSTRACT_PRED)
    atp_pre_formula (clue->DAG[0], functions, predicates, sorts);
  else
    atp_pre_term (clue->DAG[0], functions, predicates, sorts);
  if (clue->type == CLUE_ABSTRACT_PRED || clue->type == CLUE_ABSTRACT_QUANT)
    *formulas = list_cons (clue->DAG[0], *formulas);
}

/*--------------------------------------------------------------*/

/** \brief auxiliary routine for atp_pre */
static void
clue_DAG_reset_flag (Tclue clue)
{
  assert (clue == NULL || clue->type == CLUE_ABSTRACT_QUANT || 
	  clue->type == CLUE_ABSTRACT_PRED || clue->type == CLUE_ABSTRACT_TERM);
  DAG_reset_flag (clue->DAG[0]);
}

/*--------------------------------------------------------------*/

/*
  \brief Auxiliary routine that builds SPASS clauses.

  \param table a table storing clues

  \note
  veriT terms (type TDAG) must be mapped to SPASS terms (TERM).

  veriT terms are DAGs, while SPASS terms are trees.
  The mapping must obey a mapping from veriT symbols (type Tsymb) and sorts (type Tsort)
  to SPASS symbols (SYMBOL).
  This mapping is stored in the "flag" field in Tsymb and Tsort structures, as SYMBOL are
  integer values.

 */

static void
atp_pre (Ttable table)
{
  Tlist functions;
  Tlist predicates;
  Tlist sorts;
  Tlist axioms;
  int i;

  functions = predicates = sorts = axioms = NULL;

  for (i = 0; i < table_length (table); ++i)
    atp_pre_clue ((Tclue) table_get (table, i), 
			 &functions, &predicates, &sorts, &axioms);
  
  table_apply (table, (TFapply) clue_DAG_reset_flag);

  while (functions)
    {
      Tsymb symb = (Tsymb) list_car (functions);
      functions = list_remove (functions);
      assert(DAG_symb_misc(symb));
      DAG_symb_set_misc(symb, 0);
      DAG_symb_set_flag(symb, spass_NewFunction(symb->name, 
				       DAG_sort_arity(DAG_symb_sort(symb)) > 0 ? DAG_sort_arity(DAG_symb_sort(symb)) - 1 : DAG_sort_arity(DAG_symb_sort(symb))));
    }

  while (predicates)
    {
      Tsymb symb = (Tsymb) list_car (predicates);
      predicates = list_remove (predicates);
      assert(DAG_symb_misc(symb));
      DAG_symb_set_misc(symb, 0);
      DAG_symb_set_flag(symb, spass_NewPredicate(symb->name, 
					DAG_sort_arity(DAG_symb_sort(symb)) > 0 ? DAG_sort_arity(DAG_symb_sort(symb)) - 1 : DAG_sort_arity(DAG_symb_sort(symb))));
    }

  while (sorts)
    {
      Tsort sort = (Tsort) list_car (sorts);
      sorts = list_remove (sorts);
      assert(DAG_sort_misc(sort));
      DAG_sort_unmark(sort);
      DAG_sort_set_flag(sort, spass_NewSort(sort->name));
    }

  while (axioms)
    {
      TDAG DAG = DAG_of_ptr(list_car(axioms));
      SPASS_TERM term;
      SPASS_CLAUSE clause;
      axioms = list_remove (axioms);
      term = atp_from_DAG (DAG);
      clause = spass_NewUnitClause (term);
    }
  list_apply (axioms, (TFapply) &DAG_reset_Pflag);
}

/*--------------------------------------------------------------*/

void
atp_push (Tclue clue)
{
  if (atp_options_disable) return;
#ifdef DEBUG_ATP
  my_message("ATP: atp_push (");
  clue_fprint(stderr, clue);
  fprintf(stderr, ")\n");
#endif
  atp_external_clues_counter += 1;
  if (status == UNSAT)
    {
      clue_free (clue);
      return;
    }
  atp_internal_clues_counter += 1;
  clue_dup (clue);
  table_push(atp_clues_table, (void *) clue);
  assert (table_length (atp_clues_table) == atp_internal_clues_counter);
  atp_set_status (OPEN);
}

/*--------------------------------------------------------------*/

/* 
   DD removes a clue in LIFO order 
*/
void
atp_pop (void)
{
  if (atp_options_disable) return;
#ifdef DEBUG_ATP
  my_message("ATP: atp_pop (");
#endif
  --atp_external_clues_counter;
  atp_solve_point = 0;
  if (atp_external_clues_counter >= atp_internal_clues_counter) 
    {
#ifdef DEBUG_ATP
      fprintf (stderr, ")\n");
#endif
      return;
    }
  else
    {
      Tclue clue = (Tclue) table_top (atp_clues_table);
#ifdef DEBUG_ATP
      clue_fprint (stderr, clue);
      fprintf (stderr, ")\n");
#endif
      clue_free (clue);
      table_pop (atp_clues_table);
      --atp_internal_clues_counter;
      atp_set_status (OPEN);
    }
}

/*--------------------------------------------------------------*/

static Tstatus
atp_search ()
{
  spass_Saturate (spass_nil());
  return OPEN;
}

/*--------------------------------------------------------------*/
/**
   \brief auxiliary function for atp_solve()
*/

static int 
atp_clue_lookup (void * element, void * criterion)
{
  return !element;
}

/*--------------------------------------------------------------*/

/*
  DD runs the ATP prover on the set of clues on the clue stack; updates
  status with the result of this run; updates atp_inference_table with
  the derivation realized
*/
Tstatus
atp_solve (void)
{
  int i;

  if (atp_options_disable) return OPEN;

#ifdef DEBUG_ATP
  my_message("ATP: atp_solve\n");
  for (i = 0; i < table_length (atp_clues_table); ++i)
    {
      Tclue clue = (Tclue) table_get(atp_clues_table, i);
      clue_fprint(stderr, clue);
      fprintf (stderr, "\n");
    }
#endif

  /* DD returns if all clues are NULL */
  if (table_lookup (atp_clues_table, atp_clue_lookup, NULL) == NULL)
    {
      atp_set_status(SAT);
      return SAT;
    }
  /* DD returns if no non-NULL clue has been pushed since last call to atp_solve() */
  i = atp_solve_point; 
  while (i < table_length (atp_clues_table) && table_get (atp_clues_table, i) == NULL) ++i;
  if (i == table_length (atp_clues_table))
    return status;
  atp_solve_point = table_length (atp_clues_table);

  /* Retrieve symbols and declare  ATP */
  atp_pre (atp_clues_table);
  /* \todo run SPASS inference mechanism*/
  status = atp_search ();
  return status;
}

/*--------------------------------------------------------------*/

static void
atp_set_id (const int id)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_set_id (%u)\n", id);
#endif
  atp_id = id;
  atp_mask = 1 << id;
}

/*--------------------------------------------------------------*/

void       
atp_init (const int id)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_init (%i)\n", id);
#endif
  atp_set_id (id);
  options_new (0, "disable-atp", "Disable ATP prover", &atp_options_disable);
  atp_internal_clues_counter = atp_external_clues_counter = 0;
  atp_solve_point = 0;
  atp_set_status (OPEN);
  atp_clues_table = table_new (50, 50);
  atp_axioms_table = table_new (50, 50);
  atp_inference_table = table_new (0, 100);
  atp_var_eq_table = table_new (50, 50);
  atp_var_eq_set = set_new ((TFcmp) DAG_cmp, (TFfree) DAG_free);
  atp_lemmas_hash = hash_new (50, (TFhash) DAG_hash, (TFequal) DAG_equal, (TFfree) DAG_free);
  atp_new_lemmas_table = table_new (50, 50);
  spass_Init ();
}

/*--------------------------------------------------------------*/

void       
atp_done (void)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_done\n");
#endif
  spass_Done ();

  hash_free (&atp_lemmas_hash);
  table_apply (atp_new_lemmas_table, (TFapply) DAG_free);
  table_free (&atp_new_lemmas_table);

  table_apply (atp_axioms_table, (TFapply) DAG_free_anyway);
  table_free (&atp_axioms_table);
  table_apply (atp_clues_table, (TFapply) clue_free);
  table_free (&atp_clues_table);
}

/*--------------------------------------------------------------*/

void
atp_reset(void)
{
  if (atp_options_disable) return;
#ifdef DEBUG_ATP
  my_message("ATP: atp_reset\n");
#endif
  atp_internal_clues_counter = atp_external_clues_counter = 0;
  atp_solve_point = 0;
  if (atp_new_lemmas_table)
    {
      table_apply (atp_new_lemmas_table, (TFapply) DAG_free);
      table_erase (atp_new_lemmas_table);
    }
  table_apply (atp_clues_table, (TFapply) & clue_free);
  table_erase (atp_clues_table);
  atp_set_status (OPEN);
  
  spass_Done ();
  spass_Init ();
}

/*--------------------------------------------------------------*/

/* DD prints the current state of the decision procedure (TODO) */
void
atp_print (FILE * file)
{
}

/*--------------------------------------------------------------*/

/* DD stores in table 'premisses' the inferences given to ATP that were
   used to derive inference 'id'; each inference is visited at most
   once: the visited inferences see their 'processed' flag set, and
   are stored into table 'visited'.
    */

/*
void
atp_collect_premisses_aux (const int id, Titable premisses, Titable visited)
{
  Tinference inference;
  assert (id <= table_length (atp_inference_table));
  inference = table_get (atp_inference_table, id);
  if (inference->processed) return;
  inference->processed = 1;
  itable_push (visited, id);
  
  if (id - 1 < table_length (atp_clues_table))
    {
      itable_push (premisses, id - 1);
    }
  else
    {
      Tlistint ptr;
      for (ptr = inference->premisses; ptr; ptr = ptr->cdr)
	e_collect_premisses_aux (ptr->car, premisses, visited);
    }
}
*/
/*--------------------------------------------------------------*/
/* DD list is a list of inference identifiers; premisses is a pointer
   to a list of clues. the function adds to premisses all the clues
   that have been employed to derive the identified inferences. */
 /*
void
atp_collect_premisses (int id, Titable premisses)
{
  Titable visited = itable_new (20, 20);
  int i;

  atp_collect_premisses_aux (id, premisses, visited);
  for (i = 0; i < itable_length (visited); ++i)
    ((Tinference) table_get(atp_inference_table, itable_get(visited, i)))->processed = 0;
  itable_free (&visited);
}
*/

/*--------------------------------------------------------------*/
/* DD list contains inference identifiers; returns a list of all the
   clues employed to derive the identified inferences. */
Tlist
atp_collect_clues (int id)
{
  Titable premisses = itable_new (20, 20);
  Tlist result = NULL;
  int i;

  /* atp_collect_premisses (id, premisses); */
  for (i = 0; i < itable_length (premisses); ++i)
    {
      Tclue clue = (Tclue) NULL /* table_get (atp_clues_table, itable_get (premisses, i)) */; 
      result = list_cons ((void *) clue, result);
    }
  itable_free (&premisses);
  return result;
}

/*--------------------------------------------------------------*/

/* DD returns the clues that were used to derive a given clue */
Tlist
atp_premisses (const Tclue clue)
{
  assert (!atp_options_disable);
#ifdef DEBUG_ATP
  my_message("ATP: atp_premisses (");
  clue_fprint(stderr, clue);
  fprintf(stderr, ")\n");
  print_clues_list ((Tlist) clue->proof.arith);
#endif
  return clue->proof.arith;
}

/*--------------------------------------------------------------*/

/* DD returns the conflict set */
#ifdef PROOF
Tlist
atp_conflict (Tproofid * Pproof_id)
#else
Tlist
atp_conflict (void)
#endif
{
  Tlist result;
#ifdef PROOF
  *Pproof_id = 0;
#endif
#ifdef DEBUG_ATP
  my_message("ATP: atp_conflict %i\n", atp_conflict_id);
#endif
  assert (!atp_options_disable);
  assert (status == UNSAT);
  result = atp_collect_clues (atp_conflict_id);
#ifdef DEBUG_ATP
  print_clues_list(result);
#endif
  return result;
}

/*--------------------------------------------------------------*/

/* DD tests if the procedure has derived variable equalities */
int
atp_eq_queue_empty(void)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_eq_queue_empty: %i\n", table_empty (atp_var_eq_table));
#endif
  return table_empty (atp_var_eq_table);
}

/*--------------------------------------------------------------*/

/* DD removes and returns a clue to the list of variable equalities
   derived by the procedure */
Tclue
atp_eq_queue_pop(void)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_eq_queue_pop (");
  clue_fprint(stderr, (Tclue) table_top(atp_var_eq_table));
  fprintf(stderr, ")\n");
#endif
  return (Tclue) table_pop(atp_var_eq_table);
}

/*--------------------------------------------------------------*/

/* DD adds a clue to the list of variable equalities derived by the
   procedure */
void
atp_eq_queue_push(Tclue clue)
{
#ifdef DEBUG_ATP
  my_message("ATP: atp_eq_queue_push (");
  clue_fprint (stderr, clue);
  fprintf (stderr, ")\n");
#endif
  table_push (atp_var_eq_table, (void *) clue);
}

/*--------------------------------------------------------------*/
/* DD builds and returns the DAG of a lemma.  id shall be a clause in
   the saturated set of the last derivation.  the lemma is the
   implication whose antecedent is the conjunction of the hypothesis
   used to derive the clause and consequent is the clause itself.
   it returns NULL if the lemma is trivial (e.g. p => p).
*/
static TDAG 
atp_lemma (const int id)
{
  /*  Tinference inference = (Tinference) table_get (atp_inference_table, id);
  TDAG conclusion;
  TDAG antecedent;
  TDAG lemma;
  Titable premisses;
  int arity = 0;
  assert (!atp_options_disable);
  assert (inference->final);
  premisses = itable_new (20, 20);
  atp_collect_premisses (id, premisses);
  arity = itable_length (premisses);
  if (arity == 0)
    return DAG_NULL;
  else if (arity == 1)
    antecedent = DAG_of_ptr(table_get(atp_axioms_table, itable_get(premisses, 0)));
  else
    {
      int i;
      TDAG * PDAG;
      MY_MALLOC (PDAG, sizeof(TDAG) * arity);
      for (i = 0; i < arity; ++i)
	PDAG[i] = DAG_of_ptr(table_get(atp_axioms_table, itable_get(premisses, i)));
      antecedent = DAG_new (CONNECTOR_AND, arity, PDAG);
    }
  itable_free (&premisses);
  conclusion = inference->conclusion;
  if (antecedent == conclusion)
    lemma = DAG_NULL;
  else
    lemma = DAG_implies(antecedent, conclusion);
  return lemma;
  */
  return DAG_NULL;
}

/*--------------------------------------------------------------*/
/* DD pushes on table all the lemmas that were derived, i.e.  the
   clauses in the saturation set of the previous call to ATP.
*/
void atp_lemmas (Ttable table)
{
  while (!table_empty (atp_new_lemmas_table))
    {
      table_push(table, table_pop (atp_new_lemmas_table));
    }
}

/*--------------------------------------------------------------*/
/* DD tests if the module has produced lemmas */
int atp_has_lemma (void)
{
  /*
  int i;
  int result;
  */
  if (atp_options_disable) return 0;
  /*
  if (table_length (atp_new_lemmas_table) > 0) return 1;
  result = 0;

  if (table_length (atp_inference_table) > 1)
    {
      for (i = table_length (atp_inference_table) - 1; i > 0; --i)
	{
	  Tinference inference = (Tinference) table_get (atp_inference_table, i);
	  if (inference->final)
	    {
	      TDAG lemma;
	      lemma = atp_lemma (i);
	      if (lemma == DAG_NULL) continue;
	      lemma = simplify_formula (DAG_dup (lemma));
	      if (lemma == DAG_TRUE) 
		{
		  DAG_free (lemma);
		  continue;
		}
	      if (hash_lookup (atp_lemmas_hash, lemma)) continue;
	      result = 1;
	      hash_insert (atp_lemmas_hash, DAG_dup (lemma));
	      table_push (atp_new_lemmas_table, lemma);
	    }
	}
    }

  return result;
  */
  return 0;
}

/*--------------------------------------------------------------*/

static SPASS_TERM
atp_from_DAG (TDAG DAG)
{
  int i;
  SPASS_LIST args;
  SPASS_SYMBOL symbol;

  if (DAG_symb(DAG)->type == SYMB_QUANTIFIER)
    return atp_from_quantifier (DAG);

  assert (DAG_symb(DAG)->type != SYMB_QUANTIFIER);

  for (i = DAG_arity(DAG) - 1, args = spass_nil(); i >= 0; --i)
    {
      args = spass_cons (atp_from_DAG(DAG_arg(DAG, i)), args);
    }

  if (DAG_symb(DAG) == CONNECTOR_NOT)
    symbol = spass_fol_Not();
  else if (DAG_symb(DAG) == CONNECTOR_AND)
    symbol = spass_fol_And();
  else if (DAG_symb(DAG) == CONNECTOR_OR)
    symbol = spass_fol_Or();
  else if (DAG_symb(DAG) == CONNECTOR_EQUIV)
    symbol = spass_fol_Equiv();
  else if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    symbol = spass_fol_Implies();
  else if (DAG_symb(DAG) == CONNECTOR_AND)
    symbol = spass_fol_And();
  else if (DAG_symb(DAG) == PREDICATE_EQ)
    symbol = spass_fol_Equality ();
  else if (DAG_symb(DAG) == BOOLEAN_TRUE)
    symbol = spass_fol_True ();
  else if (DAG_symb(DAG) == BOOLEAN_FALSE)
    symbol = spass_fol_False ();
  else
    {
      symbol = (SPASS_SYMBOL) DAG_symb_flag(DAG_symb(DAG));
    }
  return spass_term_Create (symbol, args);
}

/*--------------------------------------------------------------*/

static SPASS_TERM
atp_from_quantifier (TDAG DAG)
{
  int i;
  SPASS_LIST args;
  SPASS_LIST vars;
  SPASS_TERM term1;
  SPASS_TERM term2;
  SPASS_SYMBOL symbol;

  assert (DAG_arity(DAG) > 1);

  for (i = 0, vars = spass_nil(); i < DAG_arity(DAG) - 1; ++i)
    {
      SPASS_SYMBOL symbol = spass_NewVariable ();
      term1 = spass_term_Create (symbol, spass_nil());
      vars = spass_cons (term1, vars);
      DAG_set_flag(DAG_arg(DAG, i), symbol);
    }

  term1 = atp_from_DAG (DAG_argn(src));

  /* DD the logic here is the same as in dfg_CreateQuantifier from SPASS */
  if (DAG_symb(DAG) == QUANTIFIER_FORALL)
    {
      symbol = spass_fol_All();
      /* the conjunction of all sort terms implies term1 */
      if (DAG_symb(DAG_argn(src)) == CONNECTOR_OR)
	{
	  /* Special treatment if matrix is a disjunction like 
	     in clauses: add all sort terms negated to the args
	     of the disjunction. */
	  assert (spass_term_TopSymbol(term1) == spass_fol_Or());
	  args = spass_term_ArgumentList (term1);
	  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
	    {
	      TDAG DAG0 = DAG_arg(DAG, i);
	      args = 
              spass_cons(Create(spass_fol_Not(), 
                                           spass_list(spass_term_Create((SPASS_SYMBOL) DAG_sort_flag(DAG_symb_sort(DAG_symb(DAG0))),
                                                                        spass_list((SPASS_TERM) DAG_flag(DAG0))))),
                         args);
	    }
	  term2 = spass_term_Create(spass_fol_Or(), args);
	} 
      else 
	{
	  /* not a disjunction, so build an implication */
	  if (DAG_arity(DAG) > 2) 
	    {
	      /* more than one sort term */
	      SPASS_TERM term3;
	      args = spass_nil ();
	      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
		{
		  TDAG DAG0 = DAG_arg(DAG, i);
		  assert (DAG_symb(DAG0)->type == SYMB_VARIABLE);
		  args = 
                  spass_cons(spass_term_Create((SPASS_SYMBOL) DAG_sort_flag(DAG_symb_sort(DAG_symb(DAG0))),
                                               spass_list(spass_term_Create((SPASS_SYMBOL) DAG_symb_flag(DAG_symb(DAG0)),
                                                                            spass_nil()))),
                             args);
		}
	      term3 = spass_term_Create (spass_fol_And(), args);
	      term2 = spass_term_Create (spass_fol_Implies(), spass_cons (term3, spass_list (term1)));
	    }
	  else
	    {
	      /* only one sort term */
	      SPASS_TERM term3;
	      term3 = 
              spass_term_Create((SPASS_SYMBOL) DAG_sort_flag(DAG_symb_sort(DAG_symb(DAG))),
                                spass_list(spass_term_Create((SPASS_SYMBOL) DAG_symb_flag(DAG_symb(DAG)),
                                                             spass_nil())));
	      term2 = spass_term_Create(spass_fol_Implies(), spass_cons(term3, spass_list(term1)));
	    } 
	}
    }
  else 
    {
      /* The conjunction of all sortterms and term1 */
      assert (DAG_symb(DAG) == QUANTIFIER_EXISTS);
      symbol = spass_fol_Exist();
      
      if (DAG_symb(DAG_argn(src)) == CONNECTOR_AND)
	{
	  /* Special treatment if <Term> is a term with "and" like */
	  /* in clauses: add all sort terms to the args of the "and" */
	  args = spass_term_ArgumentList (term1);
	  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
	    {
	      TDAG DAG0 = DAG_arg(DAG, i);
	      args = 
              spass_cons(spass_term_Create((SPASS_SYMBOL) DAG_sort_flag(DAG_symb_sort(DAG_symb(DAG0))),
					    spass_list((SPASS_TERM) DAG_tmp_DAG[DAG0])),
                         args);
	    }
	  term2 = spass_term_Create (spass_fol_And(), args);
	} 
      else 
	{
	  /* No "and" term, so build the conjunction term */
	  SPASS_TERM term3;
	  args = spass_nil ();
	  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
	    {
	      TDAG DAG0 = DAG_arg(DAG, i);
	      args = 
              spass_cons(spass_term_Create((SPASS_SYMBOL) DAG_sort_flag(DAG_symb_sort(DAG_symb(DAG0))),
                                           spass_list((SPASS_TERM) DAG_tmp_DAG[DAG0]),
                         args);
	    }
	  term3 = spass_term_Create(spass_fol_And(), args);
	  term2 = spass_term_Create(spass_fol_Implies(), spass_cons(term3, spass_list(term1)));
	}
    }
  return spass_fol_CreateQuantifier(symbol, vars, spass_list(term2));
}
