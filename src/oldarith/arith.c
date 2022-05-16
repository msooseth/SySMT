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
  \file arith.c

  \author Diego Caminha

  \brief Arithmetic module implementation.

  This module provides the interface that can be used to have access
  to the arithmetic decision procedures. Currently there are two decision
  procedures: difference logic and linear arithmetic.

  The choice of which decision procedure is accessed is automatically
  determined by the kind of the formula been processed.

  'Arith' is a module seem by veriT as a single decision procedure.

*/

/* #define DEBUG_ARITH */

#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdbool.h>

#include "config.h"
#include "undo.h"

#include "arith.h"
#include "general.h"
#include "set.h"
#include "DAG.h"
#include "DAG-ptr.h"
#include "congruence.h"
#include "dl.h"
#include "la.h"
#include "DAG-print.h"

#ifdef PROOF
#include "proof.h"
#endif

#ifdef DEBUG_ARITH
#include "clue-print.h"
#endif

static const unsigned INIT_SIZE = 50;
static const unsigned INCREMENT = 50;

typedef struct TSDAG_num
{
  TDAG dag;
  Tnumber value;
  Tlist list_premisses;
} *TDAG_num;

/** \brief Different fragments of arithmetic handled. */
typedef enum
{
  NONE, UNKNOWN, DL, LA
} Tarith_fragment;

/* DC how the decision procedure is identified from the NO schema */
static unsigned arith_id;

/* DC mask for arith */
static unsigned arith_mask;

/* DC current status */
static Tstatus status;

/* DC integer variable appears */
static unsigned integer;

/* DC conflict set of constraints (clue) returned when UNSAT */
static Tset arith_conflict_set;

/* DC associate DAGs to numerals and list of premisses (clue) */
static Thash arith_num_hash;

/* DC Some constraint not supported was received;
   0 means everything is supported */
static int arith_not_supported = 0;

/* DC Clues received by arith */
static Ttable arith_clues_table;

static Tarith_fragment fragment;

/* ---------- history stuff (for backtracking purposes) ---------------- */

/** \brief What kind of events can be recorded. */
enum {
  NUM_SET = UNDO_OLD_ARITH,
  ARITH_PUSH,
  DL_PUSH,
  LA_PUSH,
  DL_INT,
  ARITH_NOT_SUPPORTED,
  ARITH_UNSAT,
};

/*-----------------------------------------------------------------------*/

/* DC arith_push event */
static void
history_arith_push(Tclue clue)
{
  (*(Tclue *)undo_push(ARITH_PUSH)) = clue;
}

/*-----------------------------------------------------------------------*/

/* DC undo the arith_push */
static void
hook_arith_push(Tclue * Pclue)
{
  clue_free(*Pclue);
}

/*-----------------------------------------------------------------------*/

/* DC la_push event */
static void
history_la_push(Tclue clue)
{
  undo_push(LA_PUSH);
  table_push(arith_clues_table, (void *) clue);
}

/*-----------------------------------------------------------------------*/

/* DC undo the la_push */
static void
hook_la_push(void * P)
{
#ifdef DEBUG_ARITH
  printf ("ARITH removing: ");
  clue_fprint(stdout, table_top(arith_clues_table));
  printf ("\n");
#endif
  table_pop(arith_clues_table);
  la_pop();
}

/*-----------------------------------------------------------------------*/

/* DC num table new entry event*/
static void
history_num_set(TDAG_num dag_num)
{
  (*(TDAG_num *)undo_push(NUM_SET)) = dag_num;
}

/*-----------------------------------------------------------------------*/

/* DC change num table to the previous state*/
static void
hook_num_set(TDAG_num * Pdag_num)
{
  list_free(&(*Pdag_num)->list_premisses);
  number_free((*Pdag_num)->value);
  hash_remove(arith_num_hash, (void *) *Pdag_num);
}

/*-----------------------------------------------------------------------*/

/* DC dl_push event */
static void
history_dl_push()
{
  undo_push(DL_PUSH);
}

/*-----------------------------------------------------------------------*/

/* DC undo the dl_push */
static void
hook_dl_push(void * P)
{
  dl_pop();
}

/*-----------------------------------------------------------------------*/

/* DC undo the dl_push */
static void
hook_dl_int(void * P)
{
  if (fragment == DL)
    dl_set_rdl ();
  integer = 0;
}

/*-----------------------------------------------------------------------*/

/* DC undo the dl_push */
static void
hook_arith_not_supported(void * P)
{
  arith_not_supported = 0;
}

/*-----------------------------------------------------------------------*/

static int set_clue_compare(Tclue clue1, Tclue clue2);
static void set_clue_free(const void *a);

/* DC undo the dl_push */
static void
hook_arith_unsat(void * P)
{
  status = SAT;
  set_free(&arith_conflict_set);
  arith_conflict_set = set_new((TFcmp) set_clue_compare,
			       (TFfree) set_clue_free);
}

/*-----------------------------------------------------------------------*/

/* DC initializes history */
static void
history_init (void)
{
  undo_set_hook(ARITH_PUSH, (Tundo_hook)hook_arith_push, sizeof(Tclue));
  undo_set_hook(LA_PUSH, (Tundo_hook)hook_la_push, 0);
  undo_set_hook(NUM_SET, (Tundo_hook)hook_num_set, sizeof(TDAG_num));
  undo_set_hook(DL_PUSH, (Tundo_hook)hook_dl_push, 0);
  undo_set_hook(DL_INT, (Tundo_hook)hook_dl_int, 0);
  undo_set_hook(ARITH_NOT_SUPPORTED, (Tundo_hook)hook_arith_not_supported, 0);
  undo_set_hook(ARITH_UNSAT, (Tundo_hook)hook_arith_unsat, 0);
}

/*-----------------------------------------------------------------------*/

/* DC finalizes history */
static void
history_done (void)
{
}

/*--------------------------------------------------------------------*/

/* DC hash function for a TDAG_num hash */
static unsigned
DAG_num_hash (void *id)
{
  return DAG_hash (((TDAG_num) id)->dag);
}

/*-----------------------------------------------------------------------*/

/* DC equal function for a TDAG_num hash */
static int
DAG_num_equal (void *id1, void *id2)
{
  return ((TDAG_num) id1)->dag == ((TDAG_num) id2)->dag;
}

/*-----------------------------------------------------------------------*/

/* DC free function for a TDAG_num hash */
static void
DAG_num_free (void *id)
{
  DAG_free (((TDAG_num) id)->dag);
  list_free (&(((TDAG_num) id)->list_premisses));
  free ((TDAG_num) id);
}

/*-----------------------------------------------------------------------*/

/* DC Gives (only) one warning if a not supported information is received */

static void
arith_show_warning(void)
{
  if (arith_not_supported == 0)
    {
      undo_push(ARITH_NOT_SUPPORTED);
      arith_not_supported = 1;
      my_warning("Arithmetic solver received a constraint that was not expected.\n");
      my_warning("However, it will continue and try to solve the problem.\n");
    }
}

/*-----------------------------------------------------------------------*/

/* DC returns a int used to compare clue types */
static int
clue_type_order (Tclue c)
{
  int res = 1;

  if (c->polarity)
    res <<= 5;
  switch (c->type)
    {
    case CLUE_ABSTRACT_TERM:
      res <<= 4;
      break;
    case CLUE_ABSTRACT_PRED:
      res <<= 3;
      break;
    case CLUE_MERGE:
      res <<= 2;
      break;
    case CLUE_MODEL_EQUALITY:
      res <<= 2;
      break;
    case CLUE_INEQUALITY:
      res <<= 1;
      break;
    default:
      my_error ("arith: clue_type_order: strange clue\n");
    }

  return res;
}

/*-----------------------------------------------------------------------*/

/*
 DC compares two clues and returns < 0, 0 or > 0;

 for different types:
 polarity > !polarity and
 abstract > predicate > merge > disequality;

 for same type (1 DAG):
 compare clue's "DAG int address"

 for same type (2 DAGs):
 compare clue's pair of "DAG int address"
 before comparing, "swap" if pair is not sorted
 */
static int
set_clue_compare (Tclue clue1, Tclue clue2)
{
  int result;
  if (clue1 == clue2)
    return 0;
  result = clue_type_order (clue1) - clue_type_order (clue2);
  if (result != 0)
    return result;

  if ((clue1->type == CLUE_ABSTRACT_TERM && clue2->type == CLUE_ABSTRACT_TERM)
      || (clue1->type == CLUE_ABSTRACT_PRED && clue2->type == CLUE_ABSTRACT_PRED))
    return DAG_cmp (clue1->DAG[0], clue2->DAG[0]);
  else				/* if clue has 2 DAGs */
    {
      TDAG c1d1 = clue1->DAG[0], c1d2 = clue1->DAG[1];
      TDAG c2d1 = clue2->DAG[0], c2d2 = clue2->DAG[1];
      TDAG t;
      if (c1d1 > c1d2)
	t = c1d1, c1d1 = c1d2, c1d2 = t;
      if (c2d1 > c2d2)
	t = c2d1, c2d1 = c2d2, c2d2 = t;
      result = DAG_cmp (c1d1, c2d1);
      if (result != 0)
	return result;
      return DAG_cmp (c1d2, c2d2);
    }
}

/*-----------------------------------------------------------------------*/

/* DC free function */
static void
set_clue_free (const void *a)
{
  ;
}

/*-----------------------------------------------------------------------*/
/* DC reads a number from a constant DAG */
static Tnumber
arith_DAG_readable_value (Tnumber res, TDAG constant)
{
  if (DAG_arity(constant) == 0)
    return number_from_DAG (res, constant);
  else
    return number_neg (arith_DAG_readable_value (res, DAG_arg0(constant)));
}

/*-----------------------------------------------------------------------*/

/* DC sets a id to arith */
static void
arith_set_id (const unsigned id)
{
  arith_id = id;
  arith_mask = 1 << id;
}

/*-----------------------------------------------------------------------*/

/* DC returns true when dag is of sort INTEGER */
static bool
arith_is_integer (TDAG DAG)
{
  return DAG_sort(DAG) == SORT_INTEGER;
}

/*-----------------------------------------------------------------------*/

static TDAG
arith_generate_disequality_lemma (TDAG dag1, TDAG dag2)
{
  TDAG DAG_n_1l2, DAG_n_2l1, DAG_or;

  DAG_n_1l2 = DAG_not(DAG_new_args(PREDICATE_LEQ, dag1, dag2, DAG_NULL));
  DAG_n_2l1 = DAG_not(DAG_new_args(PREDICATE_LEQ, dag2, dag1, DAG_NULL));

  DAG_or = DAG_dup(DAG_or3(DAG_eq(dag1, dag2), DAG_n_1l2, DAG_n_2l1));
#ifdef DEBUG_ARITH
  my_DAG_message ("ARITH: LEMMA generated: %D\n", DAG_or);
#endif
  return DAG_or;
}

/*-----------------------------------------------------------------------*/

/* DC inserts a list of clues in a set */
static void
set_insert_list_clue (Tset set, Tlist list)
{
  LIST_LOOP_BEGIN (list, Tclue, clue);
  set_insert (set, clue);
  LIST_LOOP_END (list);
}

/*-----------------------------------------------------------------------*/

#ifndef NDEBUG

/* DC returns true when dag is of sort REAL */
static bool
arith_is_real (TDAG DAG)
{
  return DAG_sort(DAG) == SORT_REAL;
}

#endif

/*-----------------------------------------------------------------------*/

/* DC returns true if dag is not found in num table */
static bool
arith_num_table_empty (TDAG dag)
{
  TDAG_num key, result;

  MY_MALLOC (key, sizeof (struct TSDAG_num));
  key->dag = dag;

  result = (TDAG_num) hash_lookup (arith_num_hash, (void *) key);

  free (key);

  return result == NULL;
}

/*-----------------------------------------------------------------------*/

/* DC inserts a DAG+num+premisses in the num table */
static void
arith_num_table_set (TDAG dag, Tnumber value, Tlist list_premisses)
{
  TDAG_num data;

  MY_MALLOC (data, sizeof (struct TSDAG_num));
  data->dag = dag;
  data->value = number_new ();
  number_cpy (data->value, value);
  data->list_premisses = list_cpy (list_premisses);

  DAG_dup (dag);

  hash_insert (arith_num_hash, (void *) data);

  history_num_set(data);
}

/*-----------------------------------------------------------------------*/

/* DC returns the value stored in num table[dag] */
/* PRE CONDITION, table[dag] != NULL */
static Tnumber
arith_num_table_get_value (TDAG dag)
{
  TDAG_num key, result;

  MY_MALLOC (key, sizeof (struct TSDAG_num));
  key->dag = dag;

  result = (TDAG_num) hash_lookup (arith_num_hash, (void *) key);

  free (key);

  assert (result != NULL);
  return result->value;
}

/*-----------------------------------------------------------------------*/

/* DC returns a copy of the premisses list stored in num table[dag] */
/* PRE CONDITION, table[dag] != NULL */
static Tlist
arith_num_table_get_premisses (TDAG dag)
{
  TDAG_num key, result;

  MY_MALLOC (key, sizeof (struct TSDAG_num));
  key->dag = dag;

  result = (TDAG_num) hash_lookup (arith_num_hash, (void *) key);

  free (key);

  assert (result != NULL);
  return result->list_premisses;
}

/*-----------------------------------------------------------------------*/

/* DC pushes a constraint to difference logic decision procedure */
static Tstatus
arith_dl_push (TDAG x, TDAG y, Tnumber c, Tlist list_clue)
{
  if (!integer && (arith_is_integer (x) || arith_is_integer (y)))
    {
      integer = 1;
      undo_push(DL_INT);
      dl_set_idl();
    }

  status = dl_push (x, y, c, list_clue);
  history_dl_push();
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC adds the fact that DAG is equal to a number C */
static Tstatus
arith_store_dag_equal_number (TDAG dag, Tnumber c, Tlist list_clue)
{
  if (!arith_num_table_empty (dag) && !number_equal (arith_num_table_get_value (dag), c))
    {
      set_insert_list_clue (arith_conflict_set, list_merge (list_clue, arith_num_table_get_premisses (dag)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag));
      status = UNSAT;
      return status;
    }
  arith_num_table_set (dag, c, list_clue);
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC adds the fact that DAG1 is opposite to DAG2; DAG1 = -DAG2 */
static void
arith_store_dag_opposite_dag (TDAG dag1, TDAG dag2, Tlist list_clue)
{
  Tnumber vdag2;
  if (!arith_num_table_empty (dag2))
    {
      vdag2 = number_new ();
      number_neg (number_cpy (vdag2, arith_num_table_get_value (dag2)));

      arith_store_dag_equal_number (dag1, vdag2, list_merge (list_clue, arith_num_table_get_premisses (dag2)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag2));

      number_free (vdag2);
    }
  else
    {
      arith_show_warning();
#ifdef DEBUG_ARITH
      my_DAG_warning ("ARITH: ignoring variable with unary minus \"%D\"!\n", dag2);
#endif
    }
}

/*-----------------------------------------------------------------------*/
/* DC adds the fact dag1 = dag2 + dag3 */
static void
arith_store_dag_equal_sum (TDAG dag1, TDAG dag2, TDAG dag3, Tlist list_clue)
{
  bool is_empty2 = arith_num_table_empty (dag2);
  bool is_empty3 = arith_num_table_empty (dag3);
  if (!is_empty2 && !is_empty3)
    {
      Tnumber n = number_new ();
      number_add (n, arith_num_table_get_value (dag2), arith_num_table_get_value (dag3));
      arith_store_dag_equal_number (dag1, n,
				    list_merge (list_merge
						(list_clue,
						 arith_num_table_get_premisses
						 (dag2)), arith_num_table_get_premisses (dag3)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag3));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag2));
      number_free (n);
    }
  else if (!is_empty2 && is_empty3)
    {
      Tnumber n = number_new ();
      Tlist tmp;
      number_cpy (n, arith_num_table_get_value (dag2));
      tmp = list_merge (list_clue, arith_num_table_get_premisses (dag2));
      status = arith_dl_push (dag1, dag3, n, tmp);
      status = arith_dl_push (dag3, dag1, number_neg (n), tmp);
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag2));
      number_free (n);
    }
  else if (is_empty2 && !is_empty3)
    {
      Tnumber n = number_new ();
      Tlist tmp;
      number_cpy (n, arith_num_table_get_value (dag3));
      tmp = list_merge (list_clue, arith_num_table_get_premisses (dag3));
      status = arith_dl_push (dag1, dag2, n, tmp);
      status = arith_dl_push (dag2, dag1, number_neg (n), tmp);
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag3));
      number_free (n);
    }
  else
    {
      arith_show_warning();
#ifdef DEBUG_ARITH
      my_DAG_warning
	("ARITH: \"%D = %D + %D; %D and %D\" don't have values associated!\n", dag1, dag2, dag3, dag2, dag3);
#endif
    }
}

/*-----------------------------------------------------------------------*/

#ifdef PURE_ARITH

static bool
arith_DAG_is_num (TDAG DAG)
{
  return DAG_arity(DAG) == 0 && DAG_is_number(DAG) || 
  DAG_arity(DAG) == 1 && DAG_is_number (DAG_arg0(DAG));
}

#endif

/*-----------------------------------------------------------------------*/

#ifdef PURE_ARITH

/* DC returns from a "SUM DAG" of the kind "DAG + int" the int and DAG part */
static void
arith_DAG_sum_split (TDAG DAG, TDAG * res, Tnumber * v)
{
  if (arith_DAG_is_num (DAG_arg0(DAG)))
    *v = arith_DAG_readable_value(*v, DAG_arg0(DAG)), *res = DAG_arg1(DAG);
  else if (arith_DAG_is_num (DAG_arg1(DAG)))
    *v = arith_DAG_readable_value(*v, DAG_arg1(DAG)), *res = DAG_arg0(DAG);
}

#endif

/*-----------------------------------------------------------------------*/

/* DC adds the fact that dag1 = dag2 */
static void
arith_store_dag_equal_dag (TDAG dag1, TDAG dag2, Tlist list_clue)
{
  if (!arith_num_table_empty (dag1))
    {
      arith_store_dag_equal_number (dag2, arith_num_table_get_value (dag1),
				    list_merge (list_clue, arith_num_table_get_premisses (dag1)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag1));
    }
  if (status == SAT && !arith_num_table_empty (dag2))
    {
      arith_store_dag_equal_number (dag1, arith_num_table_get_value (dag2),
				    list_merge (list_clue, arith_num_table_get_premisses (dag2)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag2));
    }
  if (status == SAT)
    {
#ifdef PURE_ARITH
      if (DAG_symb(dag1) == FUNCTION_SUM)
	{
	  Tnumber v = number_new ();
	  TDAG d = DAG_NULL;
	  arith_DAG_sum_split (dag1, &d, &v);
	  status = arith_dl_push (dag2, d, v, list_clue);
	  number_neg (v);
	  status = arith_dl_push (d, dag2, v, list_clue);
	  number_free (v);
	}
      else if (DAG_symb(dag2) == FUNCTION_SUM)
	{
	  Tnumber v = number_new ();
	  TDAG d = DAG_NULL;
	  arith_DAG_sum_split (dag2, &d, &v);
	  status = arith_dl_push (dag1, d, v, list_clue);
	  number_neg (v);
	  status = arith_dl_push (d, dag1, v, list_clue);
	  number_free (v);
	}
      else
#endif
	{
	  status = arith_dl_push (dag1, dag2, number_zero, list_clue);
	  status = arith_dl_push (dag2, dag1, number_zero, list_clue);
	}
    }
}

/*-----------------------------------------------------------------------*/

/* DC adds the fact that dag1 <= dag2 + c */
static Tstatus
arith_store_dag_leq_dag (TDAG dag1, TDAG dag2, Tnumber c, Tlist list_clue)
{
  int is_empty1 = arith_num_table_empty (dag1);
  int is_empty2 = arith_num_table_empty (dag2);

  if (!is_empty1 && !is_empty2 && number_greater (arith_num_table_get_value (dag1), arith_num_table_get_value (dag2)))
    {
      set_insert_list_clue (arith_conflict_set,
			    list_merge (list_merge
					(list_clue,
					 arith_num_table_get_premisses (dag1)), arith_num_table_get_premisses (dag2)));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag2));
      list_anti_merge (list_clue, arith_num_table_get_premisses (dag1));
      status = UNSAT;
      return status;
    }
#ifdef PURE_ARITH
  if (DAG_symb(dag1) == FUNCTION_SUM)
    {
      Tnumber v = number_new ();
      TDAG d = DAG_NULL;
      arith_DAG_sum_split (dag1, &d, &v);
      number_sub (v, c, v);
      status = arith_dl_push (d, dag2, v, list_clue);
      number_free (v);
    }
  else if (DAG_symb(dag2) == FUNCTION_SUM)
    {
      Tnumber v = number_new ();
      TDAG d = DAG_NULL;
      arith_DAG_sum_split (dag2, &d, &v);
      number_add (v, v, c);
      status = arith_dl_push (dag1, d, v, list_clue);
      number_free (v);
    }
  else
#endif
    status = arith_dl_push (dag1, dag2, c, list_clue);
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC checks if the clue is a disequality */
static int
arith_is_disequality (Tclue clue)
{
  return (clue->type == CLUE_INEQUALITY);
}

/*-----------------------------------------------------------------------*/

/* DC checks if the clue is a disequality */
static Tvar_kind
arith_var_kind (Tvar_id v)
{
  return v != 0 && arith_is_integer ((TDAG) v) ? LA_INT : LA_RATIONAL;
}

/*--------------------------------------------------------------*/

static void
check_logic_and_init(void)
{
  if (fragment != NONE)
    return;
  if (strcmp(DAG_smtlib_logic(), "QF_UFIDL") == 0)
    fragment = DL;
  else if (strcmp(DAG_smtlib_logic(), "QF_UFRDL") == 0)
    fragment = DL;
  else if (strcmp(DAG_smtlib_logic(), "QF_IDL") == 0)
    fragment = DL;
  else if (strcmp(DAG_smtlib_logic(), "QF_RDL") == 0)
    fragment = DL;
  else if (strcmp(DAG_smtlib_logic(), "QF_UFLIA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "QF_UFLRA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "QF_LIA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "QF_LRA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "LRA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "UNKNOWN") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "QF_UF") == 0)
    fragment = DL;
  else if (strcmp(DAG_smtlib_logic(), "AUFLIRA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "AUFLIA") == 0)
    fragment = LA;
  else if (strcmp(DAG_smtlib_logic(), "QF_AUFLIA") == 0)
    fragment = LA;
  else
    {
      my_warning("Logic not recognized by arithmetic module: %s\n",
		 DAG_smtlib_logic());
      fragment = LA;
    }
  if (fragment == LA)
    la_init();
  else if (fragment == DL)
    dl_init(arith_id);
}

/*--------------------------------------------------------------*/

static void
arith_push_la (Tclue clue)
{
  status = SAT;

  if (!clue)
    {
      /*dl_push (NULL, NULL, number_zero  , NULL);
	history_dl_push(); */
      return;
    }

  if (arith_is_disequality (clue))
    {
      /* DC 1*A(d0) - 1*A(d1) != 0 */
      Tnumber c[2];
      Tvar_id v[2];
      Tvar_kind k[2];

      /* PF TODO this is bad practice */
      v[0] =(Tvar_id) clue->DAG[0];
      v[1] =(Tvar_id) clue->DAG[1];
      c[0] = number_cpy (number_new (), number_one);
      c[1] = number_neg (number_cpy (number_new (), number_one));
      k[0] = arith_var_kind (v[0]);
      k[1] = arith_var_kind (v[1]);
      la_push_disequality (v[0], v[1], k[0], k[1]);
      history_la_push(clue);
      number_free (c[0]);
      number_free (c[1]);
    }
  else if (clue->type == CLUE_ABSTRACT_PRED)
    {
      if (clue->polarity)
	{
	  if (DAG_symb(clue->DAG[0]) == PREDICATE_LEQ)
	    {
	      /* DC 1*A(dp0) - 1*A(dp1) <= 0 */
	      Tnumber c[2];
	      Tvar_id v[2];
	      Tvar_kind k[2];
	      v[0] = (Tvar_id) DAG_arg0(clue->DAG[0]);
	      v[1] = (Tvar_id) DAG_arg1(clue->DAG[0]);
	      c[0] = number_cpy (number_new (), number_one);
	      c[1] = number_neg (number_cpy (number_new (), number_one));
	      k[0] = arith_var_kind (v[0]);
	      k[1] = arith_var_kind (v[1]);
	      la_push_inequality (c, v, k, 2);
	      history_la_push(clue);
	      number_free (c[0]);
	      number_free (c[1]);
	    }
	  else if (DAG_symb(clue->DAG[0]) == PREDICATE_LESS)
	    {
	      /* DC + DELTA + 1*A(dp0) - 1*A(dp1) <= 0 */
	      TDAG x = DAG_arg0(clue->DAG[0]);
	      TDAG y = DAG_arg1(clue->DAG[0]);
	      Tnumber c[3];
	      Tvar_id v[3];
	      Tvar_kind k[3];
	      v[0] = 0;
	      v[1] = (Tvar_id) x;
	      v[2] = (Tvar_id) y;
	      if (arith_is_integer (x) && arith_is_integer (y))
		c[0] = number_neg (number_cpy (number_new (), number_small_neg_int));
	      else
		c[0] = number_neg (number_cpy (number_new (), number_small_neg_real));
	      c[1] = number_cpy (number_new (), number_one);
	      c[2] = number_neg (number_cpy (number_new (), number_one));
	      k[0] = arith_var_kind (v[0]);
	      k[1] = arith_var_kind (v[1]);
	      k[2] = arith_var_kind (v[2]);
	      la_push_inequality (c, v, k, 3);
	      history_la_push(clue);
	      number_free (c[0]);
	      number_free (c[1]);
	      number_free (c[2]);
	    }
	  else
	    {
	      arith_show_warning();
#ifdef DEBUG_ARITH
	      my_DAG_warning ("Arithmetic received an unexpected predicate \"%D\".\n", clue->DAG[0]);
#endif
	    }
	}
      else
	{
	  if (DAG_symb(clue->DAG[0]) == PREDICATE_LEQ)
	    {
	      /* DC + DELTA + 1*A(dp1) - 1*A(dp0) <= 0 */
	      TDAG x = DAG_arg1(clue->DAG[0]);
	      TDAG y = DAG_arg0(clue->DAG[0]);
	      Tnumber c[3];
	      Tvar_id v[3];
	      Tvar_kind k[3];
	      v[0] = 0;
	      v[1] = (Tvar_id) x;
	      v[2] = (Tvar_id) y;
	      if (arith_is_integer (x) && arith_is_integer (y))
		c[0] = number_neg (number_cpy (number_new (), number_small_neg_int));
	      else
		c[0] = number_neg (number_cpy (number_new (), number_small_neg_real));
	      c[1] = number_cpy (number_new (), number_one);
	      c[2] = number_neg (number_cpy (number_new (), number_one));
	      k[0] = arith_var_kind (v[0]);
	      k[1] = arith_var_kind (v[1]);
	      k[2] = arith_var_kind (v[2]);
	      la_push_inequality (c, v, k, 3);
	      history_la_push(clue);
	      number_free (c[0]);
	      number_free (c[1]);
	      number_free (c[2]);
	    }
	  else if (DAG_symb(clue->DAG[0]) == PREDICATE_LESS)
	    {
	      /* DC 1*A(dp1) - 1*A(dp0) <= 0 */
	      Tnumber c[2];
	      Tvar_id v[2];
	      Tvar_kind k[2];
	      v[0] = (Tvar_id) DAG_arg1(clue->DAG[0]);
	      v[1] = (Tvar_id) DAG_arg0(clue->DAG[0]);
	      c[0] = number_cpy (number_new (), number_one);
	      c[1] = number_neg (number_cpy (number_new (), number_one));
	      k[0] = arith_var_kind (v[0]);
	      k[1] = arith_var_kind (v[1]);
	      la_push_inequality (c, v, k, 2);
	      history_la_push(clue);
	      number_free (c[0]);
	      number_free (c[1]);
	    }
	  else
	    {
	      arith_show_warning();
#ifdef DEBUG_ARITH
	      my_DAG_warning ("Arithmetic solver received an unexpected predicate \"%D\".\n", clue->DAG[0]);
#endif
	    }
	}
    }
  else if (clue->type == CLUE_ABSTRACT_TERM)
    {
      if (DAG_arity(clue->DAG[0]) == 0 && DAG_is_number (clue->DAG[0]))
	{
	  /* DC - 1*A(d0) + N = 0 */
	  Tnumber c[2];
	  Tvar_id v[2];
	  Tvar_kind k[2];
	  v[0] = (Tvar_id) clue->DAG[1];
	  v[1] = 0;
	  c[0] = number_neg (number_cpy (number_new (), number_one));
	  c[1] = number_new ();
	  arith_DAG_readable_value (c[1], clue->DAG[0]);
	  k[0] = arith_var_kind (v[0]);
	  k[1] = arith_var_kind (v[1]);
	  la_push_equation (c, v, k, 2);
	  history_la_push(clue);
	  number_free (c[0]);
	  number_free (c[1]);
	}
      else if (DAG_symb(clue->DAG[0]) == FUNCTION_SUM)
	{
	  /* DC SUM(1*A(dpi)) - 1*A(d0) = 0 */
	  Tnumber *c;
	  Tvar_id *v;
	  Tvar_kind *k;
	  unsigned i;

	  MY_MALLOC (c, sizeof (Tnumber) * (DAG_arity(clue->DAG[0]) + 1));
	  MY_MALLOC (v, sizeof (Tvar_id) * (DAG_arity(clue->DAG[0]) + 1));
	  MY_MALLOC (k, sizeof (Tvar_kind) * (DAG_arity(clue->DAG[0]) + 1));
	  for (i = 0; i < DAG_arity(clue->DAG[0]); ++i)
	    {
	      c[i] = number_cpy (number_new (), number_one);
	      v[i] = (Tvar_id) DAG_arg(clue->DAG[0], i);
	      k[i] = arith_var_kind (v[i]);
	    }
	  c[DAG_arity(clue->DAG[0])] = number_neg (number_cpy (number_new (), number_one));
	  v[DAG_arity(clue->DAG[0])] = (Tvar_id) clue->DAG[1];
	  k[DAG_arity(clue->DAG[0])] = arith_var_kind (v[DAG_arity(clue->DAG[0])]);
	  la_push_equation (c, v, k, DAG_arity(clue->DAG[0]) + 1);
	  history_la_push(clue);
	  for (i = 0; i < DAG_arity(clue->DAG[0]) + 1; ++i)
	    number_free (c[i]);
	  free (c);
	  free (v);
	  free (k);
	}
      else if (DAG_symb(clue->DAG[0]) == FUNCTION_MINUS)
	{
	  /* DC 1*A(dp0) - 1*A(dp1) - 1*A(d0) = 0 */
	  Tnumber c[3];
	  Tvar_id v[3];
	  Tvar_kind k[3];
	  v[0] = (Tvar_id) DAG_arg0(clue->DAG[0]);
	  v[1] = (Tvar_id) DAG_arg1(clue->DAG[0]);
	  v[2] = (Tvar_id) clue->DAG[1];
	  c[0] = number_cpy (number_new (), number_one);
	  c[1] = number_neg (number_cpy (number_new (), number_one));
	  c[2] = number_neg (number_cpy (number_new (), number_one));
	  k[0] = arith_var_kind (v[0]);
	  k[1] = arith_var_kind (v[1]);
	  k[2] = arith_var_kind (v[2]);
	  la_push_equation (c, v, k, 3);
	  history_la_push(clue);
	  number_free (c[0]);
	  number_free (c[1]);
	  number_free (c[2]);
	}
      else if (unary_minus(DAG_symb(clue->DAG[0])))
	{
	  /* DC 1*A(dp0) + 1*A(d0) = 0 */
	  Tnumber c[2];
	  Tvar_id v[2];
	  Tvar_kind k[2];
	  v[0] = (Tvar_id) DAG_arg0(clue->DAG[0]);
	  v[1] = (Tvar_id) clue->DAG[1];
	  c[0] = number_cpy (number_new (), number_one);
	  c[1] = number_cpy (number_new (), number_one);
	  k[0] = arith_var_kind (v[0]);
	  k[1] = arith_var_kind (v[1]);
	  la_push_equation (c, v, k, 2);
	  history_la_push(clue);
	  number_free (c[0]);
	  number_free (c[1]);
	}
      else if (DAG_symb(clue->DAG[0]) == FUNCTION_PROD && DAG_arity(clue->DAG[0]) == 2)
	{
	  /* DC N*A(dp0) - 1*A(d0) = 0  || N*A(dp1) - 1*A(d0) = 0 */
	  Tnumber c[2];
	  Tvar_id v[2];
	  Tvar_kind k[2];
	  c[0] = number_new ();
	  c[1] = number_neg (number_cpy (number_new (), number_one));
	  v[1] = (Tvar_id) clue->DAG[1];
	  if (DAG_is_number (DAG_arg0(clue->DAG[0])))
	    {
	      arith_DAG_readable_value (c[0], DAG_arg0(clue->DAG[0]));
	      v[0] = (Tvar_id) DAG_arg1(clue->DAG[0]);
	    }
	  else if (DAG_is_number (DAG_arg1(clue->DAG[0])))
	    {
	      arith_DAG_readable_value (c[0], DAG_arg1(clue->DAG[0]));
	      v[0] = (Tvar_id) DAG_arg0(clue->DAG[0]);
	    }
	  else
	    {
	      arith_show_warning();
	      my_warning ("Non-linear arithmetic fragment: Multiplication between 2 variables\n");
	      number_free (c[0]);
	      number_free (c[1]);
	      return;
	    }

	  k[0] = arith_var_kind (v[0]);
	  k[1] = arith_var_kind (v[1]);
	  la_push_equation (c, v, k, 2);
	  history_la_push(clue);

	  number_free (c[0]);
	  number_free (c[1]);
	}
      else
	{
	  arith_show_warning();
#ifdef DEBUG_ARITH
	  my_DAG_warning ("Such arithmetic fragment, %D, is currently not supported.\n", clue->DAG[0]);
#endif
	}
    }
  else if (clue->type == CLUE_MERGE)
    {
      /* DC 1*d0 - 1*d1 = 0 */
      Tnumber c[2];
      Tvar_id v[2];
      Tvar_kind k[2];
      v[0] = (Tvar_id) clue->DAG[0];
      v[1] = (Tvar_id) clue->DAG[1];
      c[0] = number_cpy (number_new (), number_one);
      c[1] = number_neg (number_cpy (number_new (), number_one));
      k[0] = arith_var_kind (v[0]);
      k[1] = arith_var_kind (v[1]);
      la_push_equation (c, v, k, 2);
      history_la_push(clue);
      number_free (c[0]);
      number_free (c[1]);
    }

  if ((status = la_status ()) == UNSAT)
    {
      Tlist tmp = la_conflict (), ptr;
      undo_push(ARITH_UNSAT);
      ptr = tmp;
      do
	{
	  intptr_t c = (intptr_t) list_car (ptr);
	  set_insert (arith_conflict_set, table_get (arith_clues_table, c));
	  ptr = list_cdr (ptr);
	}
      while (ptr != tmp);
      list_free (&tmp);
    }
}

/*--------------------------------------------------------------*/

static void
arith_push_dl(Tclue clue)
{
  Tlist list_premisses;

  if (!clue)
    {
      dl_push(DAG_NULL, DAG_NULL, number_zero, NULL);
      history_dl_push();
      return;
    }

  list_premisses = list_cons(clue, NULL);
  status = SAT;

  if (arith_is_disequality (clue))
    {
      dl_push_disequality (clue);
      history_dl_push();
    }
  else if (clue->type == CLUE_ABSTRACT_PRED)
    {
      TDAG DAG0 = clue->DAG[0];
      if (clue->polarity)
	{
	  if (DAG_symb(DAG0) == PREDICATE_LEQ)
	    arith_store_dag_leq_dag (DAG_arg0(DAG0), DAG_arg1(DAG0), number_zero, list_premisses);

	  else if (DAG_symb(DAG0) == PREDICATE_LESS)
	    {
	      TDAG x = DAG_arg0(DAG0);
	      TDAG y = DAG_arg1(DAG0);
	      if (arith_is_integer (x) && arith_is_integer (y))
		arith_store_dag_leq_dag (x, y, number_small_neg_int, list_premisses);
	      else
		{
		  assert (arith_is_real (x) || arith_is_real (y));
		  arith_store_dag_leq_dag (x, y, number_small_neg_real, list_premisses);
		}
	    }
	  else
	    {
	      arith_show_warning();
#ifdef DEBUG_ARITH
	      my_DAG_warning ("Arithmetic received an unexpected predicate \"%D\".\n", DAG0);
#endif
	    }
	}
      else
	{
	  if (DAG_symb(DAG0) == PREDICATE_LEQ)
	    {
	      TDAG x = DAG_arg1(DAG0);
	      TDAG y = DAG_arg0(DAG0);
	      if (arith_is_integer (x) && arith_is_integer (y))
		arith_store_dag_leq_dag (x, y, number_small_neg_int, list_premisses);
	      else
		{
		  assert (arith_is_real (x) || arith_is_real (y));
		  arith_store_dag_leq_dag (x, y, number_small_neg_real, list_premisses);
		}
	    }
	  else if (DAG_symb(DAG0) == PREDICATE_LESS)
	    arith_store_dag_leq_dag (DAG_arg1(DAG0), DAG_arg0(DAG0), number_zero, list_premisses);
	  else
	    {
	      arith_show_warning();
#ifdef DEBUG_ARITH
	      my_DAG_warning ("Arithmetic solver received an unexpected predicate \"%D\".\n", DAG0);
#endif
	    }
	}
    }
  else if (clue->type == CLUE_MERGE)
    arith_store_dag_equal_dag (clue->DAG[0], clue->DAG[1], list_premisses);

#ifdef PURE_ARITH
  else if (1)
    arith_store_dag_equal_dag (clue->DAG[0], clue->DAG[1], list_premisses);
#endif

  else if (clue->type == CLUE_ABSTRACT_TERM)
    {
      TDAG DAG0 = clue->DAG[0];
      TDAG DAG1 = clue->DAG[1];
      if (DAG_arity(DAG0) == 0 && DAG_is_number (DAG0))
	{
	  Tnumber n = number_new ();
	  arith_DAG_readable_value (n, DAG0);
	  arith_store_dag_equal_number (DAG1, n, list_premisses);
	  number_free (n);
	}
      else if (DAG_symb(DAG0) == FUNCTION_SUM) /* DAG1 = D00 + D01 */
	arith_store_dag_equal_sum (DAG1, DAG_arg0(DAG0), DAG_arg1(DAG0), list_premisses);
      else if (DAG_symb(DAG0) == FUNCTION_MINUS) /* DAG1 = D00 - D01 -> D00 = DAG1 + D01 */
	arith_store_dag_equal_sum (DAG_arg0(DAG0), DAG1, DAG_arg1(DAG0), list_premisses);
      else if (unary_minus(DAG_symb(DAG0)))
	arith_store_dag_opposite_dag (DAG1, DAG_arg0(DAG0), list_premisses);
      else
	{
	  arith_show_warning();
#ifdef DEBUG_ARITH
	  my_DAG_warning ("Such arithmetic fragment, %D, is currently not supported.\n", DAG0);
#endif
	}
    }

  if (status == UNSAT)
    {
      Tlist tmp = dl_conflict ();
      undo_push(ARITH_UNSAT);
      set_insert_list_clue (arith_conflict_set, tmp);
      list_free (&tmp);
    }
  list_free (&list_premisses);
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

/*
 DC The different kind of clues that can be handled are:
 [~] (dag1 <= dag2 (predicate), dag1 < dag2 (predicate)), dag1 = dag2 (merge), dag1 (abstract)
 */
/* PF The real job is done above in arith_push_la and arith_push_dl */
void
arith_push (Tclue clue)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: arith_push%d\n");
  clue_print2(clue);
#endif
  /*  printf("ARITH: "); clue_fprint (stdout, clue); printf("\n"); */
  history_arith_push(clue);
  /* DC is it UNSAT already? */
  if (status == UNSAT)
    return;

  /* Checks the logic and memorizes it */
#ifdef LINEAR_ARITHMETIC
  if (fragment == NONE)
    {
      fragment = LA;
      la_init();
    }
#elif defined(DIFFERENCE_LOGIC)
  if (fragment == NONE)
    {
      fragment = DL;
      dl_init(arith_id);
    }
#else
  check_logic_and_init();
#endif

  if (fragment == LA)
    arith_push_la(clue);
  else if (fragment == DL)
    arith_push_dl(clue);

#ifdef DEBUG_ARITH
  my_message ("ARITH: push (finished); result = %s\n", 
	      status == UNSAT ? "UNSAT" : 
	      status == SAT && arith_not_supported == 0 ? "SAT" : 
	      "UNDEF");
#endif
}

/*-----------------------------------------------------------------------*/

/* DC solves constraints */
/* PF TODO hack of removing disequalities that should anyway not be produced */
Tstatus
arith_solve(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: solve()\n");
#endif
  if (status == UNSAT)
    return status;
  if (fragment == LA)
    {
      status = la_solve();
      if (status == UNSAT)
	{
	  Tlist tmp = la_conflict();
	  Tlist ptr = tmp;
	  undo_push(ARITH_UNSAT);
	  do
	    {
	      intptr_t c = (intptr_t) list_car(ptr);
	      Tclue clue = (Tclue) table_get(arith_clues_table, c);
	      /* DC You can always remove disequalities
		 from arithmetic conflicts
		 (they are used only for "model correction") */
	      if (clue->type != CLUE_INEQUALITY)
		set_insert (arith_conflict_set, clue);
	      ptr = list_cdr(ptr);
	    }
	  while (ptr != tmp);
	  list_free (&tmp);
	}
    }
  else if (fragment == DL)
    {
      status = dl_solve();
      if (status == UNSAT)
	{
	  Tlist tmp = dl_conflict();
	  undo_push(ARITH_UNSAT);
	  set_insert_list_clue(arith_conflict_set, tmp);
	  list_free(&tmp);
	}
    }
  if (status == SAT && arith_not_supported > 0)
    status = UNDEF;
#ifdef DEBUG_ARITH
  my_message ("ARITH: solve (finished); result = %s\n",
	      status == UNSAT ? "UNSAT" : 
	      (status == SAT && arith_not_supported == 0) ?
	      "SAT" : "UNDEF");
#endif
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC returns current status */
Tstatus
arith_status (void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: status()\n");
#endif
  if (status == UNSAT)
    return status;
  if (fragment == LA)
    status = la_status ();
  else if (fragment == DL)
    status = dl_status ();
  if (status == SAT && arith_not_supported > 0)
    status = UNDEF;
#ifdef DEBUG_ARITH
  my_message ("ARITH: status (finished); result = %s\n",
	      status == UNSAT ? "UNSAT" :
	      (status == SAT && arith_not_supported == 0) ?
	      "SAT" : "UNDEF");
#endif
  return status;
}

/*-----------------------------------------------------------------------*/

#ifdef PROOF
/* DC builds and returns the PROOF for a DL conflict */
/* PF TODO this certainly could be merged with the LA version */
static Tproof_id
arith_build_dl_proof(Tlist clues, TDAG DAG)
{
  Tlist clause = NULL;
  Tlist tmp = clues;
  Tproof_id proof_id;
  assert (clues);
  do
    {
      Tclue clue = list_car (tmp);
      TDAG DAG;
      if (clue->type == CLUE_ABSTRACT_PRED)
	{
	  assert (DAG_symb(clue->DAG[0]) == PREDICATE_LEQ ||
		  DAG_symb(clue->DAG[0]) == PREDICATE_LESS);
	  DAG = clue->polarity ? DAG_not(clue->DAG[0]) : clue->DAG[0];
	  clause = list_add(clause, DAG_ptr_of(DAG));
	}
      else if (clue->type == CLUE_ABSTRACT_TERM)
	{
	  assert ((DAG_arity(clue->DAG[0]) == 0 && DAG_is_number(clue->DAG[0]))
		  || DAG_symb(clue->DAG[0]) == FUNCTION_SUM
		  || unary_minus(DAG_symb(clue->DAG[0])));
	  if (clue->DAG[0] != clue->DAG[1])
	    clause = list_add(clause, DAG_ptr_of(DAG_neq(clue->DAG[0], clue->DAG[1])));
	}
      else if (clue->type == CLUE_MERGE)
	{
	  assert (clue->DAG[0] != clue->DAG[1]);
	  clause = list_add(clause, DAG_ptr_of(DAG_neq(clue->DAG[0], clue->DAG[1])));
	}
      else
	my_error ("arith_build_dl_proof: discarded clue\n");
      tmp = list_cdr(tmp);
    }
  while (tmp != clues);
  if (DAG)
    clause = list_add(clause, DAG_ptr_of(DAG));
  proof_id = proof_clause_list(dl_generic, clause);
  list_free (&clause);
  return proof_id;
}
#endif

/*-----------------------------------------------------------------------*/

#ifdef PROOF
/* DC builds and returns the PROOF for a LA conflict */
/* PF TODO this certainly could be merged with the DL version */
static Tproof_id
arith_build_la_proof(Tlist clues, TDAG DAG)
{
  Tlist clause = NULL;
  Tlist tmp = clues;
  Tproof_id proof_id;
  assert (clues);
  do
    {
      Tclue clue = list_car(tmp);
      TDAG DAG;
      if (clue->type == CLUE_ABSTRACT_PRED)
	{
	  assert (DAG_symb(clue->DAG[0]) == PREDICATE_LEQ ||
		  DAG_symb(clue->DAG[0]) == PREDICATE_LESS);
	  DAG = clue->polarity ? DAG_not(clue->DAG[0]) : clue->DAG[0];
	  clause = list_add(clause, DAG_ptr_of(DAG));
	}
      else if (clue->type == CLUE_ABSTRACT_TERM)
	{
	  assert ((DAG_arity(clue->DAG[0]) == 0 && DAG_is_number(clue->DAG[0]))
		  || DAG_symb(clue->DAG[0]) == FUNCTION_SUM
		  || unary_minus(DAG_symb(clue->DAG[0]))
		  || DAG_symb(clue->DAG[0]) == FUNCTION_MINUS
		  || DAG_symb(clue->DAG[0]) == FUNCTION_PROD);
	  if (clue->DAG[0] != clue->DAG[1])
	    clause = list_add(clause, DAG_ptr_of(DAG_neq(clue->DAG[0], clue->DAG[1])));
	}
      else if (clue->type == CLUE_MERGE)
	{
	  assert (clue->DAG[0] != clue->DAG[1]);
	  clause = list_add(clause, DAG_ptr_of(DAG_neq(clue->DAG[0], clue->DAG[1])));
	}
      /*
       * DC This is because conflict sets for Integer Linear Arithmetic
         may not be minimal,
       * and therefore, they may contain disequalities.
       * TODO: Think: should the inequalities be removed from non minimal conflict sets?
       */
      else if (clue->type == CLUE_INEQUALITY)
	{
	  assert (false);
	  clause = list_add (clause, DAG_ptr_of(DAG_eq(clue->DAG[0], clue->DAG[1])));
	}
      else
	my_error ("arith_build_la_proof: discarded clue\n");
      tmp = list_cdr(tmp);
    }
  while (tmp != clues);
  if (DAG)
    clause = list_add(clause, DAG_ptr_of(DAG));
  proof_id = proof_clause_list(la_generic, clause);
  list_free(&clause);
  return proof_id;
}
#endif

/*-----------------------------------------------------------------------*/

/* DC returns a list of conflict constraints (clue) when UNSAT */
#ifdef PROOF
Tlist
arith_conflict(Tproof_id * proof_id)
#else
Tlist
arith_conflict(void)
#endif
{
  Tlist tmp;
#ifdef DEBUG_ARITH
  my_message ("ARITH: conflict()\n");
#endif
  tmp = set_list (arith_conflict_set);
#ifdef PROOF
  if (fragment == DL)
    *proof_id = arith_build_dl_proof(tmp, DAG_NULL);
  else /* if LINEAR_ARITHMETIC */
    *proof_id = arith_build_la_proof(tmp, DAG_NULL);
#endif
#ifdef DEBUG_ARITH
  list_clue_fprint (stdout, tmp);
  /*printf("DAGs from conflict:\n");
     {
     Tlist ptr = tmp;
     do{
     Tclue clue = (Tclue)list_car(ptr);
     clue_fprint(stdout, clue);
     printf("\n");
     if (clue->type == CLUE_MERGE)
     my_DAG_message("%D = %D\n", clue->DAG[0], clue->DAG[1]);
     else if (DAG_arity(clue->DAG[0]) == 2)
     my_DAG_message("%D = %D %s %D\n", clue->DAG[1], DAG_arg0(clue->DAG[0]), DAG_symb(clue->DAG[0])->name, DAG_arg1(clue->DAG[0]));
     else
     my_DAG_message("%D = %D\n", clue->DAG[1], clue->DAG[0]);

     ptr = list_cdr(ptr);
     } while (ptr != tmp);
     } */
#endif
  return tmp;
}

/*-----------------------------------------------------------------------*/

/* DC returns a list of premisses of a equality (clue) */
Tlist
arith_premisses(const Tclue clue)
{
  Tlist tmp;
  assert (clue->origin == arith_id);
#ifdef DEBUG_ARITH
  my_message ("ARITH: premisses()\n");
#endif
  tmp = list_cpy(clue->proof.arith);
  assert (tmp);
#ifdef PROOF
  if (fragment == LA)
    clue->proof_id =
      arith_build_la_proof(tmp, DAG_eq(clue->DAG[0], clue->DAG[1]));
  else if (fragment == DL)
    clue->proof_id =
      arith_build_dl_proof(tmp, DAG_eq(clue->DAG[0], clue->DAG[1]));
#endif
  return tmp;
}

/*-----------------------------------------------------------------------*/

/* DC returns found lemmas in the given table */
void
arith_lemmas(Tstack_DAG * Plemmas)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: lemmas()\n");
#endif
  if (fragment == LA)
    {
      /* PF TODO I do not understand why this is special for LA */
      if (!arith_has_lemma ())
	return;
      assert (la_model_has_conflict());
      while (la_model_has_conflict())
	{
	  int d = la_model_conflict_pop();
	  Tclue c = (Tclue) table_get(arith_clues_table, d);
	  TDAG d1 = c->DAG[0], d2 = c->DAG[1];
	  TDAG dag_lemma = arith_generate_disequality_lemma(d1, d2);
#ifdef PROOF
	  proof_add_disequality_lemma(DAG_dup(dag_lemma));
#endif
	  stack_push(*Plemmas, dag_lemma);
	}
    }
  else if (fragment == DL)
    dl_lemmas(Plemmas);
}

/*-----------------------------------------------------------------------*/

/**
   \remark just a proxy for DL and LA functions */
bool
arith_has_lemma(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: has_lemma()\n");
#endif
  if (fragment == LA)
    return la_model_has_conflict();
  if (fragment == DL)
    return dl_has_lemma();
  return false;
}

/*-----------------------------------------------------------------------*/

/**
   \remark just a proxy for DL and LA functions */
bool
arith_eq_queue_empty(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: eq_queue_empty()\n");
#endif
  if (fragment == LA)
    return la_eq_queue_empty();
  if (fragment == DL)
    return dl_eq_queue_empty();
  return true;
}

/*-----------------------------------------------------------------------*/

/**
   \remark just a proxy for DL functions
   \remark unimplemented for LA */
Tclue
arith_eq_queue_pop(void)
{
#ifdef DEBUG_ARITH
  if (fragment == DL)
    {
      Tclue clue = dl_eq_queue_pop();
      my_message ("ARITH: eq_queue_pop()\n");
      clue_fprint (stderr, clue);
      fprintf (stderr, "\n");
      return clue;
    }
#else
  if (fragment == DL)
    return dl_eq_queue_pop();
#endif
  if (fragment == LA)
    return NULL;
  return NULL;
}

/*-----------------------------------------------------------------------*/

/**
   \remark just a proxy for DL and LA functions */
bool
arith_model_eq_queue_empty(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: eq_model_queue_empty()\n");
#endif
  if (fragment == LA)
    return la_model_eq_queue_empty();
  if (fragment == DL)
    return dl_model_eq_queue_empty();
  return true;
}

/*-----------------------------------------------------------------------*/

/**
   \remark just a proxy for DL and LA functions */
Tclue
arith_model_eq_queue_pop(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: model_eq_queue_pop()\n");
  if (fragment == LA)
    {
      Tclue clue;
      Tvar_id d1, d2;
      la_model_eq_queue_pop(&d1, &d2);
      clue = clue_new_model_equality((TDAG) d1, (TDAG) d2, arith_id);
      clue_fprint(stderr, clue);
      fprintf(stderr, "\n");
      return clue;
    }
  if (fragment == DL)
    {
      Tclue clue = dl_model_eq_queue_pop();
      clue_fprint(stderr, clue);
      fprintf(stderr, "\n");
      return clue;
    }
#else
  if (fragment == LA)
    {
      Tvar_id d1, d2;
      la_model_eq_queue_pop(&d1, &d2);
      return clue_new_model_equality((TDAG) d1, (TDAG) d2, arith_id);
    }
  if (fragment == DL)
    return dl_model_eq_queue_pop();
#endif
  return NULL;
}

/*-----------------------------------------------------------------------*/

void
arith_print (FILE * file)
{
}

/*-----------------------------------------------------------------------*/

void
arith_init(const unsigned id)
{
#ifdef DEBUG_ARITH
  my_message("ARITH: init()\n");
#endif
  arith_set_id(id);
  status = SAT;
  arith_not_supported = 0;
  integer = 0;
  history_init();

  arith_num_hash = hash_new(INIT_SIZE,
			    (TFhash) DAG_num_hash,
			    (TFequal) DAG_num_equal,
			    (TFfree) DAG_num_free);
  arith_conflict_set = set_new((TFcmp) set_clue_compare,
			       (TFfree) set_clue_free);
  arith_clues_table = table_new(INIT_SIZE, INCREMENT);

  if (fragment == LA)
    la_init ();
  else if (fragment == DL)
    dl_init (id);
}

/*-----------------------------------------------------------------------*/

void
arith_done(void)
{
#ifdef DEBUG_ARITH
  my_message ("ARITH: done()\n");
#endif
  /* DC free data created during pushes */
  arith_not_supported = 0;

  history_done();

  /* DC free data created during init */
  hash_free(&arith_num_hash);
  set_free(&arith_conflict_set);
  table_free(&arith_clues_table);

  /* DC free sub DP */
  if (fragment == LA)
    la_done();
  else if (fragment == DL)
    dl_done();
}
