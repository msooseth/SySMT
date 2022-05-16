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
   \file dl.c
   \author Diego Caminha
   \brief Difference logic decision procedure implementation
   Implementation of a difference logic decision procedure based on graphs */

#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdbool.h>

#include "config.h"

#include "dl.h"
#include "arith.h"
#include "clue.h"
#include "general.h"
#include "table.h"
#include "set.h"
#include "DAG.h"
#include "DAG-ptr.h"
#include "congruence.h"
#include "options.h"
#include "proof.h"

#ifdef DEBUG_DL
#include "DAG-print.h"
#include "clue-print.h"
#endif

static const unsigned INIT_SIZE = 200;
static const unsigned INCREMENT = 200;

/*
  --------------------------------------------------------------
  Struct Types
  --------------------------------------------------------------
*/

/**
   \struct TSedge
   \brief Edge struct, represent a constraint */
/* PF TODO I think only one constraint id would be enough */
typedef struct TSedge
{
  unsigned destination; /**< Destination variable id */
  Tnumber weight;       /**< Cost */
  Tlist list_clue;      /**< Clues that originated this edge */
} *Tedge;

/**
   \struct TSvariable_id
   \brief A pair of TDAG and unsigned. */
/* PF TODO what for? */
typedef struct TSvariable_id
{
  TDAG dag;
  unsigned id;
} *Tvariable_id;

/**
   \strcut Tnumber_int_pair
   \brief A pair of Tnumber and unsigned. */
/* PF TODO what for? */
typedef struct
{
  Tnumber first;
  unsigned second;
} Tnumber_int_pair;

/*
  --------------------------------------------------------------
  Local variables
  --------------------------------------------------------------
*/

/* DC how the decision procedure is identified from the NO schema */
static int dl_id;

/* DC mask for dl */
static unsigned dl_mask;

/* DC ---- Association between variable DAGs and variable identifiers ----- */

/* DC distance table, points to the current distance from "variable 0" */
static Ttable/*<Tnumber>*/ dl_distance_table;

/* DC edges table, (n x n) table, [u][v] points to the current (u, v) edge value */
static Ttable/*<Ttable<Tedge>>*/ dl_edge_table;

/* DC numbers of edges of each variable */
static Ttable/*<Tunsigned>*/ dl_variable_degree_table;

/* DC current status */
static Tstatus status;

/* DC conflict set of constraints (clue) returned when UNSAT */
static Tset dl_conflict_set;

/* DC number of pushed clues */
static unsigned level;

/* DC level when status became UNSAT */
static unsigned unsat_level;

/* DC integer variables are involved, so generate model equalities for completeness */
static bool is_idl;

/* DC identifies a dummy variable acting as a sentinel in the algorithm */
static unsigned dl_sentinel_id;

/* DC number of variables created so far */
static unsigned dl_variables_nb;

/* DC associate each variable to a local int id */
static Thash dl_variable_id_hash;

/* DC associate eache variable id to its DAG */
static Ttable/*<TDAG>*/ dl_variable_DAG;

/* DC graph used to find strongly conected components (scc) and equalities */
static Ttable dl_edge_table_scc;

/* DC transpose graph used to find strongly conected components and equalities */
static Ttable dl_edge_table_scc_t;

/* DC indicates whenever is necessary to execute the procedure to find the strongly conected component */
static char dl_search_scc;

/* DC indicates whenever is necessary to execute the procedure to find the model equalities */
static char dl_search_model_eq;

/* DC indicates whenever there is a lemma to be given that will modify the current model */
static char dl_model_lemma;

/* DC variable equalities derived by the decision procedure */
static Ttable dl_var_eq_table;

/* DC model equalities derived by IDL */
static Ttable dl_model_eq_table;

/* DC lemmas derived */
static Ttable dl_lemmas_table;

/* DC equalities already returned until current level */
static Tset dl_set_returned_eq;

/* DC model equalities already returned until current level */
static Tset dl_set_returned_model_eq;

/* DC disequalities received */
static Ttable dl_table_disequalities;

/* DC true when Splitting on Demand is used instead of Model Equalities */
static bool split_on_demand = false;

/* DC hash of already generated lemmas for avoiding repetition */
static Thash dl_hash_generated_lemmas;

static void dl_add_edge (unsigned source_id, unsigned destination_id, Tnumber weight, Tlist list_clue);
static void history_variable_created (Tvariable_id variable_id);
static int dl_get_pos_edge (unsigned source_id, unsigned destination_id);
static unsigned dl_degree (unsigned variable_id);

static Tlist dl_compute_premisses (const Tclue, TDAG, TDAG, const int scc_pred[], const int scc_t_pred[]);


bool
dl_has_model_equalities()
{
  return set_empty(dl_set_returned_model_eq) == false;
}


/*
  --------------------------------------------------------------
  Association variable id with DAG
  --------------------------------------------------------------
*/

/* DC hash function for a Tvariable_id hash */
static unsigned
variable_id_hash(void *id)
{
  return DAG_hash(((Tvariable_id) id)->dag);
}

/*-----------------------------------------------------------------------*/

/* DC equal function for a Tvariable hash */
static int
variable_id_equal(void *id1, void *id2)
{
  return ((Tvariable_id) id1)->dag == ((Tvariable_id) id2)->dag;
}

/*-----------------------------------------------------------------------*/

/* DC free function for a Tvariable hash */
static void
variable_id_free(void *id)
{
  DAG_free(((Tvariable_id) id)->dag);
  free((Tvariable_id) id);
}

/*-----------------------------------------------------------------------*/

/* DC returns the variable id (and creates a new one if it is the first time it appears) */
static unsigned
dl_variable_id(TDAG v)
{
  /* DC searching key */
  Tvariable_id tmp;
  /* DC lookup result */
  Tvariable_id result;
  /* DC source table for resize edges */
  Ttable source_table;

  /* DC search */
  MY_MALLOC(tmp, sizeof (struct TSvariable_id));
  tmp->dag = v;
  result = (Tvariable_id) hash_lookup(dl_variable_id_hash, (void *) tmp);
  if (result)
    {
      /* DC return new id */
      free (tmp);
      return result->id;
    }
  /* DC if first time it appears */
  /* DC register it properly and return new id */
  DAG_dup (tmp->dag);
  tmp->id = dl_variables_nb++;
  hash_insert(dl_variable_id_hash, (void *) tmp);
  table_push(dl_variable_DAG, DAG_ptr_of(v));
  /* DC out degree = 0 */
  table_push(dl_variable_degree_table, 0);
  /* DC resize edge_table */
  source_table = table_new(INIT_SIZE, INCREMENT);
  table_push(dl_edge_table, source_table);
  /* DC all new variable have this 0 cost edge from "variable 0" */
  dl_add_edge(dl_sentinel_id, tmp->id, number_zero, NULL);
  /* DC all variables start with distance 0 from "variable 0" */
  table_push(dl_distance_table, number_zero);
  /* DC history recording */
  history_variable_created (tmp);
  return tmp->id;
}

/*-----------------------------------------------------------------------*/

/* DC removes a variable */
static void
dl_variable_id_remove (Tvariable_id assoc)
{
  --dl_variables_nb;
  assert (assoc->id == dl_variables_nb);
  hash_remove(dl_variable_id_hash, (void *) assoc);
}

/*
  --------------------------------------------------------------
  History (backtracking)
  --------------------------------------------------------------
*/

/* DC what kind of events do we record */
typedef enum {
  VARIABLE_CREATED,
  EDGE_CREATED,
  EDGE_EDITED,
  DISTANCE_EDITED,
  EQUALITY_FOUND,
  MODEL_EQUALITY_FOUND,
  DISEQUALITY_PUSHED
} Tevent_kind;

/* DC edge insertion data */
typedef struct TShistory_edge_created
{
  unsigned source_id;
  unsigned destination_id;
  Tlist list_clue;
} *Thistory_edge_created;

/* DC edge edition data */
typedef struct TShistory_edge_edited
{
  unsigned source_id;
  unsigned destination_id;
  Tnumber weight;
  Tlist list_clue;
} *Thistory_edge_edited;

/* DC distance edition data */
typedef struct TShistory_distance_edited
{
  unsigned variable_id;
  Tnumber distance;
} *Thistory_distance_edited;

/* DC equality clue found */
typedef Tclue Thistory_equality_found;

/* DC indentifies a recorded event */
typedef struct TShistory
{
  void *data;
  int level;
  Tevent_kind kind;
  struct TShistory *next;
} *Thistory;

/* DC list of events recorded */
static Thistory dl_history;

/*-----------------------------------------------------------------------*/

/* DC add a new record in history */
static void
history_new_record(int level, Tevent_kind kind, void * data)
{
  Thistory record;
  MY_MALLOC(record, sizeof (struct TShistory));
  record->level = level;
  record->kind = kind;
  record->data = data;
  record->next = dl_history;
  dl_history = record;
}

/*-----------------------------------------------------------------------*/

/* DC records a variable insertion */
static void
history_variable_created(Tvariable_id variable_id)
{
  history_new_record(level, VARIABLE_CREATED, (void *) variable_id);
}

/*-----------------------------------------------------------------------*/

/* DC records a edge insertion */
static void
history_edge_created(unsigned source_id, unsigned destination_id,
		     Tlist list_clue)
{
  Thistory_edge_created data;
  MY_MALLOC(data, sizeof(struct TShistory_edge_created));
  data->source_id = source_id;
  data->destination_id = destination_id;
  data->list_clue = list_clue;
  history_new_record(level, EDGE_CREATED, data);
}

/*-----------------------------------------------------------------------*/

/* DC records a edge edition */
static void
history_edge_edited(unsigned source_id, unsigned destination_id,
		    Tnumber weight, Tlist list_clue)
{
  Thistory_edge_edited data;
  MY_MALLOC(data, sizeof(struct TShistory_edge_edited));
  data->source_id = source_id;
  data->destination_id = destination_id;
  data->weight = number_new();
  number_cpy(data->weight, weight);
  data->list_clue = list_clue;
  history_new_record(level, EDGE_EDITED, data);
}

/*-----------------------------------------------------------------------*/

/* DC records a distance edition */
static void
history_distance_edited(unsigned variable_id, Tnumber distance)
{
  Thistory_distance_edited data;
  MY_MALLOC (data, sizeof(struct TShistory_distance_edited));
  data->variable_id = variable_id;
  data->distance = distance;
  history_new_record(level, DISTANCE_EDITED, data);
}

/*-----------------------------------------------------------------------*/

/* DC records a equality clue found */
static void
history_equality_found(Tclue clue)
{
  clue_dup (clue);
  history_new_record(level, EQUALITY_FOUND, (void *) clue);
}

/*-----------------------------------------------------------------------*/

/* DC records a model equality clue found */
static void
history_model_equality_found(Tclue clue)
{
  Tlist list_premisses = list_cons(clue, NULL);
#ifdef DEBUG_DL
  my_message ("DL: model_equality_found()\n");
#endif
  dl_add_edge(dl_variable_id(clue->DAG[0]), dl_variable_id(clue->DAG[1]),
	      number_zero, list_premisses);
  list_free(&list_premisses);
  clue_dup (clue);
  history_new_record(level, MODEL_EQUALITY_FOUND, (void *) clue);
}

/*-----------------------------------------------------------------------*/

/* DC records a disequality pushed */
static void
history_disequality_pushed(Tclue clue)
{
  history_new_record(level, DISEQUALITY_PUSHED, (void *) clue);
}

/*-----------------------------------------------------------------------*/

/* DC removes last variable created */
static void
history_variable_created_back(void)
{
  Ttable source_table;
  Tvariable_id data = (Tvariable_id) dl_history->data;
  /* DC resize variable DAG table */
  table_pop(dl_variable_DAG);
  /* DC resize degree */
  table_pop(dl_variable_degree_table);
  /* DC resize edge_table */
  source_table = (Ttable) table_pop(dl_edge_table);
  table_free(&source_table);
  /* DC resize distance */
  table_pop(dl_distance_table);
  /* DC remove from hash */
  dl_variable_id_remove(data);
}

/*-----------------------------------------------------------------------*/

/* DC removes a edge from a sorted table and shift the remaining edges */
static Tedge
table_sorted_remove(Ttable table, unsigned s, unsigned d)
{
  unsigned len = table_length (table);
  int p = dl_get_pos_edge (s, d);
  Tedge edge = table_get (table, p);

  assert (p != -1);

  for (; p < len - 1; ++p)
    table_set (table, p, table_get (table, p + 1));
  table_pop (table);

  return edge;
}

/*-----------------------------------------------------------------------*/

/* DC removes last edge created */
static void
history_edge_created_back(void)
{
  Ttable source_table;
  unsigned degree;
  Tedge edge;
  Thistory_edge_created data = (Thistory_edge_created) dl_history->data;

  /* DC remove edge */
  source_table = (Ttable) table_get (dl_edge_table, data->source_id);
  edge = table_sorted_remove (source_table, data->source_id,
			      data->destination_id);
  list_free (&edge->list_clue);
  number_free(edge->weight);
  free (edge);

  /* DC reduce degree of source variable */
  degree = dl_degree (data->source_id);
  --degree;
  table_set (dl_variable_degree_table, data->source_id, (Tunsigned) degree);

  free (data);
}

/*-----------------------------------------------------------------------*/

/* DC changes edge to previous value */
static void
history_edge_edited_back()
{
  Ttable source_table;
  Tedge   edge;
  int pos_edge;
  Thistory_edge_edited data = (Thistory_edge_edited) dl_history->data;

  /* DC change weight value */
  source_table = (Ttable) table_get (dl_edge_table, data->source_id);
  pos_edge = dl_get_pos_edge (data->source_id, data->destination_id);
  assert (pos_edge != -1);
  edge = (Tedge) table_get (source_table, pos_edge);

  number_free(edge->weight);
  edge->weight = data->weight;
  list_free (&edge->list_clue);
  edge->list_clue = data->list_clue;
  
  free (data);
}

/*-----------------------------------------------------------------------*/

/* DC change distance to previous value */
static void
history_distance_edited_back()
{
  Thistory_distance_edited data = (Thistory_distance_edited) dl_history->data;
  /* DC change distance value */
  number_free (table_get(dl_distance_table, data->variable_id));
  table_set (dl_distance_table, data->variable_id, data->distance);
  free (data);
}

/*-----------------------------------------------------------------------*/

/* DC change the set of returned equalities to previous state */
static void
history_equality_found_back(void)
{
  Tclue clue = (Tclue) dl_history->data;
  /* DC change to previous state */
  set_remove (dl_set_returned_eq, (void *) clue);
  list_free (&clue->proof.arith);
  clue_free (clue);
}

/*-----------------------------------------------------------------------*/

/* DC change the set of returned model equalities to previous state */
static void
history_model_equality_found_back(void)
{
#ifdef DEBUG_DL
  my_message ("DL: model_equality_found_back()\n");
#endif
  Tclue clue = (Tclue) dl_history->data;
  /* DC change to previous state */
  set_remove(dl_set_returned_model_eq, (void *) clue);
  clue_free(clue);
}

/*-----------------------------------------------------------------------*/

/* DC change the set of pushed disequalities to previous state */
static void
history_disequality_pushed_back(void)
{
  /* DC change to previous state */
  table_pop(dl_table_disequalities);
}

/*-----------------------------------------------------------------------*/

/* DC goes back in time restoring the status */
static void
history_backtrack(unsigned level)
{
  while (dl_history && dl_history->level > level)
    {
      Thistory tmp;
      switch (dl_history->kind)
	{
	case VARIABLE_CREATED:
	  history_variable_created_back();
	  break;
	case EDGE_CREATED:
	  history_edge_created_back();
	  break;
	case EDGE_EDITED:
	  history_edge_edited_back();
	  break;
	case DISTANCE_EDITED:
	  history_distance_edited_back();
	  break;
	case EQUALITY_FOUND:
	  history_equality_found_back();
	  break;
	case MODEL_EQUALITY_FOUND:
	  history_model_equality_found_back();
	  break;
	case DISEQUALITY_PUSHED:
	  history_disequality_pushed_back();
	  break;
	default:
	  assert (0);
	}
      tmp = dl_history->next;
      free(dl_history);
      dl_history = tmp;
    }
}

/*-----------------------------------------------------------------------*/

/* DC initializes history */
static void
history_init(void)
{
  dl_history = NULL;
}

/*-----------------------------------------------------------------------*/

/* DC resets history */
static void
history_reset(void)
{
  while (dl_history != NULL)
    {
      Thistory tmp = dl_history->next;
      free(dl_history->data);
      free(dl_history);
      dl_history = tmp;
    }
}

/*-----------------------------------------------------------------------*/

/* DC finalizes history */
static void
history_done(void)
{
  history_reset();
}

/*
  --------------------------------------------------------------
  The real data structures
  --------------------------------------------------------------
*/

/* DC returns the position of (source_id, destination_id) edge in dl_edge_table[source_id], -1 if not found*/
static int
dl_get_pos_edge(unsigned source_id, unsigned destination_id)
{
  Ttable t = (Ttable) table_get (dl_edge_table, source_id);
  int ini;
  int end;
  int mid;

  ini = 0;
  end = table_length (t) - 1;
  mid = (ini + end) / 2;

  while (ini <= end)
    {
      unsigned d = ((Tedge) table_get (t, mid))->destination;
      if (d == destination_id)
	return mid;
      else if (d < destination_id)
	ini = mid + 1;
      else
	end = mid - 1;
      mid = (ini + end) / 2;
    }
  return -1;
}

/*-----------------------------------------------------------------------*/

/* DC returns the out degree of variable_id */
static unsigned
dl_degree(unsigned variable_id)
{
  return (unsigned) (Tunsigned) table_get(dl_variable_degree_table,
					  variable_id);
}

/*-----------------------------------------------------------------------*/

/* DC inserts a edge in a sorted table */
static void
dl_insertion_sort_edge(Ttable table, Tedge edge)
{
  int i;
  table_push(table, (void *) edge);
  for (i = table_length(table) - 2; i >= 0; --i)
    if (((Tedge) table_get(table, i))->destination > edge->destination)
      table_set(table, i + 1, table_get (table, i));
    else
      break;
  table_set(table, i + 1, (void *) edge);
}

/*-----------------------------------------------------------------------*/

/* DC generates and saves a lemma of the kind (x <= y + o) ==> (x <= y + n) */
/* where d < c */
/*static TDAG
generate_propagation_lemma (TDAG x, TDAG y, TDAG n, TDAG o)
{
  TDAG DAG_sum1, DAG_sum2, DAG_leq1, DAG_leq2, DAG_imp;

  DAG_sum1 =  (DAG_new_args (FUNCTION_SUM, y, o, NULL));
  DAG_sum2 =  (DAG_new_args (FUNCTION_SUM, y, n, NULL));

  DAG_leq1 =  (DAG_new_args (PREDICATE_LEQ, x, DAG_sum1, NULL));
  DAG_leq2 =  (DAG_new_args (PREDICATE_LEQ, x, DAG_sum2, NULL));

  DAG_imp = DAG_dup (DAG_new_args (CONNECTOR_IMPLIES, DAG_leq1, DAG_leq2, NULL));

#ifdef DEBUG_DL
  {
    my_DAG_message ("DL: LEMMA generated: %D\n", DAG_imp);
  }
#endif

  table_push(dl_lemmas_table, DAG_ptr_of(DAG_imp));
  return DAG_imp;
}*/

/*-----------------------------------------------------------------------*/
/*int counter = 0, pushes = 0;*/
/* DC adds a new edge in the relative level */
static void
dl_add_edge(unsigned source_id, unsigned destination_id,
	    Tnumber weight, Tlist list_clue)
{
  Tedge new_edge;
  unsigned degree;
  int pos_edge;
  Ttable source_table;

  /*++pushes;*/
  /* DC set new edge */
  source_table = (Ttable) table_get(dl_edge_table, source_id);
  pos_edge = dl_get_pos_edge(source_id, destination_id);
  if (pos_edge == -1)
    {
      /* DC new edge */
      MY_MALLOC(new_edge, sizeof (struct TSedge));
      new_edge->destination = destination_id;
      new_edge->weight = number_new();
      number_cpy(new_edge->weight, weight);
      new_edge->list_clue = list_cpy (list_clue);
      /* DC add new edge */
      dl_insertion_sort_edge(source_table, new_edge);
      /* DC raise degree of source variable */
      degree = dl_degree(source_id);
      ++degree;
      table_set(dl_variable_degree_table, source_id, (Tunsigned) degree);
      /* DC history recording */
      history_edge_created(source_id, destination_id, new_edge->list_clue);
    }
  else
    {
      /* DC edit edge */
      new_edge = (Tedge) table_get(source_table, pos_edge);
      /* DC is it a tighter constraint? */
      if (number_less(weight, new_edge->weight))
	{
	  /* DC history recording */
	  history_edge_edited(source_id, destination_id,
			      new_edge->weight, new_edge->list_clue);

	  /* DC changing */
	  number_cpy(new_edge->weight, weight);
	  new_edge->list_clue = list_cpy (list_clue);
	}     
      else
        {
      	  /*printf("Edge could have been deduced %d <= %d + (%.2lf, %.2lf), count = %d, pushes = %d, nvar = %d\n", source_id, destination_id, weight, new_edge->weight, ++counter, pushes, dl_variables_nb);*/
      	  
      	  /* DC generate lemmas about deduced clues; didn't show good results (few tests) */
      	  
      	  /*TDAG dag1 = table_get(dl_variable_DAG, source_id);
      	  TDAG dag2 = table_get(dl_variable_DAG, destination_id);
      	  TDAG dagnv = DAG_new_integer((int)round(weight));
      	  TDAG dagov = DAG_new_integer((int)round(new_edge->weight));
      	  TDAG lem = generate_propagation_lemma(dag1, dag2, dagnv, dagov), result = NULL;
      	  result = DAG_of_ptr(hash_lookup(dl_hash_generated_lemmas, lem));
          if (result == NULL)
            hash_insert(dl_hash_generated_lemmas, DAG_ptr_of(lem));
          else
            {
              table_pop (dl_lemmas_table);
              DAG_free(lem);
            }*/
       	}
    }

}

/*-----------------------------------------------------------------------*/

/* DC returns the destination variable of the pos_th edge of variable_id */
static unsigned
dl_edge_destination(unsigned variable_id, unsigned pos)
{
  Ttable source_table = (Ttable) table_get(dl_edge_table, variable_id);
  Tedge edge = (Tedge) table_get(source_table, pos);
  return edge->destination;
}

/*-----------------------------------------------------------------------*/

/* DC returns the weight of the pos_th edge of variable_id */
static Tnumber
dl_edge_weight(unsigned variable_id, unsigned pos)
{
  Ttable source_table = (Ttable) table_get(dl_edge_table, variable_id);
  Tedge edge = (Tedge) table_get(source_table, pos);
  return edge->weight;
}

/*-----------------------------------------------------------------------*/

/* DC returns the clue of the pos_th edge of variable_id */
static Tlist
dl_edge_list_clue(unsigned variable_id, unsigned pos)
{
  Ttable source_table = (Ttable) table_get(dl_edge_table, variable_id);
  Tedge edge = (Tedge) table_get(source_table, pos);
  return edge->list_clue;
}

/*-----------------------------------------------------------------------*/

/* DC returns the distance from "variable 0" to variable_id */
/* #define dl_get_distance(id) (((Tdistance) table_get(dl_distance_table, (id)))->distance) */
static Tnumber
dl_get_distance(unsigned variable_id)
{
  return table_get(dl_distance_table, variable_id);
}

/*-----------------------------------------------------------------------*/

/* DC sets a new distance from "variable 0" to variable_id in current level */
static void
dl_set_distance (unsigned variable_id, Tnumber distance)
{
  Tnumber new_distance = number_new();
  number_cpy(new_distance, distance);
  /* DC history recording */
  history_distance_edited(variable_id, dl_get_distance(variable_id));
  /* DC changing */
  table_set(dl_distance_table, variable_id, new_distance);
}

/*-----------------------------------------------------------------------*/

/* DC inserts a list of clues in a set */
static void
set_insert_list_clue(Tset set, Tlist list)
{
  Tlist ptr = list;
  Tlist ini = ptr;
  if (!list)
    return;
  do
    {
      Tclue clue = (Tclue) list_car(ptr);
      set_insert(set, clue);
      ptr = list_cdr(ptr);
    }
  while (ptr != ini);

}

/*-----------------------------------------------------------------------*/

#if 0

/* DC does a dfs improving the distance when is the case */
static Tstatus
dl_dfs_improve (unsigned source_id, char *visited)
{
  unsigned i;
#ifdef DEBUG_DL
  my_message ("DL: dfs_improve (%lu)\n", source_id);
#endif
  if (visited[source_id])
    return UNSAT;
  visited[source_id] = 1;
  /* DC for each variable leaving source_id */
  for (i = 0; i < dl_degree(source_id); ++i)
    {
      unsigned destination_id = dl_edge_destination(source_id, i);
      Tnumber weight = dl_edge_weight(source_id, i);
      /* DC if it improves, continue dfs */
      Tnumber sum = number_new();
      number_add(sum, dl_get_distance(source_id), weight);
      if (number_less(sum, dl_get_distance(destination_id)))
	{
	  dl_set_distance(destination_id, sum);
	  if (dl_dfs_improve(destination_id, visited) == UNSAT)
	    {
	      set_insert_list_clue(dl_conflict_set,
				   dl_edge_list_clue(source_id, i));
	      number_free(sum);
	      return UNSAT;
	    }
	}
      number_free(sum);
    }
  visited[source_id] = 0;
  return SAT;
}

#endif

/*-----------------------------------------------------------------------*/

/* DC compares two DAG addresses, been aware of overflows; returns < 0, 0 or > 0 */
#ifdef DEBUG
static int (* compare_int) (TDAG, TDAG) = DAG_cmp;
#else
static int
compare_int(TDAG d1, TDAG d2)
{
  intptr_t a = (intptr_t) d1;
  intptr_t b = (intptr_t) d2;
  if (a > b)
    return 1;
  else if (b > a)
    return -1;
  else
    return 0;
}
#endif

/*-----------------------------------------------------------------------*/

/* DC returns a int used to compare clue types */
static int
clue_type_order(Tclue c)
{
  int res = 1;
  if (c->polarity)
    res <<= 5;
  switch (c->type)
    {
    case CLUE_ABSTRACT_TERM: res <<= 4; break;
    case CLUE_ABSTRACT_PRED: res <<= 3; break;
    case CLUE_MERGE: res <<= 2; break;
    case CLUE_MODEL_EQUALITY: res <<= 2; break;
    default : my_error ("arith: clue_type_order: strange clue\n");
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
set_clue_compare(Tclue clue1, Tclue clue2)
{
  int result;
  if (clue1 == clue2)
    return 0;
  if ((result = (clue_type_order(clue1) - clue_type_order(clue2)) ) == 0)
    {
      if ((clue1->type == CLUE_ABSTRACT_TERM &&
	   clue2->type == CLUE_ABSTRACT_TERM) ||
	  (clue1->type == CLUE_ABSTRACT_PRED &&
	   clue2->type == CLUE_ABSTRACT_PRED))
         result = compare_int(clue1->DAG[0], clue2->DAG[0]);
      else /* if clue has 2 DAGs */
        {
          TDAG c1d1 = clue1->DAG[0], c1d2 = clue1->DAG[1];
          TDAG c2d1 = clue2->DAG[0], c2d2 = clue2->DAG[1];
          TDAG t;
          if (compare_int (c1d1, c1d2) > 0) t = c1d1, c1d1 = c1d2, c1d2 = t;
          if (compare_int (c2d1, c2d2) > 0) t = c2d1, c2d1 = c2d2, c2d2 = t;
          if ((result = compare_int(c1d1, c2d1)) == 0)
            result = compare_int(c1d2, c2d2);
        }
    }
  return result;
}

/*-----------------------------------------------------------------------*/

/* DC free function */
static void
set_clue_free(const void *a)
{
  /*clue_free ((Tclue) a); */
}

/*-----------------------------------------------------------------------*/

/* DC pseudo heap, remove min O(n) */
static unsigned
heap_remove_min(unsigned v[], Tnumber impr[], unsigned *n)
{
  unsigned i, index = 0;
  unsigned res;
  Tnumber best = number_zero;
  /* DC search */
  for (i = 0; i < *n; ++i)
    if (number_less(impr[v[i]], best))
      {
	best = impr[v[i]];
	index = i;
      }
  res = v[index];
  /* DC remove */
  for (i = index; i < (*n) - 1; ++i)
    v[i] = v[i + 1];
  --(*n);

  return res;
}

/*-----------------------------------------------------------------------*/

/* DC pseudo heap, insert O(1) */
static void
heap_insert_improve(unsigned heap[], Tnumber impr[], unsigned pre[], 
		    unsigned *n, 
		    unsigned source, unsigned dest, Tnumber value)
{
  if (number_less(value, impr[dest]))
    {
      if (number_equal(impr[dest], number_zero))
	heap[(*n)++] = dest;
      number_cpy(impr[dest], value);
      pre[dest] = source;
    }
}

/*-----------------------------------------------------------------------*/

/* DC solves the problem incrementally */
static Tstatus
dl_solve_incremental(unsigned source_id, unsigned destination_id, Tnumber cost)
{
  /* DC Old version of incremental solve, faster in some cases
     char visited[dl_variables_nb];
     memset (visited, 0, sizeof(visited));
     return dl_dfs_improve (source_id, visited); */
  unsigned size = dl_variables_nb;
  unsigned u, v;
  Tnumber value, d1, tmp;

  if (status == UNSAT)
    return status;

  if (source_id == destination_id && number_less(cost, number_zero))
    {
      status = UNSAT;
      set_insert_list_clue(dl_conflict_set,
			   dl_edge_list_clue(source_id,
					     dl_get_pos_edge(source_id,
							     destination_id)));
      return status;
    }

  u = source_id;
  v = destination_id;
  value = number_new();
  tmp = number_new();
  d1 = number_new();
  number_add(tmp, dl_get_distance (u), cost);
  number_sub(value, tmp, dl_get_distance (v));
  if (number_less(value, number_zero))
    {
      unsigned i;
      unsigned n;
      /* DC create pseudo heap */
      unsigned heap[size];
      Tnumber impr[size];
      unsigned pre[size];
      for (i = 0; i < size; ++i)
	{
	  impr[i] = number_new();
	  number_set(impr[i], 0);
	}
      /*memset (impr, 0, sizeof (impr));*/
      n = 0;

      heap_insert_improve(heap, impr, pre, &n, u, v, value);
      while (n > 0)
	{
	  v = heap_remove_min(heap, impr, &n);
	  number_add(d1, dl_get_distance (v), impr[v]);
	  dl_set_distance(v, d1);
	  /* DC for each variable leaving v */
	  for (i = 0; i < dl_degree (v); ++i)
	    {
	      unsigned t = dl_edge_destination (v, i);
	      Tnumber weight = dl_edge_weight (v, i);
	      number_sub(value, number_add(tmp, d1, weight), dl_get_distance(t));
	      if (number_less(value, impr[t]))
		{
		  if (t == source_id)
		    {
		      unsigned j;
		      pre[source_id] = v;
		      j = source_id;
		      /*printf("BEGIN Conflict Graph:\n");*/
		      do
			{
			  /*TDAG dag1 = table_get(dl_variable_DAG, pre[j]);
		            TDAG dag2 = table_get(dl_variable_DAG, j);
		            my_DAG_message("From %D to %D, clues are:\n", dag1, dag2);
		            list_clue_fprint (stdout, dl_edge_list_clue (pre[j], dl_get_pos_edge (pre[j], j)));*/
			  set_insert_list_clue(dl_conflict_set,
					       dl_edge_list_clue(pre[j], dl_get_pos_edge(pre[j], j)));
			  j = pre[j];
			}
		      while (j != source_id);
		      /*printf("END Conflict Graph.\n");*/
		      number_free(value);
		      number_free(tmp);
		      number_free(d1);
		      for (i = 0; i < size; ++i)
			number_free(impr[i]);
		      return UNSAT;
		    }
		  else
		    heap_insert_improve(heap, impr, pre, &n, v, t, value);
		}
	    }
	}
      for (i = 0; i < size; ++i)
	number_free(impr[i]);
    }
  number_free(value);
  number_free(tmp);
  number_free(d1);
  return SAT;
}

/*-----------------------------------------------------------------------*/

/* DC solves problem not considering any other previous result */
static Tstatus
dl_solve_not_incremental (void)
{
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC return the "slack" between 2 vertices */
/* DC POS CONDITION the number returned will be compared to zero */
static Tnumber
dl_slack (Tnumber res, unsigned var1, unsigned var2)
{
  Tnumber tmp;
  int pos = dl_get_pos_edge (var1, var2);
  if (pos == -1)
    return number_cpy(res, number_not_zero);
  tmp = number_new();
  number_add(res, number_sub(tmp, dl_get_distance(var1),
			     dl_get_distance(var2)),
	     dl_edge_weight (var1, pos));
  number_free(tmp);
  return res;
}

/*-----------------------------------------------------------------------*/

/* DC does the dfs necessary to search SCCs */
static void
dfs_time(const Ttable edge_table, unsigned finish_time[], char visited[], 
	 const unsigned vertice, int *time)
{
  int i;
  unsigned v;
  Ttable t = (Ttable) table_get(edge_table, vertice);
  visited[vertice] = 1;
  for (i = table_length(t) - 1; i >= 0; --i)
    {
      v = (unsigned) (Tunsigned) table_get(t, i);
      if (!visited[v])
	dfs_time(edge_table, finish_time, visited, v, time);
    }
  finish_time[(*time)++] = vertice;
}

/*-----------------------------------------------------------------------*/

/* DC does a bfs from source to dest, saving predecessors */
static void
bfs (const Ttable edge_table, char visited[], int pred[], 
     const unsigned source, const unsigned dest, const unsigned size)
{
  unsigned * queue;
  unsigned iqueue = 0;
  unsigned fqueue = 0;
  MY_MALLOC (queue, size * sizeof (unsigned));

  visited[source] = 1;
  pred[source] = -1;
  queue[fqueue++] = source;
  while (iqueue < fqueue)
    {
      unsigned u = queue[iqueue++];
      int i;
      Ttable t = (Ttable) table_get (edge_table, u);
      for (i = table_length(t) - 1; i >= 0; --i)
	{
	  unsigned v = (unsigned) (Tunsigned) table_get(t, i);
	  if (visited[v] == 0)
	    {
	      visited[v] = 1;
	      pred[v] = u;
	      if (v == dest)
		{
		  u = dest;
		  break;
		}
	      queue[fqueue++] = v;
	    }
	}
      if (u == dest)
	break;
    }
  free (queue);
}

/*-----------------------------------------------------------------------*/

/* DC function that compare a pair used in a qsort, first by the double then by the int */
static int
compare_Tnumber_int_pair (const void *a, const void *b)
{
  Tnumber_int_pair p1 = *((Tnumber_int_pair *) a);
  Tnumber_int_pair p2 = *((Tnumber_int_pair *) b);
  if (number_greater(p1.first, p2.first))
    return 1;
  else if (number_less(p1.first, p2.first))
    return -1;
  else if (p1.second == p2.second)
    return 0;
  else return p1.second > p2.second ? 1 : -1;
}

/*-----------------------------------------------------------------------*/

/* DC searchs for derivated equalities and saves them in a table for later use */
/* DC TODO THINK: Can this be incremental? */
static void
dl_search_equalities (void)
{
#ifdef PURE_ARITH 
  return; /* DC don't search and propagate equalities */
#endif
  unsigned source_id;
  unsigned n = dl_variables_nb;
  unsigned i;
  int pos, time, pre_time;
  /* DC finish_time[i] gives the vertice that finished at time i */
  unsigned * finish_time1;
  unsigned * finish_time2;
  char *visited_dfs, *visited_bfs;
  /* DC pair of variable and distance used to be sorted and find equalities */
  Tnumber_int_pair *var_dist;
  /* DC predecessors obtained from BFS to build the shortest path from x to y and y to x */
  int * pred_x;
  int * pred_y;
#ifdef DEBUG_DL
  my_message ("DL: dl_search_equalities()\n");
#endif

  /* DC init */
  MY_MALLOC (finish_time1, n * sizeof (unsigned));
  MY_MALLOC (finish_time2, n * sizeof (unsigned));
  MY_MALLOC (visited_dfs, n * sizeof (char));
  MY_MALLOC (visited_bfs, n * sizeof (char));
  MY_MALLOC (var_dist, n * sizeof (Tnumber_int_pair));
  MY_MALLOC (pred_x, n * sizeof (int));
  MY_MALLOC (pred_y, n * sizeof (int));

  table_apply (dl_edge_table_scc, (void (*)(void *)) table_erase);
  table_apply (dl_edge_table_scc_t, (void (*)(void *)) table_erase);

  for (i = table_length (dl_edge_table_scc); i < n; ++i)
    {
      table_push(dl_edge_table_scc, table_new(INIT_SIZE, INCREMENT));
      table_push(dl_edge_table_scc_t, table_new(INIT_SIZE, INCREMENT));
    }

  /* DC build graphs to look for scc */
  for (source_id = 0; source_id < n; ++source_id)
    {
      Ttable t = (Ttable) table_get (dl_edge_table_scc, source_id);
      for (pos = 0; pos < dl_degree (source_id); ++pos)
	{
	  unsigned destination_id = dl_edge_destination (source_id, pos);
	  Tnumber sl = number_new();
	  if (number_equal(dl_slack (sl, source_id, destination_id),
			   number_zero))
	    {
	      Ttable t2 = (Ttable) table_get(dl_edge_table_scc_t,
					     destination_id);
	      table_push(t, (void *) (Tunsigned) destination_id);
	      table_push(t2, (void *) (Tunsigned) source_id);
	    }
	  number_free(sl);
	}
    }

  /* DC first dfs */
  memset (visited_dfs, 0, n * sizeof(char));
  time = 0;
  for (i = 0; i < n; ++i)
    if (!visited_dfs[i])
      dfs_time (dl_edge_table_scc, finish_time1, visited_dfs, i, &time);

  /* DC second dfs, in the order of decreasing finish_time1 */
  memset (visited_dfs, 0, n * sizeof(char));
  memset (visited_bfs, 1, n * sizeof(char));
  time = 0;
  if (n != 0)
    {
      i = n - 1;				       
      while (true)
      {
	if (!visited_dfs[finish_time1[i]])
	  {
	    unsigned j;
	    unsigned k;

	    pre_time = time;
	    dfs_time (dl_edge_table_scc_t, finish_time2, visited_dfs, finish_time1[i], &time);
	    /* DC the tree with root "finish_time1[i]" is a SCC */
	    /* all vertices of this tree are in finish_time2[pre_time] .. finish_time2[time-1] */
	    /* DC TODO IMPROVE?, below can be done in linear time average (hash), instead of n log n (set) */
	    for (j = pre_time, k = 0; j < time; ++j, ++k)
	      {
		var_dist[k].first = dl_get_distance (finish_time2[j]);
		var_dist[k].second = finish_time2[j];
	      }
	    qsort (var_dist, time - pre_time, sizeof (Tnumber_int_pair), compare_Tnumber_int_pair);
	    for (j = 1; j < time - pre_time; ++j)
	      {
		if (number_equal (var_dist[j].first, var_dist[j - 1].first))	/* DC x == y */
		  {
		    /* DC Mount clue and save it */
		    Tclue clue;
		    TUproof proof;
		    unsigned id1, id2;
		    TDAG DAG1, DAG2;
		    id1 = var_dist[j].second;
		    id2 = var_dist[j - 1].second;
		    DAG1 = DAG_of_ptr(table_get(dl_variable_DAG, id1));
		    DAG2 = DAG_of_ptr(table_get(dl_variable_DAG, id2));
		    proof.generic = (void *) 0;
		    clue = clue_new_merge (DAG1, DAG2, dl_id, proof);

		    if (set_insert (dl_set_returned_eq, (void *) clue))
		      {
			/* DC search for the shortest path (optimal premisses set) from id1 to id2 and from id2 to id1 */
			for (k = pre_time; k < time; ++k)
			  {
			    visited_bfs[finish_time2[k]] = 0;
			    pred_y[finish_time2[k]] = -1;
			  }
			bfs (dl_edge_table_scc, visited_bfs, pred_y, id1, id2, time - pre_time);
			for (k = pre_time; k < time; ++k)
			  {
			    visited_bfs[finish_time2[k]] = 0;
			    pred_x[finish_time2[k]] = -1;
			  }
			bfs (dl_edge_table_scc, visited_bfs, pred_x, id2, id1, time - pre_time);
			for (k = pre_time; k < time; ++k)
			  visited_bfs[finish_time2[k]] = 1;
			/* DC save it */
			clue->proof.arith = dl_compute_premisses (clue, clue->DAG[0], clue->DAG[1], pred_x, pred_y);
			table_push(dl_var_eq_table, (void *) clue);
			history_equality_found (clue);
		      }
		    else
		      clue_free(clue);
		  }
	      }
	  }
	if (i == 0) break;
	--i;
      }
    }
  /* DC free */
  free (finish_time1);
  free (finish_time2);
  free (visited_bfs);
  free (visited_dfs);
  free (var_dist);
  free (pred_x);
  free (pred_y);
}

/*-----------------------------------------------------------------------*/

/* 
  DC TODO is this the best lemma overall?; (few tests) the best so far
  
  DC generates and saves a lemma of the kind (x!=y) ==> (x<y||x>y) 
  "!(dag1 == dag2) ==> !(dag1 <= dag2) || !(dag2 <= dag1))"
  "(dag1 == dag2) || !(dag1 <= dag2) || !(dag2 <= dag1))"
*/
static TDAG
generate_disequality_lemma (TDAG dag1, TDAG dag2)
{
  TDAG DAG_n_1l2, DAG_n_2l1, DAG_or;
  DAG_n_1l2 = DAG_not(DAG_new_args(PREDICATE_LEQ, dag1, dag2, NULL));
  DAG_n_2l1 = DAG_not(DAG_new_args(PREDICATE_LEQ, dag2, dag1, NULL));
  DAG_or = DAG_dup(DAG_new_args(CONNECTOR_OR, DAG_eq(dag1, dag2),
				DAG_n_1l2, DAG_n_2l1, NULL));
#ifdef PROOF
  proof_add_disequality_lemma(DAG_dup(DAG_or));
#endif
  table_push(dl_lemmas_table, DAG_ptr_of(DAG_or));
#ifdef DEBUG_DL
  my_DAG_message("DL: LEMMA generated: %D\n", DAG_or);
#endif
  return DAG_or;
}

/*-----------------------------------------------------------------------*/

#ifdef PURE_ARITH

/* DC checks if the DAG is a number */
static int
dl_DAG_is_num(TDAG DAG)
{
  return (DAG_arity(DAG) == 0 && DAG_is_number(DAG)) ||
    (DAG_arity(DAG) == 1 && DAG_is_number(DAG_arg0(DAG)));
}

/*-----------------------------------------------------------------------*/

/* DC reads a value from a constant DAG */
/* TODO unify with arith_DAG_readable_value */
static Tnumber
dl_DAG_readable_value(Tnumber res, TDAG constant)
{
  if (DAG_arity(constant) == 0)
    return number_from_DAG(res, constant);
  else
    return number_neg(dl_DAG_readable_value(res, DAG_arg0(constant)));
}

/*-----------------------------------------------------------------------*/

/* DC returns from a "SUM DAG" of the kind "DAG + int" the int and DAG part */
static void
dl_DAG_sum_split(TDAG DAG, TDAG *res, Tnumber *v)
{
  if (dl_DAG_is_num (DAG_arg0(DAG)))
    *v = dl_DAG_readable_value(*v, DAG_arg0(DAG)), *res = DAG_arg1(DAG);
  else if (dl_DAG_is_num (DAG_arg1(DAG)))
    *v = dl_DAG_readable_value(*v, DAG_arg1(DAG)), *res = DAG_arg0(DAG);
#ifdef DEBUG_DL
  else
    my_DAG_error("DAG %D is not of kind SUM\n", dag); 
#endif
}

#endif /* PURE_ARITH */

/*-----------------------------------------------------------------------*/

/* DC searchs for model equalities and saves them in a table for later use */
static void
dl_search_model_equalities (void)
{
  unsigned i;
  /* DC number of variables */
  int size;
  /* DC pair of variable and distance used to be sorted and find model equalities */
  Tnumber_int_pair *var_dist;
#ifdef PURE_ARITH
  Tnumber v = number_new(), t = number_new();
#endif

#ifdef DEBUG_DL
  {
    Tlist list;
    my_message("DL: dl_search_model_equalities()\n");
    my_message("DL: number of disequalities = %d\n",
	       table_length(dl_table_disequalities));
    for (i = 0; i < table_length(dl_table_disequalities); ++i)
      {
	clue_fprint(stderr, table_get(dl_table_disequalities, i)); 
	fprintf(stderr, "\n");
      }
    my_message ("DL: number returned equalities = %d\n",
		set_size(dl_set_returned_eq));
    list = set_list(dl_set_returned_eq);
    list_clue_fprint(stderr, list);
  
    my_message ("DL: Disequalities\n");
    for (i = 0; i < table_length(dl_table_disequalities); ++i)
      {
	Tclue clue = table_get (dl_table_disequalities, i);
	my_DAG_message("%D != %D\n", clue->DAG[0], clue->DAG[1]);
      }
    my_message ("DL: Equalities\n");
    if (list)
      {
        Tlist ptr = list;
        do
          {
	    Tclue clue = (Tclue) list_car (ptr);
	    my_DAG_message("%D = %D\n", clue->DAG[0], clue->DAG[1]);
	    ptr = list_cdr (ptr);
	  }
        while (ptr != list);
      }
    else
      {
        fprintf(stderr,"empty\n");
      }  
  }
#endif

  /* DC don't generate model equalities if the model needs to be corrected */
  if (dl_model_lemma)
    return;

  /* DC init */
  size = dl_variables_nb;
  MY_MALLOC (var_dist, size * sizeof (Tnumber_int_pair));

  /* DC pre-process: ignore variable 0, copy and sort */
  for (i = 1; i < size; ++i)
    {
      var_dist[i - 1].first = dl_get_distance (i);
      var_dist[i - 1].second = i;
    }
  --size;
  qsort (var_dist, size, sizeof (Tnumber_int_pair), compare_Tnumber_int_pair);

  /* DC find model equalities */
  for (i = 1; i < size; ++i)
    if (number_equal(var_dist[i].first, var_dist[i - 1].first))	/* DC x == y */
      {
	/* DC Mount clue and save it */
	Tclue clue;
	TDAG DAG1 = DAG_of_ptr(table_get(dl_variable_DAG, var_dist[i].second));
	TDAG DAG2 = DAG_of_ptr(table_get(dl_variable_DAG, var_dist[i - 1].second));
	clue = clue_new_model_equality(DAG1, DAG2, dl_id);

	/* DC not a normal equality and not already found */
	if (set_lookup(dl_set_returned_eq, (void *) clue) == NULL)
	  {
	    if (set_insert(dl_set_returned_model_eq, (void *) clue))
              table_push(dl_model_eq_table, (void *) clue);
	    else
	      clue_free(clue);
	  }
	else
	  clue_free(clue);
      }
      
  /* DC searches for a conflict between a disequality and model equalities */
  for (i = 0; i < table_length(dl_table_disequalities); ++i)
    {
      Tclue c = (Tclue) table_get(dl_table_disequalities, i);
      TDAG dag1 = c->DAG[0], dag2 = c->DAG[1];
      unsigned d1;
      unsigned d2;
      
#ifdef PURE_ARITH
      TDAG d = NULL;
      if (DAG_symb(dag1) == FUNCTION_SUM)
        {
          dl_DAG_sum_split(dag1, &d, &v);
          d1 = dl_variable_id(d);
          d2 = dl_variable_id(dag2);
	  number_sub(t, dl_get_distance(d1), dl_get_distance(d2));
	  number_neg(v);
          if (number_equal(t, v))
            {
              dl_model_lemma = 1;
              generate_disequality_lemma(dag1, dag2);
              continue;
            }
        }
      else if (DAG_symb(dag2) == FUNCTION_SUM)
        {
          dl_DAG_sum_split(dag2, &d, &v);
          d1 = dl_variable_id(dag1);
          d2 = dl_variable_id(d);
	  number_sub(t, dl_get_distance(d1), dl_get_distance(d2));
          if (number_equal(t, v))
            {
              dl_model_lemma = 1;
              generate_disequality_lemma(dag1, dag2);
              continue;
            }
        }
      else
#endif
        {
          d1 = dl_variable_id(dag1);
          d2 = dl_variable_id(dag2);
          if (number_equal(dl_get_distance(d1), dl_get_distance(d2)))
            {
              dl_model_lemma = 1;
              generate_disequality_lemma(dag1, dag2);
              continue;
            }
        }
    }

  /* DC Model equalities are only really saved if there are no problems with disequalities */
  if (!dl_model_lemma
  #ifdef PURE_ARITH
  && false /* DC don't propagate model equalities */
  #endif
  ) 
    for (i = 0; i < table_length(dl_model_eq_table); ++i)
      history_model_equality_found((Tclue)table_get(dl_model_eq_table, i));
  else
    {
      for (i = 0; i < table_length(dl_model_eq_table); ++i)
        {
          Tclue clue = (Tclue) table_get(dl_model_eq_table, i);
          set_remove(dl_set_returned_model_eq, clue);
          clue_free(clue);
        }
      table_erase(dl_model_eq_table);
    }
    
  /* DC free */
  free(var_dist);
#ifdef PURE_ARITH
  number_free(v);
  number_free(t);
#endif
}

/*-----------------------------------------------------------------------*/

/* DC receives a new predicate clue with head symbol <=, of the type (x - y <= c) */
static void
dl_push_difference(TDAG x, TDAG y, Tnumber c, Tlist clue_list)
{
  unsigned id_x = dl_variable_id(x);
  unsigned id_y = dl_variable_id(y);
  dl_add_edge(id_y, id_x, c, clue_list);

  /* DC incremental solving, INTERFACE CONFLICT: IS IT ALWAYS INCREMENTAL OR NEVER? */
  status = dl_solve_incremental(id_y, id_x, c);
}

/*-----------------------------------------------------------------------*/

/* DC mount the path form source to dest using predecessor */
static void
collect_clues(unsigned source, unsigned dest, Tset clues, const int pred[])
{
  while (dest != source)
    {
      int p = pred[dest];
      Tlist ptr = dl_edge_list_clue(p, dl_get_pos_edge(p, dest));
      Tlist ini = ptr;
      if (ptr != NULL)
	do
	  {
	    Tclue clue = (Tclue) list_car(ptr);
	    set_insert(clues, clue);
	    ptr = list_cdr(ptr);
	  }
	while (ptr != ini);
      dest = p;
    }
}

/*-----------------------------------------------------------------------*/

/* DC returns a list of premisses of an equality */
static Tlist
dl_compute_premisses(const Tclue clue, TDAG DAG1, TDAG DAG2, 
		     const int pred_x[], const int pred_y[])
{
  unsigned x = dl_variable_id(DAG1);
  unsigned y = dl_variable_id(DAG2);
  Tset set_premisses = set_new((TFcmp) set_clue_compare,
			       (TFfree) set_clue_free);
  Tlist premisses_list;
  /* DC path from x to y */
  collect_clues (x, y, set_premisses, pred_y);
  /* DC path from y to x */
  collect_clues (y, x, set_premisses, pred_x);
  premisses_list = set_list(set_premisses);
  set_free (&set_premisses);
#ifdef DEBUG_DL
  {
    my_message ("DL: dl_premisses (");
    clue_fprint (stderr, clue);
    fprintf (stderr, ")\n");
    list_clue_fprint (stderr, premisses_list);
  }
#endif
  return premisses_list;
}

/*-------------------------------------------------------------------------
	GLOBAL FUNCTIONS
-------------------------------------------------------------------------*/

/* DC sets a id to arith */
static void
dl_set_id(const int id)
{
  dl_id = id;
  dl_mask = 1 << id;
}

/*-----------------------------------------------------------------------*/

/*
 DC Everything pushed will be treated as x <= y (+c)
 where x and y are two arbitrary DAGs 
 and c is a numerical constant received apart
*/
Tstatus
dl_push(TDAG x, TDAG y, Tnumber c, Tlist clue_list)
{
#ifdef DEBUG_DL
  my_DAG_message ("DL: push {%D <= %D + ", x, y);
  fprintf(stderr, "(%.15lf), level %d, n_var = %d}\n", 
	  number_to_double(c), level + 1, dl_variables_nb);
#endif
  ++level;
  /* DC is it UNSAT already? */
  if (status == UNSAT)
    return status;
  status = SAT;
  if (!x)
    return status;
  /* DC add to the graph */
  dl_push_difference(x, y, c, clue_list);
  /* DC status */
#ifdef DEBUG_DL
  my_message("DL: push(solve) -> result = %s, level %d\n",
	     status == SAT ? "SAT" : "UNSAT", level);
#endif
  if (status == UNSAT)
    unsat_level = level;
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC save disequalities to check the consistency against model equalities generated */
void
dl_push_disequality (Tclue clue)
{
#ifdef DEBUG_DL
  my_DAG_message ("DL: dl_push_disequality: %D != %D\n",
		  clue->DAG[0], clue->DAG[1]);
#endif
  ++level;
  if (status == UNSAT)
    return;
  table_push(dl_table_disequalities, clue);
  history_disequality_pushed (clue);
}

/*-----------------------------------------------------------------------*/

/* DC current problem has integer variables; generate models */
void
dl_set_idl ()
{
  is_idl = true;
}

/*-----------------------------------------------------------------------*/

/* DC current problem do not have integer variables */
void
dl_set_rdl ()
{
  is_idl = false;
}

/*-----------------------------------------------------------------------*/

/* DC if current status == SAT then takes the last clue pushed out, otherwise does nothing */
void
dl_pop (void)
{
#ifdef DEBUG_DL
  my_message ("DL: pop(), level = %d\n", level-1);
#endif
  dl_search_scc = 0;
  dl_search_model_eq = 0;

  history_backtrack(--level);
  if (status == UNSAT && level < unsat_level)
    {
      status = (level == 0 ? OPEN : SAT);
      set_free(&dl_conflict_set);
      dl_conflict_set = set_new((TFcmp) set_clue_compare,
				(TFfree) set_clue_free);
    }
  dl_print (stderr);
}

/*-----------------------------------------------------------------------*/

/* DC solves constraints */
Tstatus
dl_solve(void)
{
#ifdef DEBUG_DL
  my_message ("DL: solve()\n");
#endif
  dl_print(stderr);

  /* DC search for equalities just after calling solve, it's a bit heavy computation */
  dl_search_scc = 1;

  /* DC search for model equalities just after calling solve, we want to avoid them as long as possible */
  dl_search_model_eq = 1;

#ifdef DEBUG_DL
  my_message ("DL: dl_solve -> result = %s, level %d\n", status == SAT ? "SAT" : "UNSAT", level);
#endif

  if (status != UNDEF)
    return status;

  /* DC solve not incremental, INTERAFACE CONFLICT: IF INCREMENTAL IT WILL NEVER BE CALLED */
  status = dl_solve_not_incremental();
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC returns current status */
Tstatus
dl_status(void)
{
  return status;
}

/*-----------------------------------------------------------------------*/

/* DC returns a list of conflict constraints (clue) when UNSAT */
Tlist
dl_conflict(void)
{
#ifdef DEBUG_DL
  {
    Tlist list = set_list(dl_conflict_set);
    my_message("DL: dl_conflict_list ()\n");
    list_clue_fprint(stderr, list);
    my_message("DL: dl_conflict_list.\n");
    list_free(&list);
  }
#endif
  return set_list(dl_conflict_set);
}

/*-----------------------------------------------------------------------*/

/* DC returns a list of premisses of a equality (clue) */
Tlist
dl_premisses(const Tclue clue)
{
  assert (clue->origin == dl_id);
  return clue->proof.arith;
}

/*-----------------------------------------------------------------------*/

/* DC returns found lemmas in the given table */
void
dl_lemmas(Tstack_DAG * Plemmas)
{
#ifdef DEBUG_DL
  my_message ("DL: dl_lemmas()\n");
#endif
  while (!table_empty(dl_lemmas_table))
    stack_push(*Plemmas, DAG_of_ptr(table_pop(dl_lemmas_table)));
  /* DC lemma was given, the model will be changed */
  dl_model_lemma = 0;
}

/*-----------------------------------------------------------------------*/

/* DC returns true if there is a new lemma found */
bool
dl_has_lemma(void)
{
#ifdef DEBUG_DL
  my_message ("DL: dl_has_lemma()\n");
#endif

  /* DC generate splitting lemmas for disequalities */
  /* DC currently only (x != y ==> x > y xor x < y) is implemented */
  if (split_on_demand)
    {
      int i;
      for (i = 0; i < table_length(dl_table_disequalities); ++i)
        {
          Tclue c;
          TDAG d1, d2, lem, result;
              
          c = (Tclue) table_get(dl_table_disequalities, i);
          d1 = c->DAG[0];
          d2 = c->DAG[1];
          lem = generate_disequality_lemma(d1, d2);

          result = DAG_of_ptr(hash_lookup(dl_hash_generated_lemmas, DAG_ptr_of(lem)));
          if (result == DAG_NULL)
            hash_insert(dl_hash_generated_lemmas, DAG_ptr_of(lem));
          else
            {
              table_pop(dl_lemmas_table);
              DAG_free(lem);
            }
        }
    }
  return !table_empty(dl_lemmas_table);
}

/*-----------------------------------------------------------------------*/

/* DC returns true when there is still a equality to pop */
bool
dl_eq_queue_empty(void)
{
  if (status == UNSAT)
    return true;
#ifdef DEBUG_DL
  {
    my_message ("DL: eq_queue_empty() --> %d, nb eq = %d\n",
		dl_search_scc, table_length (dl_var_eq_table));
  }
#endif
  if (dl_search_scc)
    {
      dl_search_equalities ();
      dl_search_scc = 0;
    }
  return table_empty (dl_var_eq_table);
}

/*-----------------------------------------------------------------------*/

/* DC returns a equality found when solving */
Tclue
dl_eq_queue_pop (void)
{
  assert (!dl_eq_queue_empty());
#ifdef DEBUG_DL
  my_message ("DL: eq_queue_pop() --> %d\n", dl_search_scc);
#endif
  if (status == SAT && dl_search_scc)
    {
      dl_search_equalities();
      dl_search_scc = 0;
    }
#ifdef DEBUG_DL
  {
    Tclue clue = (Tclue) table_pop(dl_var_eq_table);
    my_message("DL: eq_queue_pop(), %d\n", dl_search_scc);
    clue_fprint(stderr, clue);
    fprintf(stderr, "\n");
    return clue;
  }
#endif
  return (Tclue) table_pop(dl_var_eq_table);
}

/*-----------------------------------------------------------------------*/

/* DC returns true when there is still a model equality to pop */
bool
dl_model_eq_queue_empty(void)
{

  if (status == UNSAT || split_on_demand)
    return true;

#ifdef DEBUG_DL
  my_message ("DL: model_eq_queue_empty() --> %d, nb model_eq = %d\n",
	      dl_search_model_eq, table_length(dl_model_eq_table));
#endif

  if (dl_search_model_eq && is_idl)
    {
      dl_search_model_equalities();
      dl_search_model_eq = 0;
    }
  return dl_model_lemma || table_empty(dl_model_eq_table);
}

/*-----------------------------------------------------------------------*/

/* DC returns a model equality found */
Tclue
dl_model_eq_queue_pop(void)
{
  assert (!dl_model_eq_queue_empty());
#ifdef DEBUG_DL
    my_message ("DL: model_eq_queue_pop() --> %d\n", dl_search_model_eq);
#endif
  if (status == SAT && dl_search_model_eq && is_idl)
    {
      dl_search_model_equalities();
      dl_search_model_eq = 0;
    }
#ifdef DEBUG_DL
  {
    Tclue clue = (Tclue) table_pop(dl_model_eq_table);
    my_message("DL: model_eq_queue_pop(), %d\n", dl_search_model_eq);
    clue_fprint(stderr, clue);
    fprintf(stderr, "\n");
    return clue;
  }
#endif
  return (Tclue) table_pop (dl_model_eq_table);
}

/*-----------------------------------------------------------------------*/

/* DC print intern data */
void
dl_print (FILE * file)
{
#ifdef DEBUG_DL_DATA_STATE
  int i, j;
  my_message ("DL: DATA BEGIN *****************************************\n");
  my_message ("Number of Variables: %d\n", dl_variables_nb);
  my_message ("Number of pushed clues = %d\n", level);

  my_message ("\n");
  my_message ("Distance (var_id, dist):");
  for (i = 0; i < dl_variables_nb; ++i)
    my_message (" (%d, %lf)", i, table_get (dl_distance_table, i));
  my_message ("\n\n");
  my_message ("Edges (dest, cost):\n");
  for (i = 0; i < dl_variables_nb; ++i)
    {
      my_message ("(Degree = %d)", dl_degree (i));
      for (j = 0; j < dl_degree (i); ++j)
	my_message (" (%d, %lf)", dl_edge_destination (i, j), number_to_double(dl_edge_weight (i, j)));
      my_message ("\n");
    }
  my_message ("\n");
  my_message ("Edges Position:\n");
  my_message ("		");
  for (j = 0; j < dl_variables_nb; ++j)
    my_message ("%4d", j);
  my_message ("\n");
  my_message ("----");
  for (j = 0; j < dl_variables_nb; ++j)
    my_message ("----");
  my_message ("\n");
  for (i = 0; i < dl_variables_nb; ++i)
    {
      my_message ("%3d|", i);
      for (j = 0; j < dl_variables_nb; ++j)
	my_message ("%4d", dl_get_pos_edge (i, j));
      my_message ("\n");
    }

  my_message ("\n");
  my_message ("Status = %s\n", (status == OPEN ? "OPEN" : (status == SAT ? "SAT" : "UNSAT")));
  if (status == UNSAT)
    {
      my_message ("\tConflict list:\n");
      list_clue_fprint (stderr, set_list (dl_conflict_set));
    }

  my_message ("DL: DATA END *******************************************\n");
#endif
}

/*-----------------------------------------------------------------------*/

/* DC inits data structures */
void
dl_init (const unsigned id)
{
  Ttable t;
  int i;

  dl_set_id (id);

  dl_sentinel_id = 0;
  status = OPEN;
  dl_search_scc = 0;
  dl_search_model_eq = 0;
  dl_model_lemma = 0;
  is_idl = false;

  level = 0;
  unsat_level = 0;
  dl_variables_nb = 1;

  dl_variable_id_hash = hash_new (INIT_SIZE, (TFhash) variable_id_hash, 
				  (TFequal) variable_id_equal, 
				  (TFfree) variable_id_free);

  dl_hash_generated_lemmas = hash_new (INIT_SIZE, (TFhash) DAG_hash, (TFequal) DAG_equal, NULL);

  dl_edge_table = table_new (INIT_SIZE, INCREMENT);
  t = table_new (INIT_SIZE, INCREMENT);
  table_push(dl_edge_table, (void *) t);

  dl_variable_degree_table = table_new (INIT_SIZE, INCREMENT);
  table_push(dl_variable_degree_table, 0);

  dl_distance_table = table_new (INIT_SIZE, INCREMENT);
  table_push(dl_distance_table, number_zero);

  dl_variable_DAG = table_new (INIT_SIZE, INCREMENT);
  table_push(dl_variable_DAG, NULL);

  dl_conflict_set = set_new ((TFcmp) set_clue_compare, (TFfree) set_clue_free);

  history_init ();
  dl_var_eq_table = table_new (INIT_SIZE, INCREMENT);
  dl_set_returned_eq = set_new ((TFcmp) set_clue_compare, (TFfree) set_clue_free);

  dl_model_eq_table = table_new (INIT_SIZE, INCREMENT);
  dl_set_returned_model_eq = set_new ((TFcmp) set_clue_compare, (TFfree) set_clue_free);

  dl_table_disequalities = table_new (INIT_SIZE, INCREMENT);

  dl_lemmas_table = table_new(INIT_SIZE, INCREMENT);

  dl_edge_table_scc = table_new (INIT_SIZE, INCREMENT);
  dl_edge_table_scc_t = table_new (INIT_SIZE, INCREMENT);
  for (i = 0; i < INIT_SIZE; ++i)
    {
      table_push(dl_edge_table_scc, table_new (INIT_SIZE, INCREMENT));
      table_push(dl_edge_table_scc_t, table_new (INIT_SIZE, INCREMENT));
    }

  options_new (0, "split-on-demand", "Use Splitting on Demand instead of Model Equalities for completeness. It does not work for some theory combinations such as UFIDL, UFLIA", &split_on_demand);
    
}

/*-----------------------------------------------------------------------*/

/* DC frees the data */
void
dl_done (void)
{
  Ttable t;
  int i;

  /* DC free data created during pushes */
  level = 0;
  unsat_level = 0;
  history_backtrack (level);
  history_done ();

  /* DC free data created during init */
  hash_free (&dl_variable_id_hash);

  t = (Ttable) table_pop (dl_edge_table);
  table_free (&t);
  assert (table_empty (dl_edge_table));
  table_free (&dl_edge_table);

  table_free (&dl_variable_degree_table);
  table_free (&dl_distance_table);
  table_free (&dl_variable_DAG);

  set_free (&dl_conflict_set);
  set_free (&dl_set_returned_eq);
  set_free (&dl_set_returned_model_eq);
  table_free (&dl_var_eq_table);
  table_free (&dl_model_eq_table);
  table_free (&dl_lemmas_table);
  table_free (&dl_table_disequalities);
  hash_free (&dl_hash_generated_lemmas);

  for (i = table_length (dl_edge_table_scc) - 1; i >= 0; --i)
    {
      Ttable t = table_get (dl_edge_table_scc, i);
      table_free (&t);
      t = table_get (dl_edge_table_scc_t, i);
      table_free (&t);
    }
  table_free (&dl_edge_table_scc);
  table_free (&dl_edge_table_scc_t);

#ifdef DEBUG_DL
  my_message ("DL: done (end)\n");
#endif
}

/*-----------------------------------------------------------------------*/

/* DC resets the data */
void
dl_reset (void)
{
  dl_sentinel_id = 0;
  status = OPEN;
  dl_variables_nb = 1;
  level = 0;
  unsat_level = 0;
  dl_search_scc = 0;
  dl_search_model_eq = 0;
  dl_model_lemma = 0;
  is_idl = false;

  /* DC free data created during pushes */
  history_backtrack (level);
  history_reset ();

  /* DC reset data created during init */
  set_free (&dl_conflict_set);
  dl_conflict_set = set_new ((TFcmp) set_clue_compare,
			     (TFfree) set_clue_free);

  table_erase (dl_var_eq_table);
  table_erase (dl_model_eq_table);
  table_erase (dl_lemmas_table);

  set_free (&dl_set_returned_eq);
  dl_set_returned_eq = set_new ((TFcmp) set_clue_compare,
				(TFfree) set_clue_free);

  set_free (&dl_set_returned_model_eq);
  dl_set_returned_model_eq = set_new ((TFcmp) set_clue_compare,
				      (TFfree) set_clue_free);

  table_erase (dl_table_disequalities);
  hash_erase (dl_hash_generated_lemmas);
}
