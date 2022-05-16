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
  \file la.c

  \author Diego Caminha

  \brief Linear arithmetic decision procedure implementation.

  Implementation of a linear arithmetic decision procedure based on a variation of the simplex method.

*/

/* #define DEBUG_LA */

#ifdef DEBUG_LA
  #define PRINT_LA
#endif

/*#define PRINT_LA*/

#ifdef PRINT_LA
  #include <stdio.h>
#endif

#include <stdbool.h>
#include "config.h"
#include "la.h"
#include "list.h"
#include "table.h"
#include "set.h"
#include "general.h"
#include "hashmap.h"

static const unsigned TABLE_INIT_SIZE = 100;
static const unsigned TABLE_INCREMENT = 100;

typedef struct TShistory*   Thistory;

typedef struct TSvar*         Tvar;
typedef struct TSmon*         Tmon;
typedef struct TSexp*         Texp;
typedef struct TSdisequality* Tdisequality;
typedef struct TSequality*    Tequality;
typedef struct TSequation*    Tequation;
typedef struct TSvar_prop*    Tvar_prop;
typedef struct TSsimplex*     Tsimplex;

/** \brief A pair of Tnumber and Tvar_id.*/
typedef struct
{
  Tnumber first; /**< First element of the pair */
  Tvar_id second; /**< Second element of the pair */
} Tnumber_int_pair;

/** \brief Possible kinds of expression. */
typedef enum{
  LA_USER,    /**< Created by the user and used by \e equation->le */
  LA_INTERNAL /**< Created internally and used by \e equation->comb */
}Texp_kind;

/**
 \brief Simplex.
 \remarks It should be possible to run more than one simplex at time.
*/
struct TSsimplex
{
  /** \brief Goal. It may be a minimization or reach goal.*/
  Tequation goal;
  /** \brief Table of equations. The pushed constraints are added here. */
  Ttable eq;
  /** \brief Table of disequalities. */
  Ttable disequalities;
  /** \brief Status of consistency. */
  bool consistent;
  /** \brief Id of the constraints that lead to a conflict. */
  Tlist conflict;
  /** \brief The properties of the variables in the simplex.
     The id of a variable points to the index in this table. */
  Ttable vp;
  /** \brief Current value of the solution. */
  Tnumber sol;
  /** \brief Maps the user variable id to internal variable id. */
  Thashmap hmid;
  /** \brief Number of pushes so far. */
  int level;
  
  /** \brief This is set true when there is an infinite loop in the branch and bound of integer cases. */
  bool cannot_find_solution;
  /** \brief If it is true then we can look for model equalities. */
  bool search_model_equalities;
  /** \brief Contains the conflicts between disequalities and the current model.
      It contains disequalities. */
  Ttable model_conflict;
  /** \brief Contains the equalities that can be extracted from the current model. */
  Ttable model_eq;
  /** \brief Set of returned equalities and model equalities. */
  Tset returned_eq;
  
  /** \brief List of events recorded. */
  Thistory history;
};

/** \brief Linear equation.

  \remark \a equation->le and \a equation->comb are never combined.
   The variables used by them may have the same 'id', but this is not a problem
   since \a equation->comb does not use the variable properties. */
struct TSequation
{
  /* DC General properties */
  /*****************************/
  
  /** \brief Identification number of the constraint. */
  int id;
  /** \brief The linear equation, i.e., expression = 0. */
  Texp le;
  /** \brief The arithmetic combination that derived the current \a le. */
  Texp comb;
  /** \brief The user original linear equation. The user \a le is modified
     if a basic variable is created for transforming inequality in equality. */
  Texp user_le;
  
  
  /* DC Information that should be kept for faster 'searching' */
  /*************************************************************/
  
  /** \brief Points to the monomial where the basic variable is. */
  Tmon bmon;
  /** \brief List of monomials. Contains all the monomials where the equation
     appears. */
  Tlist lm;
};


/** \brief Disequality. */
struct TSdisequality
{
  /** \brief First variable ID of the disequality. Internal numeration is used. */
  Tvar_id var_id1;
  /** \brief Second variable ID of the disequality. Internal numeration is used. */
  Tvar_id var_id2;
  /** \brief ID that identifies the user constraint. */
  int id;
};


/** \brief Equality or model equality that may be created. */
struct TSequality
{
  /** \brief First variable ID of the equality. Internal numeration is used. */
  Tvar_id var_id1;
  /** \brief DC Second variable ID of the equality. Internal numeration is used. */
  Tvar_id var_id2;
};


/** \brief Expression.

   An expression is a sorted list of monomials
   where no variables appears twice and coefficients are different from zero.
   The constant term is always represented (it exists when zero) and is
   the first element in the list. */
struct TSexp
{
  /** \brief Type of the expression: created by the user or internal.
     Used to avoid updating links when manipulating expressions. */
  Texp_kind kind;
  /** \brief Sorted listed of monomials. */
  Tlist mons;
};

/** \brief Monomial. */
struct TSmon
{
  /** \brief Variable. If it is a constant: \a var->id == 0 */
  Tvar var;
  /** \brief Coefficient. */
  Tnumber coef;
  /** \brief Equation that the monomial is part of. */
  Tequation e;
};

/** \brief Variable. */
struct TSvar
{
  /** \brief Integer identification. */
  Tvar_id id;
};

/** \brief The properties a (user or slack) variable may have. The variables
   used in \a equation->comb has no such properties. */
struct TSvar_prop
{
  /* DC Value/bound properties */
  /*****************************/
  
  /** \brief Is it integer? */
  bool is_int;
  /** \brief Upper bound of the variable. */
  Tnumber upper;
  /** \brief Lower bound of the variable. */
  Tnumber lower;
  /** \brief Current value associated to the variable. */
  Tnumber value;
  /** \brief Explanation of the upper bound. */
  Texp exp_upper;
  /** \brief Explanation of the lower bound. */
  Texp exp_lower;
  /** \brief The id given by the user. If it is not given by the user then \a user_id = -1. */
  Tvar_id user_id;
  
  /* DC Useful information saved after using la_check_[in,de]crease_value() or la_update_sol()*/
  /**************************************************************************/
  
  /** \brief How much the variable can increase its value; direct or indirect;
     If \a inc is negative it means how much the variable can be decreased. */
  Tnumber inc;
  /** \brief Basic variable that may be limited by, NULL otherwise */
  Tvar var_lim;
  /** \brief How much the solution will increase if \a inc is applied.
     This value is saved for avoid recalculating. */
  Tnumber sol_inc;
  /** \brief Pointer to the goal monomial where the variable is. */
  Tmon goal_mon;
  
  
  /* DC Information that should be kept for faster 'searching' */
  /*************************************************************/
  
  /** \brief List of monomials. Contains all the monomials where the variable
     appears. Except for the goal equation. */
  Tlist lm;
  /** \brief If it is a basic variable, points to the constraint id, -1 otherwise.
     \a simplex->eq[basic] returns the equation where \a basic is the basic variable.  */
  Tsigned basic;
}; 


/*-----------------------------------------------------------------------*/
/* Local data                                                            */
/*-----------------------------------------------------------------------*/

/* DC simplex data */
static Tsimplex la_s;

/*-----------------------------------------------------------------------*/
/* List of local functions                                               */
/*-----------------------------------------------------------------------*/

#ifdef DEBUG_LA
static void          la_do_tests();
#endif

/* DC Goal and Solution value */
static Tnumber       la_goal_value(Tsimplex s);
static Tnumber       la_solution_value(Tsimplex s);
static void          la_update_sol(Tsimplex s);

/* DC Updating and pivot */
static void          la_update(Tsimplex s, Tvar v);
static void          la_pivot_and_update(Tsimplex s, Tvar enter_var, Tvar leave_var);
static void          la_increase_value(Tsimplex s, Tvar v);

/* DC Updating/pivoting selecting criteria */
static void          la_check_increasing_value(Tsimplex s, Tvar v);
static void          la_check_decreasing_value(Tsimplex s, Tvar v);
#if 0
static Tvar          la_get_var_to_maximize(Tsimplex s);
static Tvar          la_get_var_to_minimize(Tsimplex s);
#endif
static Tvar          la_get_var_to_maximize2(Tsimplex s);
static Tvar          la_get_var_to_minimize2(Tsimplex s);

/* DC Startup */
static bool          la_minimize (Tsimplex s);
static bool          la_reach (Tsimplex s);

/* DC Consistency */
static bool          la_adjust_model(Tsimplex s, int depth);
static bool          la_consistent (Tsimplex s);
static Tlist         la_colect_conflict_from_unreachable_goal(Tsimplex s);
static Tlist         la_colect_explanation_of_fixed_variables(Tsimplex s, Texp e);

/* DC Bounds */
static void          la_equation_check_bound(Tsimplex s, Tequation e);
static void          la_inequality_check_bound(Tsimplex s, Tequation e);
static void          la_update_lower_bound(Tsimplex s, Tequation e);
static void          la_update_upper_bound(Tsimplex s, Tequation e);

/* DC Equation */
static Tequation     la_equation_new(Tsimplex s, Tnumber coef[], Tvar_id var_id[], Tunsigned size);
static void          la_equation_free(Tsimplex s, Tequation e);
static void          la_equation_normalize(Tsimplex s, Tequation e);
static void          la_equation_add(Tsimplex s, Tequation e);
static void          la_inequality_add(Tsimplex s, Tequation e);
static void          la_equation_inc(Tsimplex s);
static int           la_equation_size(Tsimplex s);
static Tequation     la_equation_from_var(Tsimplex s, Tvar v);
static bool          la_equation_has_one_variable(Tequation e);

/* DC Disequality */
static Tdisequality  la_disequality_new(Tsimplex s, Tvar_id var_id1, Tvar_id var_id2);
static void          la_disequality_free(Tdisequality d);

/* DC equality */
static Tequality     la_equality_new(Tsimplex s, Tvar_id var_id1, Tvar_id var_id2);
static void          la_equality_free(Tequality e);
static void          la_search_model_equalities(Tsimplex s);
static int           la_equality_compare (Tequality a, Tequality b);

/* DC Expression */
static Texp          la_exp_new(Tsimplex s, Tnumber coef[], Tvar_id var_id[], Tunsigned size, Texp_kind ek, Tequation eq);
static Texp          la_exp_cpy(Texp e);
static void          la_exp_free(Texp e);
static void          la_exp_combine(Tsimplex s, Texp e1, Texp e2, Tnumber n1, Tnumber n2);
static bool          la_exp_has_int_solution(Texp le, Tsimplex s);
static void          la_exp_get_gcd_after_normalization(Texp le, Tnumber gcd, Tnumber mult, Tsimplex s);
static void          la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term(Texp le, Tnumber lcm, Tnumber cons, Tsimplex s);
static bool          la_exp_is_all_var_int(Texp le, Tsimplex s);
static void          la_exp_update_monomial_linking_list_of_its_variables(Texp le, Tsimplex s);
static void          la_exp_remove_unlinked_fixed_variables(Tequation e, Tsimplex s);
static void          la_exp_round_down_inequality_of_integers(Tequation e, Tsimplex s);

/* DC Variable properties */
static Tvar_prop     la_increase_properties(Tsimplex s, Tvar_id user_id, Tvar_kind var_type);
static void          la_var_prop_free(Tvar_prop vp);

/* DC Variable */
static Tvar          la_var_new(Tvar_id var_id);
static void          la_var_free(Tvar v);
static Tnumber       la_var_value(Tsimplex s, Tvar v);
static void          la_check_var(Tsimplex s, Tvar_id var_id[], Tvar_kind var_type[], Tunsigned size);
static bool          la_var_has_int_solution(Tvar_id var_id, Tsimplex s);

/* DC User variable identification */
static Tvar_id*      la_var_id_lookup(Tsimplex s, Tvar_id user_id);
static Tvar_id       la_var_id_recover(Tsimplex s, Tvar_id user_id);
static Tvar_id       la_var_id_register(Tsimplex s, Tvar_id user_id, Tvar_kind var_type);
static void          la_var_id_unregister(Tsimplex s, Tvar_id user_id);
static Tunsigned     la_var_id_register_count(Tsimplex s);
static void          la_var_id_init(Tsimplex s);
static void          la_var_id_reset(Tsimplex s);
static void          la_var_id_free(Tsimplex s);

/* DC Basic Variable */
static bool          la_var_is_basic(Tsimplex s, Tvar v);
static Tvar          la_get_basic_var(Tsimplex s, Tequation e);
static Tnumber       la_get_basic_coef(Tsimplex s, Tequation e);
static Tequation     la_get_basic_equation(Tsimplex s, Tvar bv);

/* DC Monomial */
static Tmon          la_mon_new(Tnumber coef, Tvar_id var_id, Tequation e);
static void          la_mon_free(Tmon m);
static bool          la_mon_less(Tmon a, Tmon b);
static Tmon          la_mon_get_best_to_become_basic_variable(Tsimplex s, Texp le);
static void          la_mon_combine_to_remove_from_equations(Tsimplex s, Tmon m, Tequation e);


/* DC Circular list auxiliary functions */
static void          la_list_add_mons(Tlist *res, Tlist lm);
static bool          la_list_mon_begin(Tlist l);
static bool          la_list_remove(Tlist *ptr, Tlist *begin);

/* DC Hash */
static unsigned      int_hash (int n);
static int           int_equal (void *a, void *b);

/* DC Comparing */
static int           compare_Tnumber_int_pair (const void *a, const void *b);

/*-----------------------------------------------------------------------*/
/* History stuff                                                         */
/*-----------------------------------------------------------------------*/

/** \brief What kind of events the module records. */
typedef enum
{ PROPERTIES_INCREASED, VARIABLE_ASSOCIATED, EQUATION_ADDED, 
  UPPER_BOUND_CHANGED, LOWER_BOUND_CHANGED, STATUS_CHANGED, DISEQUALITY_ADDED,
  EQUALITY_FOUND
} Tevent_kind;

/** \brief Indentifies a recorded event. */
struct TShistory
{
  void *data;
  int level;
  Tevent_kind kind;
  struct TShistory *next;
};

typedef struct TShistory_bound_changed
{
  Tvar_prop vp;
  Texp exp_bound;
  Tnumber n;
}*Thistory_bound_changed;

/*-----------------------------------------------------------------------*/

/* DC Records an increase in the variable properties */
static void
history_properties_increased (Tsimplex s)
{
  Thistory record;
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  /*printf("history_properties_increased()\n");*/
  record->kind = PROPERTIES_INCREASED;
  
  record->data = NULL;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC Returns to the previous state when a property have been increased */
static void
history_properties_increased_back (Tsimplex s)
{
  /*printf("history_properties_increased_back(), now there will be %d in the game\n", table_length(s->vp)-1);
  my_DAG_message("the removing variable is %d\n", ((Tvar_prop)table_top(s->vp))->user_id);*/
  la_var_prop_free((Tvar_prop)table_pop(s->vp));
}

/*-----------------------------------------------------------------------*/

/* DC Records a varible association */
static void
history_variable_associated (Tsimplex s, Tvar_id var_id)
{
  Thistory record;
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  record->kind = VARIABLE_ASSOCIATED;
  
  record->data = (void *) var_id;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC Returns to the previous state when a variable has been associated */
static void
history_variable_associated_back (Tsimplex s)
{
  Tvar_id var_id = (Tvar_id) s->history->data;
  la_var_id_unregister(s, var_id);
}

/*-----------------------------------------------------------------------*/

/* DC Records an equation insertion */
static void
history_equation_added (Tsimplex s)
{
  Thistory record;
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  /*printf("history_equation_added()\n");*/
  record->kind = EQUATION_ADDED;
  
  record->data = NULL;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when an equation has been added */
static void
history_equation_added_back (Tsimplex s)
{
  Tlist ptr;
  /* DC Equation to be removed */
  Tequation eq = (Tequation)table_pop(s->eq);
  /* DC Basic variable from the equation to be removed */
  Tvar eqbv;
  /* DC Monomial where we can find the variable related to 'eq' in 'eq' */
  Tmon eqm = NULL;

  /*printf("history_equation_added_back()\n");*/
  /*printf("removing (%d)", eq->id); la_exp_print(eq->user_le); printf(" from other equations\n");
  la_exp_print(eq->le); printf("\n"); la_exp_print(eq->comb); printf("\n");*/
  
  /* DC Search for the monomial where 'eq' is. */
  ptr = eq->lm;
  while (true)
    {
      Tmon m = ((Tmon)list_car(ptr));
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  la_list_remove(&ptr, &eq->lm);
	}
      else if (eq == m->e)
	{
	  eqm = m;
	  break;
	}
      else
	{
	  /* DC Swap equations 'm->e' and 'eq' */
	  Texp t;
	  Tmon t2;
	  Tsigned t3;
	  Tequation tme = m->e, teq = eq;
	  Tlist p, ini;

	  t3 = ((Tvar_prop)table_get(s->vp, la_get_basic_var (s, m->e)->id))->basic;
	  ((Tvar_prop)table_get(s->vp, la_get_basic_var (s, m->e)->id))->basic = ((Tvar_prop)table_get(s->vp, la_get_basic_var (s, eq)->id))->basic;
	  ((Tvar_prop)table_get(s->vp, la_get_basic_var (s, eq)->id))->basic = t3;
	  
	  p = ini = tme->le->mons;
	  do
	    {
	      Tmon t = list_car(p);
	      t->e = teq;
	      p = list_cdr(p);
	    }
	  while (p != ini);
	  p = ini = tme->comb->mons;
	  do
	    {
	      Tmon t = list_car(p);
	      t->e = teq;
	      p = list_cdr(p);
	    }
	  while (p != ini);
	  
	  p = ini = teq->le->mons;
	  do
	    {
	      Tmon t = list_car(p);
	      t->e = tme;
	      p = list_cdr(p);
	    }
	  while (p != ini);
	  p = ini = teq->comb->mons;
	  do
	    {
	      Tmon t = list_car(p);
	      t->e = tme;
	      p = list_cdr(p);
	    }
	  while (p != ini);
	  
	  t = teq->le;
	  teq->le = tme->le;
	  tme->le = t;
	  
	  t = teq->comb;
	  teq->comb = tme->comb;
	  tme->comb = t;
	  
	  t2 = teq->bmon;
	  teq->bmon = tme->bmon;
	  tme->bmon = t2;
	  
	  eqm = m;
	  break;
	}
    }
  
  /* DC Is there always a trace of 'eq' in itself? */
  assert(eqm != NULL);

  /* DC Remove the (traces of the) equation from the other constraints */
  ptr = eq->lm;
  do
    {
      Tmon m = ((Tmon)list_car(ptr));
      /*printf("examining "); la_exp_print(m->e->user_le); printf("\n");*/
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  ptr = list_cdr(ptr);
	}
      /* DC If the equation is itself then do nothing for now */
      else if (m->e->id < eq->id)
	{	    
	  Tnumber n = number_neg(number_cpy(number_new(), m->coef));
	  number_div(n, n, eqm->coef);
	  /*printf("adjusting "); la_exp_print(m->e->le); printf("\n");
	  printf("will multiply by %s (", number_to_str(n));
	  la_exp_print(eq->le); printf(")\n");*/
	  la_exp_combine(s, m->e->le, eq->le, number_one, n);
	  la_exp_combine(s, m->e->comb, eq->comb, number_one, n);
	  number_free(n);
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &eq->lm)) break;
	}
      else 
	ptr = list_cdr(ptr);
    }
  while (ptr != eq->lm);

  /* DC Reduce the number of basic variables */
  eqbv = la_get_basic_var(s, eq);
  if (eqbv != NULL && eqbv->id < la_var_id_register_count(s))
    {
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, eqbv->id);
      vp->basic = -1;
    }
 
  /*printf("about to remove (%d)", eq->id); la_exp_print(eq->user_le); printf(" from other equations\n");
  la_exp_print(eq->le); printf("\n"); la_exp_print(eq->comb); printf("\n");*/
  la_equation_free(s, eq);
  s->goal = NULL;
}

/*-----------------------------------------------------------------------*/

/* DC records a change of upper bound */
static void
history_upper_bound_changed (Tsimplex s, Tvar_prop vp)
{
  Thistory record;
  Thistory_bound_changed data;
  
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  MY_MALLOC (data, sizeof (struct TShistory_bound_changed));
  data->vp = vp;
  data->exp_bound = la_exp_cpy(vp->exp_upper);
  data->n = number_cpy(number_new(), vp->upper);
  
  record->kind = UPPER_BOUND_CHANGED;
  
  record->data = (void*)data;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when an upper bound has been changed */
static void
history_upper_bound_changed_back (Tsimplex s)
{
  Thistory_bound_changed data = (Thistory_bound_changed)s->history->data;
  number_cpy(data->vp->upper, data->n);
  number_free(data->n);
  la_exp_free(data->vp->exp_upper);
  data->vp->exp_upper = data->exp_bound;
  free(data);
}

/*-----------------------------------------------------------------------*/

/* DC records a change of lower bound */
static void
history_lower_bound_changed (Tsimplex s, Tvar_prop vp)
{
  Thistory record;
  Thistory_bound_changed data;
  
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  MY_MALLOC (data, sizeof (struct TShistory_bound_changed));
  data->vp = vp;
  data->exp_bound = la_exp_cpy(vp->exp_lower);
  data->n = number_cpy(number_new(), vp->lower);
  
  record->kind = LOWER_BOUND_CHANGED;
  
  record->data = (void*)data;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when an lower bound has been changed */
static void
history_lower_bound_changed_back (Tsimplex s)
{
  Thistory_bound_changed data = (Thistory_bound_changed)s->history->data;
  number_cpy(data->vp->lower, data->n);
  number_free(data->n);
  la_exp_free(data->vp->exp_lower);
  data->vp->exp_lower = data->exp_bound;
  free(data);
}

/*-----------------------------------------------------------------------*/

/* DC records a change of status */
static void
history_status_changed (Tsimplex s)
{
  Thistory record;
  
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  record->kind = STATUS_CHANGED;
  
  record->data = (void*)s->consistent;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when the status has been changed */
static void
history_status_changed_back (Tsimplex s)
{
  s->consistent = (bool)s->history->data;
  list_free(&s->conflict);
  s->conflict = NULL;
}

/*-----------------------------------------------------------------------*/

/* DC records an disequality insertion */
static void
history_disequality_added (Tsimplex s)
{
  Thistory record;
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  record->kind = DISEQUALITY_ADDED;
  
  record->data = NULL;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when a disequality inserted */
static void
history_disequality_added_back (Tsimplex s)
{
  table_pop(s->eq);
  la_disequality_free((Tdisequality)table_pop(s->disequalities));
}

/*-----------------------------------------------------------------------*/

/* DC records an equality 'discovery' */
static void
history_equality_found (Tsimplex s, Tequality e)
{
  Thistory record;
  MY_MALLOC (record, sizeof (struct TShistory));
  record->level = s->level;
  
  record->kind = EQUALITY_FOUND;
  
  record->data = e;
  record->next = s->history;
  s->history = record;
}

/*-----------------------------------------------------------------------*/

/* DC returns to the previous state when a equality has been found */
static void
history_equality_found_back (Tsimplex s)
{
  Tequality e = (Tequality)s->history->data;
  set_remove(s->returned_eq, e);
  la_equality_free(e);
}

/*-----------------------------------------------------------------------*/

/* DC goes back in time restoring the status */
static void
history_backtrack (Tsimplex s)
{
  while (s->history != NULL && s->history->level > s->level)
    {
      Thistory tmp;
      switch (s->history->kind)
	{
	  case PROPERTIES_INCREASED:
	    history_properties_increased_back (s);
	    break;
	  case VARIABLE_ASSOCIATED:
	    history_variable_associated_back (s);
	    break;
	  case EQUATION_ADDED:
	    history_equation_added_back (s);
	    break;
	  case UPPER_BOUND_CHANGED:
	    history_upper_bound_changed_back (s);
	    break;
	  case LOWER_BOUND_CHANGED:
	    history_lower_bound_changed_back (s);
	    break;
	  case STATUS_CHANGED:
	    history_status_changed_back (s);
	    break;
	  case DISEQUALITY_ADDED:
	    history_disequality_added_back (s);
	    break;
	  case EQUALITY_FOUND:
	    history_equality_found_back (s);
	    break;
	  default:
	    assert (0);
	}
      tmp = s->history->next;
      free (s->history);
      s->history = tmp;
    }
}

/*-----------------------------------------------------------------------*/

/* DC initializes history */
static void
history_init (Tsimplex s)
{
  s->history = NULL;
}

/*-----------------------------------------------------------------------*/

/* DC resets history */
static void
history_reset (Tsimplex s)
{
  int t = s->level;
  s->level = -1;
  history_backtrack(s);
  s->level = t;
  /*while (s->history != NULL)
    {
      Thistory tmp = s->history->next;
      free (s->history->data);
      free (s->history);
      s->history = tmp;
    }*/
}

/*-----------------------------------------------------------------------*/

/* DC finalizes history */
static void
history_done (Tsimplex s)
{
  history_reset (s);
}

/*-----------------------------------------------------------------------*/
/* Local functions                                                       */
/*-----------------------------------------------------------------------*/


#if defined(DEBUG_LA) || defined(PRINT_LA)
#include "la-print.c.include"
#endif

/*-----------------------------------------------------------------------*/

/*-----------------------------------------------------------------------*/

#ifdef DEBUG_LA

/*#include "la-test1.c.include"
#include "la-test2.c.include"
#include "la-test3.c.include"
#include "la-test4.c.include"
#include "la-test5.c.include"
#include "la-test6.c.include"
#include "la-test7.c.include"
#include "la-test8.c.include"
#include "la-test9.c.include"
#include "la-test10.c.include"
#include "la-test11.c.include"*/

/* DC Some tests performed */
static void
la_do_tests()
{
  /*la_do_test1();
  la_do_test2();
  la_do_test3();
  la_do_test4();
  la_do_test5();
  la_do_test6();
  la_do_test7();
  la_do_test8();
  la_do_test9();
  la_do_test10();
  la_do_test11();*/
}
#endif

/*-----------------------------------------------------------------------*/

/* DC Gets the value to reach from the goal */
static Tnumber
la_goal_value(Tsimplex s)
{
  /*return ((Tmon)list_car(s->goal->le->mons))->coef;*/
  return number_zero;
}

/*-----------------------------------------------------------------------*/

/* DC Returns the current value of the solution */
static Tnumber
la_solution_value(Tsimplex s)
{
  return s->sol;
}

/*-----------------------------------------------------------------------*/

/* DC Updates the solution value according to the goal. Should be used
   when the goal equation is changed during 'la_push()'. */
static void
la_update_sol(Tsimplex s)
{
  Tlist ptr;
  Tnumber n = number_new();
  number_cpy(s->sol, number_zero);
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_update_sol()\n");
#endif
  
  /* DC For each variable in the goal */
  ptr = list_cdr(s->goal->le->mons);
  if (ptr != s->goal->le->mons)
    do
      {
        /* DC Add to the solution 'coef' * 'value' */
        Tmon m = list_car(ptr);
        Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);

        number_mul(n, m->coef, vp->value);
        number_add(s->sol, s->sol, n);
	
	/* DC Save the pointer to the goal monomial for avoiding to search */
	vp->goal_mon = m;
      
        ptr = list_cdr(ptr);
      }
    while (ptr != s->goal->le->mons);
  number_add(s->sol, s->sol, ((Tmon)list_car(ptr))->coef);
  
  number_free(n);
}

/*-----------------------------------------------------------------------*/

/* DC Updates the value of 'v', changing also the value of all the 
   basic variables that depends of 'v'.
   The value of 'v' is changed by adding 'vp->inc' ('vp->inc' can be negative) */
static void
la_update(Tsimplex s, Tvar v)
{
  Tlist ptr;
  Tvar_prop vp = (Tvar_prop)table_get(s->vp, v->id);
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_update()\n");
#endif
  
  /* DC For each equation that contains 'v' */
  ptr = vp->lm;
  while (ptr != NULL)
    {
      Tmon m = (Tmon)list_car(ptr);
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &vp->lm)) break;
	}
      else
	{
	  /* DC Change value of the basic variable */
	  Tvar bv = la_get_basic_var(s, m->e);
	  Tnumber vbv = la_var_value(s, bv);
	  Tnumber n = number_new();
	  
	  number_div(n, m->coef, la_get_basic_coef(s, m->e));
	  number_mul(n, vp->inc, n);
	  number_neg(n);
	  number_add(vbv, vbv, n);
	  number_free(n);
	  
	  ptr = list_cdr(ptr);
	  if (ptr == vp->lm)
	    break;
	}
    }
  number_add(vp->value, vp->value, vp->inc);
  number_add(s->sol, s->sol, vp->sol_inc);
}

/*-----------------------------------------------------------------------*/

/* DC Updates the value of 'enter_var', pivots it with 'leave_var' and
   changes also the value of all the basic variables that depends of them */
static void
la_pivot_and_update(Tsimplex s, Tvar enter_var, Tvar leave_var)
{
  /* DC List 'iterator' */
  Tlist ptr;
  /* DC Properties of the entering variable */
  Tvar_prop evp = (Tvar_prop)table_get(s->vp, enter_var->id);
  /* DC Properties of the leaving variable */
  Tvar_prop lvp = (Tvar_prop)table_get(s->vp, leave_var->id);
  /* DC Equation of the leaving variable */
  Tequation le = la_get_basic_equation(s, leave_var);
  /* DC Monomial of the entering variable in the equation where 'leave_var' is basic */
  Tmon em = NULL;
  Tnumber tmp = number_new();
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_pivot_and_update()\n");
#endif
  
  /* DC Update */
    
  /* DC For each equation that contains 'enter_var' */
  ptr = evp->lm;
  while (evp->lm != NULL)
    {
      Tmon m = (Tmon)list_car(ptr);
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &evp->lm)) break;
	}
      else if (!number_equal(evp->inc, number_zero))
	{
	  /* DC Change value of the basic variable */
	  Tvar bv = la_get_basic_var(s, m->e);
	  Tnumber vbv = la_var_value(s, bv);
	  Tnumber n = number_new();
	  
	  number_div(n, m->coef, la_get_basic_coef(s, m->e));
	  number_mul(n, evp->inc, n);
	  number_sub(vbv, vbv, n);
	  number_free(n);
	  
	  if (m->e == le)
	    em = m;
	  
	  ptr = list_cdr(ptr);
	  if (ptr == evp->lm)
	    break;
	}
      else
	{
	  /* DC Look for 'em' */
	  if (m->e == le)
	    {
	      em = m;
	      break;
	    }

	  ptr = list_cdr(ptr);
	  if (ptr == evp->lm)
	    break;
	}      
    }
  number_add(evp->value, evp->value, evp->inc);
  number_add(s->sol, s->sol, evp->sol_inc);
  
  /* DC Pivot */
  
  /* DC For each equation 'm->e' that contains 'enter_var' */
  if (evp->lm != NULL)
    {
      ptr = evp->lm;
      while (ptr != NULL)
	{
	  Tmon m = (Tmon)list_car(ptr);
	  if (number_equal(m->coef, number_zero))
	  {
	    /* DC Update equation linking list */
	    la_mon_free(m);
	    if (la_list_remove(&ptr, &evp->lm)) break;
	  }
	  else if (m->e != le)
	    {
	      /* DC Modify 'm->e': remove 'enter_var' from 'm->e->le' by combining it with 'le->le' */
	      number_cpy(tmp, m->coef);
	      number_neg(tmp);
	      number_div(tmp, tmp, em->coef);

	      la_exp_combine(s, m->e->le, le->le, number_one, tmp);
	      la_exp_combine(s, m->e->comb, le->comb, number_one, tmp);
	      la_mon_free(m);
	      if (la_list_remove(&ptr, &evp->lm)) break;
	    }
	  else
	    {
	      ptr = list_cdr(ptr);
	      if (ptr == evp->lm)
		break;
	    }
	    /*ptr = list_cdr(ptr);*/
	}
      /*while (list_cdr(ptr) != ptr)      ;*/
    }
  
  /* DC Remove 'enter_var' from the goal */
  number_cpy(tmp, evp->goal_mon->coef);
  number_neg(tmp);
  number_div(tmp, tmp, em->coef);
  la_exp_combine(s, s->goal->le, le->le, number_one, tmp);
  la_exp_combine(s, s->goal->comb, le->comb, number_one, tmp);
  
  /* DC Swap basic and non-basic variable */
  evp->basic = lvp->basic;
  lvp->basic = -1;
  em->e->bmon = em;
  
  number_free(tmp);
}

/*-----------------------------------------------------------------------*/

/* DC Changes the value of the 'v' doing a pivot only if necessary */
static void
la_increase_value(Tsimplex s, Tvar v)
{
  Tvar_prop vp = (Tvar_prop)table_get(s->vp, v->id);
  if (vp->var_lim == NULL)
    la_update(s, v);
  else
    la_pivot_and_update(s, v, vp->var_lim);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
#endif
}

/*-----------------------------------------------------------------------*/

/* DC Checks for how much the variable 'v' can be increased. 
   Checks for indirect bounds by verifying all the constraints that contains 'v'.
   The maximum value the variable can increase, and if this is directly limited
   or not, is saved in the variable properties. */
static void
la_check_increasing_value(Tsimplex s, Tvar v)
{
  Tlist ptr;
  Tvar_prop vp;
  Tnumber tmp = number_new();
  
  vp = ((Tvar_prop)table_get(s->vp, v->id));
  
  /* DC Initially 'v' is directly limited */
  vp->var_lim = NULL;
  number_sub(vp->inc, vp->upper, vp->value);

#ifdef DEBUG_LA
  fprintf(stderr, "  => x%d is directly limited by %s\n", v->id, number_to_str(vp->inc));
#endif
  
  /* DC For each equation that contains 'v' do search for indirect limit */
  ptr = vp->lm;
  while (ptr != NULL)
    {
      Tmon m = (Tmon)list_car(ptr);
      
      if (number_equal(vp->inc, number_zero))
	break;
      
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &vp->lm)) break;
	}
      else
	{
	  Tvar bv = la_get_basic_var(s, m->e);
	  Tvar_prop vpbv = ((Tvar_prop)table_get(s->vp, bv->id));
	  Tnumber cbv = la_get_basic_coef(s, m->e);
	  
	  /* DC Same sign or opposite */
	  if (number_less(cbv, number_zero) == number_less(m->coef, number_zero))
	    number_sub(tmp, vpbv->value, vpbv->lower);
	  else
	    number_sub(tmp, vpbv->value, vpbv->upper);
	  number_mul(tmp, tmp, cbv);
	  number_div(tmp, tmp, m->coef);
  #ifdef DEBUG_LA
	  fprintf(stderr, "  => x%d is indirectly limited by %s (BV = x%d)\n", v->id, number_to_str(tmp), bv->id);
  #endif
	  if (number_less(tmp, vp->inc))
	    {
	      number_cpy(vp->inc, tmp);
	      vp->var_lim = bv;
	    }
      
	  ptr = list_cdr(ptr);
	  if (ptr == vp->lm)
	    break;
	}
    }

  number_free(tmp);
#ifdef DEBUG_LA
  fprintf(stderr, "  -> x%d can increase by %s\n", v->id, number_to_str(vp->inc));
#endif
}

/*-----------------------------------------------------------------------*/

/* DC Checks for how much the variable 'v' can be decreased. 
   Checks for indirect bounds by verifying all the constraints that contains 'v'.
   The maximum value the variable can decrease, and if this is directly limited
   or not, is saved in the variable properties. */
static void
la_check_decreasing_value(Tsimplex s, Tvar v)
{
  Tlist ptr;
  Tvar_prop vp;
  Tnumber tmp = number_new();
  
  vp = ((Tvar_prop)table_get(s->vp, v->id));
  
  /* DC Initially 'v' is directly limited */
  vp->var_lim = NULL;
  number_sub(vp->inc, vp->lower, vp->value);
  
#ifdef DEBUG_LA
  fprintf(stderr, "  => x%d is directly limited by %s\n", v->id, number_to_str(vp->inc));
#endif
  
  /* DC For each equation that contains 'v' do search for indirect limit */
  ptr = vp->lm;
  while (ptr != NULL)
    {
      Tmon m = (Tmon)list_car(ptr);
      
      if (number_equal(vp->inc, number_zero))
	break;
      
      if (number_equal(m->coef, number_zero))
	{
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &vp->lm)) break;
	}
      else
	{
	  Tvar bv = la_get_basic_var(s, m->e);
	  Tvar_prop vpbv = ((Tvar_prop)table_get(s->vp, bv->id));
	  Tnumber cbv = la_get_basic_coef(s, m->e);

	  /* DC Same sign or opposite */
	  if (number_less(cbv, number_zero) == number_less(m->coef, number_zero))
	    number_sub(tmp, vpbv->value, vpbv->upper);
	  else
	    number_sub(tmp, vpbv->value, vpbv->lower);
	  number_mul(tmp, tmp, cbv);
	  number_div(tmp, tmp, m->coef);
#ifdef DEBUG_LA
	  fprintf(stderr, "  => x%d is indirectly limited by %s (BV = x%d)\n", v->id, number_to_str(tmp), bv->id);
#endif
	  if (number_less(vp->inc, tmp))
	    {
	      number_cpy(vp->inc, tmp);
	      vp->var_lim = bv;
	    }
	  
	  ptr = list_cdr(ptr);
	  if (ptr == vp->lm)
	    break;
	}
    }

  number_free(tmp);
#ifdef DEBUG_LA
  fprintf(stderr, "  -> x%d can increase by %s\n", v->id, number_to_str(vp->inc));
#endif
}

/*-----------------------------------------------------------------------*/

#if 0
/* DC Returns a variable to maximize. Performs a search and returns the
   variable that will mostly maximize the goal, NULL if the current
   solution cannot be maximized. If it can maximize more than the goal value,
   it will do just enough to reaching it.

   The search is quadratic meaning that for each variable in the goal it will
   perform a search in each equation that contains this variable to
   determine the value of the indirect bound.
   */
static Tvar
la_get_var_to_maximize(Tsimplex s)
{
  Texp e = s->goal->le;
  Tlist lmon; /* DC 'iterator' list of monomials */
  Tvar rvar = NULL; /* DC Returning variable */
  Tnumber bsol_inc = number_zero; /* DC Best increase of the solution */
  Tnumber sol_inc = number_new(); /* DC How much the solution will increase */
  Tnumber goal_dif = number_new(); /* DC How much the solution can increase */
  
  number_sub(goal_dif, la_goal_value(s), la_solution_value(s));
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_get_var_to_maximize()\n");
#endif
  
  /* DC For each variable v in the goal */
  lmon = list_cdr(e->mons);
  if (lmon != e->mons)
    do
      {
        Tmon m = list_car(lmon);
	
        Tvar v = m->var;
        Tvar_prop vp = (Tvar_prop)table_get(s->vp, v->id);
        /* DC Positive or negative coefficient */
        if (number_less(number_zero, m->coef))
          la_check_increasing_value(s, v);
        else
	  la_check_decreasing_value(s, v);

        number_mul(sol_inc, m->coef, vp->inc);
        /* DC If the increasing value will go over than the 'goal value' */
        if (number_greater(sol_inc, goal_dif))
          {
            /* DC Reduce the increasing for just reaching the 'goal value' */
            number_div(vp->inc, goal_dif, m->coef);
            number_cpy(vp->sol_inc, goal_dif);
            bsol_inc = vp->sol_inc;
            rvar = v;
#ifdef DEBUG_LA
	    fprintf(stderr, "  -> x%d will be 'increased' only by %s\n", v->id, number_to_str(vp->inc));
#endif
	    break;
          }
	/* DC if 'v' will increase more the solution */
        else if (number_less(bsol_inc, sol_inc))
          {
            number_cpy(vp->sol_inc, sol_inc);
            bsol_inc = vp->sol_inc;
            rvar = v;
          }
	/* DC if the solution cannot be increased but a pivot can be done */
	else if (rvar == NULL && number_equal(sol_inc, number_zero) && vp->var_lim != NULL)
	  {
	    number_cpy(vp->sol_inc, sol_inc);
            bsol_inc = vp->sol_inc;
            rvar = v;
	  }

        /* DC Just get the first variable that can have any improvement */
        /*if (!number_equal(sol_inc, number_zero))
                  break;*/

        lmon = list_cdr(lmon);
      }
    while (lmon != e->mons);

#ifdef DEBUG_LA  
  if (rvar != NULL)
    fprintf(stderr, "la_get_var_to_maximize(): x%d picked\n", rvar->id);
  else
    fprintf(stderr, "la_get_var_to_maximize(): NONE picked\n");
#endif 
  
  number_free(sol_inc);
  number_free(goal_dif);
    
  return rvar;
}
#endif
/*-----------------------------------------------------------------------*/

#if 0
/* DC Returns a variable to minimize. Performs a search and returns the
   variable that will mostly minimize the goal, NULL if the current
   solution cannot be maximized. If it can minimize more than the goal value,
   it will do just enough to reaching it.

   The search is quadratic meaning that for each variable in the goal it will
   perform a search in each equation that contains this variable to
   determine the value of the indirect bound.
   */
static Tvar
la_get_var_to_minimize(Tsimplex s)
{
  Tlist lmon; /* DC 'iterator' list of monomials */
  Tvar rvar = NULL; /* DC Returning variable */
  Tnumber bsol_inc = number_zero; /* DC Best decrease of the solution */
  Tnumber sol_inc = number_new(); /* DC How much the solution will decrease */
  Tnumber goal_dif = number_new(); /* DC How much the solution can decrease */
  
  number_sub(goal_dif, la_goal_value(s), la_solution_value(s));
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_get_var_to_minimize()\n");
#endif
  
  /* DC For each variable v in the goal */
  lmon = list_cdr(s->goal->le->mons);
  if (lmon != s->goal->le->mons)
    do
      {
        Tmon m = list_car(lmon);
	
        Tvar v = m->var;
        Tvar_prop vp = (Tvar_prop)table_get(s->vp, v->id);
        /* DC Positive or negative coefficient */
        if (number_less(number_zero, m->coef))
          la_check_decreasing_value(s, v);
        else
	  la_check_increasing_value(s, v);

        number_mul(sol_inc, m->coef, vp->inc);
        /* DC If the increasing value will go over than the 'goal value' */
        if (number_greater(goal_dif, sol_inc))
          {
            /* DC Reduce the increasing for just reaching the 'goal value' */
            number_div(vp->inc, goal_dif, m->coef);
            number_cpy(vp->sol_inc, goal_dif);
            bsol_inc = vp->sol_inc;
            rvar = v;
#ifdef DEBUG_LA
	    fprintf(stderr, "  -> x%d will be 'increased' only by %s\n", v->id, number_to_str(vp->inc));
#endif
	    break;
          }
        else if (number_less(sol_inc, bsol_inc))
          {
            number_cpy(vp->sol_inc, sol_inc);
            bsol_inc = vp->sol_inc;
            rvar = v;
          }
	/* DC if the solution cannot be increased but a pivot can be done */
	else if (rvar == NULL && number_equal(sol_inc, number_zero) && vp->var_lim != NULL)
	  {
	    number_cpy(vp->sol_inc, sol_inc);
            bsol_inc = vp->sol_inc;
            rvar = v;
	  }

        /* DC Just get the first variable that can have any improvement */
        /*if (!number_equal(sol_inc, number_zero))
          break;*/

        lmon = list_cdr(lmon);
      }
    while (lmon != s->goal->le->mons);

#ifdef DEBUG_LA
  if (rvar != NULL)
    fprintf(stderr, "la_get_var_to_minimize(): x%d picked\n", rvar->id);
  else
    fprintf(stderr, "la_get_var_to_minimize(): NONE picked\n");
#endif
  
  number_free(sol_inc);
  number_free(goal_dif);
    
  return rvar;
}
#endif
/*-----------------------------------------------------------------------*/

/* DC Returns a variable to maximize. Performs a search and returns the
   variable that will mostly maximize the goal, NULL if the current
   solution cannot be maximized. If it can maximize more than the goal value,
   it will do just enough to reaching it.

   This is a second maximization strategy. It is linear instead of
   quadratic as in the first strategy.

   In this strategy we look for the variable that has the most potential to
   maximize the goal by looking only at the direct limits. Once chose,
   we calculate the real (indirect) bound only of this variable.

   TODO: Not enough experimenting was performed to determine if this second
   strategy is better than the first one.
   */
static Tvar
la_get_var_to_maximize2(Tsimplex s)
{
  Tlist lmon; /* DC 'iterator' list of monomials */
  Tvar rvar = NULL; /* DC Returning variable */
  Tmon rmon = NULL; /* DC Pointer to the returning monomial */
  Tnumber bsol_inc = number_cpy(number_new(), number_zero); /* DC Best increase of the solution */
  Tnumber var_inc = number_new(); /* DC How much a variable can increase the solution value */
  Tnumber sol_inc = number_new(); /* DC How much the solution will increase */
  Tnumber goal_dif = number_new(); /* DC How much the solution can increase */
  Tvar_prop vp;

  number_sub(goal_dif, la_goal_value(s), la_solution_value(s));

#ifdef DEBUG_LA
  fprintf(stderr, "la_get_var_to_maximize2()\n");
#endif

  /* DC For each variable v in the goal */
  lmon = list_cdr(s->goal->le->mons);
  if (lmon != s->goal->le->mons)
    do
      {
        Tmon m = list_car(lmon);

        Tvar v = m->var;
        vp = (Tvar_prop)table_get(s->vp, v->id);

        /* DC Positive or negative coefficient */
        if (number_less(number_zero, m->coef))
          number_mul(var_inc, number_sub(var_inc, vp->upper, vp->value), m->coef);
        else
          number_mul(var_inc, number_sub(var_inc, vp->lower, vp->value), m->coef);

        /* DC Keep the one with potentially best increase value */
        if (number_greater(var_inc, bsol_inc))
          {
	    rvar = v;
	    rmon = m;
	    number_cpy(bsol_inc, var_inc);
          }
        lmon = list_cdr(lmon);
      }
    while (lmon != s->goal->le->mons);

  /* DC If any of the variables can increase its value */
  if (rvar != NULL)
    {
      vp = (Tvar_prop)table_get(s->vp, rvar->id);
      /* DC Positive or negative coefficient */
      if (number_less(number_zero, rmon->coef))
	la_check_increasing_value(s, rvar);
      else
	la_check_decreasing_value(s, rvar);

      number_mul(sol_inc, rmon->coef, vp->inc);

      /* DC If the increasing value will go over than the 'goal value' */
      if (number_greater(sol_inc, goal_dif))
	{
	  /* DC Reduce the increasing for just reaching the 'goal value' */
	  number_div(vp->inc, goal_dif, rmon->coef);
	  number_cpy(vp->sol_inc, goal_dif);
#ifdef DEBUG_LA
	  fprintf(stderr, "  -> x%d will be 'increased' only by %s\n", rvar->id, number_to_str(vp->inc));
#endif
	}
      else
	number_cpy(vp->sol_inc, sol_inc);
    }
  /* DC ELSE: it means that all variables are directly limited and therefore
   * no maximization can be done and the problem should stop.
   */


#ifdef DEBUG_LA
  if (rvar != NULL)
    fprintf(stderr, "la_get_var_to_maximize2(): x%d picked\n", rvar->id);
  else
    fprintf(stderr, "la_get_var_to_maximize2(): NONE picked\n");
#endif

  number_free(sol_inc);
  number_free(goal_dif);
  number_free(bsol_inc);
  number_free(var_inc);

  return rvar;
}

/*-----------------------------------------------------------------------*/

/* DC Returns a variable to minimize. Performs a search and returns the
   variable that will mostly minimize the goal, NULL if the current
   solution cannot be maximized. If it can minimize more than the goal value,
   it will do just enough to reaching it.

   This is a second minimization strategy. It is linear instead of
   quadratic as in the first strategy.

   In this strategy we look for the variable that has the most potential to
   minimize the goal by looking only at the direct limits. Once chose,
   we calculate the real (indirect) bound only of this variable.

   TODO: Not enough experimenting was performed to determine if this second
   strategy is better than the first one.
   */
static Tvar
la_get_var_to_minimize2(Tsimplex s)
{
  Tlist lmon; /* DC 'iterator' list of monomials */
  Tvar rvar = NULL; /* DC Returning variable */
  Tmon rmon = NULL; /* DC Pointer to the returning monomial */
  Tnumber bsol_inc = number_cpy(number_new(), number_zero); /* DC Best decrease of the solution */
  Tnumber var_inc = number_new(); /* DC How much a variable can decrease the solution value */
  Tnumber sol_inc = number_new(); /* DC How much the solution will decrease */
  Tnumber goal_dif = number_new(); /* DC How much the solution can decrease */
  Tvar_prop vp;

  number_sub(goal_dif, la_goal_value(s), la_solution_value(s));

#ifdef DEBUG_LA
  fprintf(stderr, "la_get_var_to_minimize2()\n");
#endif

  /* DC For each variable v in the goal */
  lmon = list_cdr(s->goal->le->mons);
  if (lmon != s->goal->le->mons)
    do
      {
        Tmon m = list_car(lmon);

        Tvar v = m->var;
        vp = (Tvar_prop)table_get(s->vp, v->id);

        /* DC Positive or negative coefficient */
        if (number_less(number_zero, m->coef))
          number_mul(var_inc, number_sub(var_inc, vp->lower, vp->value), m->coef);
        else
          number_mul(var_inc, number_sub(var_inc, vp->upper, vp->value), m->coef);

        /* DC Keep the one with potentially best decrease value */
        if (number_less(var_inc, bsol_inc))
          {
	    rvar = v;
	    rmon = m;
	    number_cpy(bsol_inc, var_inc);
          }
        lmon = list_cdr(lmon);
      }
    while (lmon != s->goal->le->mons);

  /* DC If any of the variables can decrease its value */
  if (rvar != NULL)
    {
      vp = (Tvar_prop)table_get(s->vp, rvar->id);
      /* DC Positive or negative coefficient */
      if (number_less(number_zero, rmon->coef))
	la_check_decreasing_value(s, rvar);
      else
	la_check_increasing_value(s, rvar);

      number_mul(sol_inc, rmon->coef, vp->inc);

      /* DC If the increasing value will go over than the 'goal value' */
      if (number_greater(goal_dif, sol_inc))
	{
	  /* DC Reduce the increasing for just reaching the 'goal value' */
	  number_div(vp->inc, goal_dif, rmon->coef);
	  number_cpy(vp->sol_inc, goal_dif);
  #ifdef DEBUG_LA
	  fprintf(stderr, "  -> x%d will be 'increased' only by %s\n", rvar->id, number_to_str(vp->inc));
  #endif
	}
      else
	number_cpy(vp->sol_inc, sol_inc);
    }
  /* DC ELSE: it means that all variables are directly limited and therefore
   * no minimization can be done and the problem should stop.
   */


#ifdef DEBUG_LA
  if (rvar != NULL)
    fprintf(stderr, "la_get_var_to_minimize2(): x%d picked\n", rvar->id);
  else
    fprintf(stderr, "la_get_var_to_minimize2(): NONE picked\n");
#endif

  number_free(sol_inc);
  number_free(goal_dif);
  number_free(bsol_inc);
  number_free(var_inc);

  return rvar;
}

/*-----------------------------------------------------------------------*/

/* DC Tries to reach the goal, decreasing the value of the goal function.
   Returns true if successful. */
static bool
la_minimize(Tsimplex s)
{

  /*  int counter = 0; */
#ifdef DEBUG_LA
  fprintf(stderr, "la_minimize()\n");
#endif
  
  /* DC While did not reach the goal */
  while (number_greater(la_solution_value(s), la_goal_value(s)) )
    {
      Tvar inc_var = la_get_var_to_minimize2(s);
      /*printf("Minimize loop (counter = %d)\n", ++counter);*/
      /*printf("Solution is %s, goal is %s\n", number_to_str(la_solution_value(s)), number_to_str(la_goal_value(s)));
      printf("inc_var = %d\n", inc_var == NULL ? 0 : inc_var->id);*/
      /* DC If cannot maximize anymore then stop */
      if (inc_var == NULL)
	{
	  history_status_changed(s);
	  s->conflict = la_colect_conflict_from_unreachable_goal(s);
	  return (s->consistent = false);
	}
      la_increase_value(s, inc_var);
    } 
  return true;
}

/*-----------------------------------------------------------------------*/

/* DC Tries to reach the goal . Returns true if successful. */
static bool
la_reach(Tsimplex s)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_reach()\n");
#endif
  
  /* DC While did not reach the goal */
  while (!number_equal(la_solution_value(s), la_goal_value(s)) )
    {
      Tvar inc_var;
      if (number_less(la_solution_value(s), la_goal_value(s)))
	inc_var = la_get_var_to_maximize2(s);
      else
	inc_var = la_get_var_to_minimize2(s);
      /* DC If cannot maximize anymore then stop */
      if (inc_var == NULL)
	{
	  history_status_changed(s);
	  s->conflict = la_colect_conflict_from_unreachable_goal(s);
	  return (s->consistent = false);
	}
      la_increase_value(s, inc_var);
    }
  return true;
}

/*-----------------------------------------------------------------------*/

/* DC Checks if there are integer variables in the model with rational values.
   If so, try to change the model using branch-and-cut techniques.
 
   This function calls the function 'la_solve', and 'la_solve' calls
   'la_adjust_model', so it works as a recursive function in Depth-first 
   search (DFS).
   It pushes new inequalities and eventually pops them, and when poping the 
   value of the variables is preserved due to the nature of the decision 
   procedure.
 */
static bool
la_adjust_model(Tsimplex s, int depth)
{
  Tunsigned i;
  Tunsigned size = table_length(s->vp);
  if (s->consistent == false)
    return false;
  if (s->cannot_find_solution)
    return false;
  
#ifdef DEBUG_LA
  printf("la_adjust_model(depth = %d)\n", depth);
#endif
    
  if (depth >= 1000)
    {
      /*my_error("Arithmetic loop in the branch and bound!\n");*/
      s->cannot_find_solution = true;
      return false;
    }
        
  /* DC No plane cuts is possible, try branch and bound */
  
  for (i = 1; i < size; ++i)
    {
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, i);
      if (vp->is_int && !number_is_int(vp->value))
        {
	  Tnumber c[2], first_try, second_try;
	  Tvar_id v[2] = {0, vp->user_id};
	  Tvar_kind k[2] = {LA_RATIONAL, LA_INT};
	  
	  if (!la_var_has_int_solution(i, s))
            return false;
	  
	  first_try = number_neg(number_floor(number_cpy(number_new(), vp->value)));
	  second_try = number_ceil(number_cpy(number_new(), vp->value));
	  
#ifdef DEBUG_LA
	  printf("la_adjust_model(): Branch and Bound: x%d cannot have value %s\n", i, number_to_str(vp->value));
#endif
	  c[1] = number_cpy(number_new(), number_one);
	  c[0] = first_try;
#ifdef DEBUG_LA
	  printf("la_adjust_model(depth = %d): Trying first x%d + %s <= 0\n", depth, i, number_to_str(c[0]));
	  printf("c = {%s, %s}, v = {%d, %d}, user_id = %d\n", number_to_str(c[0]), number_to_str(c[1]), v[0], v[1], vp->user_id);
#endif
	  la_push_inequality(c, v, k, 2);
	  if (s->consistent && la_adjust_model(s, depth+1))
	      la_pop();
          else
	    {
	      la_pop();
	      number_neg(c[1]);
	      c[0] = second_try;
	      v[1] = vp->user_id;
#ifdef DEBUG_LA
	      printf("la_adjust_model(depth = %d): Trying second -x%d + %s <= 0\n", depth, i, number_to_str(c[0]));
	      printf("c = {%s, %s}, v = {%d, %d}, user_id = %d\n", number_to_str(c[0]), number_to_str(c[1]), v[0], v[1], vp->user_id);
#endif
	      la_push_inequality(c, v, k, 2);
	      if (s->consistent && la_adjust_model(s, depth+1))
	        la_pop();
	      else
		{
		  la_pop();
		  number_free(c[1]);
	          number_free(first_try);
		  number_free(second_try);
		  return false;
		}
	    }
	  number_free(c[1]);
	  number_free(first_try);
	  number_free(second_try);
	  return true;
	}
    }
  return true;
}


/*-----------------------------------------------------------------------*/

/* DC Returns true if the current status is consistent */
static bool
la_consistent (Tsimplex s)
{
  return s->consistent;
}

/*-----------------------------------------------------------------------*/

/* DC Colects IDs of the constraints that resulted in a conflict */
static Tlist
la_colect_conflict_from_unreachable_goal(Tsimplex s)
{
  Tlist ptr, ret = NULL;
  
  /* DC For each variable in the goal explanation, add it to the conflict set */
  la_list_add_mons(&ret, s->goal->comb->mons);
  
  /* DC For each variable in the goal, add its bound to the conflict set */
  if (number_less(la_solution_value(s), la_goal_value(s)))
    {
      ptr = list_cdr(s->goal->le->mons);
      do
	{
	  Tmon m = list_car(ptr);
	  Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
	  if (number_less(m->coef, number_zero))
	    {
	      if (vp->exp_lower != NULL)
                la_list_add_mons(&ret, vp->exp_lower->mons);
	    }
	  else
	    {
	      if (vp->exp_upper != NULL)
		la_list_add_mons(&ret, vp->exp_upper->mons);
	    }
	  ptr = list_cdr(ptr);
	}
      while (ptr != s->goal->le->mons);
    }
  else
    {
      ptr = list_cdr(s->goal->le->mons);
      do
	{
	  Tmon m = list_car(ptr);
	  if (number_less(m->coef, number_zero))
	    {
	      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
	      if (vp->exp_upper != NULL)
		la_list_add_mons(&ret, vp->exp_upper->mons);
	    }
	  else
	    {
	      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
	      if (vp->exp_lower != NULL)
		la_list_add_mons(&ret, vp->exp_lower->mons);
	    }
	  ptr = list_cdr(ptr);
	}
      while (ptr != s->goal->le->mons);
    }
  return ret;
  
}

/*-----------------------------------------------------------------------*/

/* DC Colect the explanation of fixed variables in an expression */
static Tlist
la_colect_explanation_of_fixed_variables(Tsimplex s, Texp e)
{
  Tlist ptr, ret = NULL;
  
  /* DC For each fixed variable in the expression, add its bound to the conflict set */
  ptr = list_cdr(e->mons);
  do
    {
      Tmon m = list_car(ptr);
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
      if (number_equal(vp->value, vp->lower) && number_equal(vp->value, vp->upper))
	{
	  Texp exp = la_exp_new(s, NULL, NULL, 0, LA_INTERNAL, NULL);
          la_exp_combine(s, exp, vp->exp_upper, number_one, number_one);
	  la_exp_combine(s, exp, vp->exp_lower, number_one, number_one);
	  la_list_add_mons(&ret, exp->mons);
	  la_exp_free(exp);
	}
      ptr = list_cdr(ptr);
    }
  while (ptr != e->mons);

  return ret;
}

/*-----------------------------------------------------------------------*/

/* DC Checks for the bounds of the variable in the equation 'e', updating
 if necessary. PRE-CONDITION: there is only one variable in the equation. */
static void
la_equation_check_bound(Tsimplex s, Tequation e)
{
  assert(la_equation_has_one_variable(e));

#ifdef DEBUG_LA
  fprintf(stderr, "la_check_bound()\n");
#endif

  la_update_lower_bound(s, e);
  la_update_upper_bound(s, e);
}

/*-----------------------------------------------------------------------*/

/* DC Checks for the bounds of the variable in the inequality 'e', updating
 if necessary. PRE-CONDITION: there is only one variable in the equation. */
static void
la_inequality_check_bound(Tsimplex s, Tequation e)
{
  Tmon m = list_car(list_cdr(e->le->mons));
  assert(la_equation_has_one_variable(e));

#ifdef DEBUG_LA
  fprintf(stderr, "la_check_bound()\n");
#endif

  if (number_less(m->coef, number_zero))
    la_update_lower_bound(s, e);
  else
    la_update_upper_bound(s, e);
}

/*-----------------------------------------------------------------------*/

/* DC Updates the lower bound 'x' in 'e', assuming that 'e' is
   in the format "c1 - c2 * x <= 0" */
static void
la_update_lower_bound(Tsimplex s, Tequation e)
{
  Tmon m = list_car(list_cdr(e->le->mons));
  Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
  Tnumber n = number_new();
  
  /*printf("la_update_lower_bound()\n");
  la_exp_print(e->le);*/

#ifdef DEBUG_LA
  fprintf(stderr, "la_update_lower_bound()\n");
#endif
  if (!number_equal(m->coef, number_zero))
    {
      number_div(n, ((Tmon)list_car(e->le->mons))->coef, m->coef);
      number_neg(n);
      if (vp->is_int)
	number_ceil(n);
      if (number_greater(n, vp->lower))
        {
	  history_lower_bound_changed(s, vp);
	  number_cpy(vp->lower, n);
	  if (vp->exp_lower != NULL)
	    la_exp_free(vp->exp_lower);
	  vp->exp_lower = la_exp_cpy(e->comb);
	}
    }
  number_free(n);
}

/*-----------------------------------------------------------------------*/

/* DC Updates the upper bound 'x' in 'e', assuming that 'e' is
   in the format "c1 + c2 * x <= 0" */
static void
la_update_upper_bound(Tsimplex s, Tequation e)
{
  Tmon m = list_car(list_cdr(e->le->mons));
  Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
  Tnumber n = number_new();
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_update_upper_bound()\n");
#endif
  
  /*printf("la_update_upper_bound()\n");
  la_exp_print(e->le);*/
    
  if (!number_equal(m->coef, number_zero))
    {
      number_div(n, ((Tmon)list_car(e->le->mons))->coef, m->coef);
      number_neg(n);
      if (vp->is_int)
	number_floor(n);
      if (number_less(n, vp->upper))
	{
	  history_upper_bound_changed(s, vp);
	  number_cpy(vp->upper, n);
	  if (vp->exp_upper != NULL)
	    la_exp_free(vp->exp_upper);
	  vp->exp_upper = la_exp_cpy(e->comb);
	}
    }
  number_free(n);
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new equation. */
static Tequation
la_equation_new(Tsimplex s, Tnumber coef[], Tvar_id var_id[], Tunsigned size)
{
  Tnumber c[1];
  Tvar_id v[1]; 
  Tequation e;
  MY_MALLOC(e, sizeof(struct TSequation));

#ifdef DEBUG_LA
  fprintf(stderr, "la_equation_new()\n");
#endif
  
  e->id = s->level;
  e->bmon = NULL;
  
  c[0] = number_one;
  v[0] = la_equation_size(s);
  e->comb = la_exp_new(s, c, v, 1, LA_INTERNAL, e);
  
  e->le = la_exp_new(s, coef, var_id, size, LA_USER, e);
  e->user_le = la_exp_cpy(e->le);
  e->lm = list_add(NULL, (Tmon)list_car(list_cdr(e->comb->mons)));
  
  return e;
}

/*-----------------------------------------------------------------------*/

/* DC Frees the equation. It does not completly frees the equation,
   monomials of 'le' and 'comb' are set to zero, and later removed.*/
static void
la_equation_free(Tsimplex s, Tequation eq)
{
  /* DC Remove 'eq' trace from itself */
  Tmon m = (Tmon)list_car(eq->lm);
  Texp e1 = la_exp_cpy(eq->le);
  Texp e2 = la_exp_cpy(eq->comb);
  Tnumber n = number_neg(number_cpy(number_new(), number_one));
  
  la_exp_combine(s, m->e->le, e1, number_one, n);
  la_exp_combine(s, m->e->comb, e2, number_one, n);

  number_free(n);
  la_mon_free(m);
  la_exp_free(e1);
  la_exp_free(e2);
  list_free(&eq->lm);

  la_exp_free(eq->user_le);
  /* DC Do not free the monomials from 'le' and 'comb', except for the first. */
  la_mon_free(list_car(eq->le->mons)); 
  list_free(&eq->le->mons);
  free(eq->le);
  la_mon_free(list_car(eq->comb->mons)); 
  list_free(&eq->comb->mons);
  free(eq->comb);
  
  free(eq);
}

/*-----------------------------------------------------------------------*/

/* Replaces basic variables in the expression for an equivalent expression */
static void
la_equation_normalize(Tsimplex s, Tequation e1)
{
  Tlist lm = e1->le->mons;
  Tvar bv = la_get_basic_var(s, e1);
  
#ifdef DEBUG_LA
  fprintf(stderr, "la_equation_normalize():\n");
#endif
    
  /* DC For each variable in the expression */
  do
    {
      Tmon m = (Tmon)list_car(lm);
      lm = list_cdr(lm);
      if (la_var_is_basic(s, m->var) && m->var != bv)
	{
	  Tequation e2 = la_get_basic_equation(s, m->var);
	  Tnumber c1 = number_neg(number_cpy(number_new(), m->coef));
	  number_div(c1, c1, la_get_basic_coef(s, e2));
	  
  	  la_exp_combine(s, e1->le, e2->le, number_one, c1);
	  la_exp_combine(s, e1->comb, e2->comb, number_one, c1);
	  number_free(c1);
	  
	  /* DC The list pointer may be deleted during the combination, so restart */
	  lm = list_cdr(e1->le->mons);
	}
    }
  while (lm != e1->le->mons);
  
}

/*-----------------------------------------------------------------------*/

/* DC Try to find a variable that has no upper and lower bounds to be the next basic variable.
 * If none is found then get the variable with larger difference between upper and lower bounds.
 * Assumes that all variable in 'le' are non-basic.
 */
static Tmon
la_mon_get_best_to_become_basic_variable(Tsimplex s, Texp le)
{
  Tmon m = (Tmon)list_car(list_cdr(le->mons));
  Tmon best_m = m;
  Tvar_prop vp;
  Tnumber best_range = number_cpy(number_new(), number_zero);
  Tnumber range = number_new();

  /* DC For each variable in 'e' */
  Tlist ptr = list_cdr(le->mons);
  do
    {
      /* DC Verify the bounds to look for the best variable */
      m = list_car(ptr);
      vp = (Tvar_prop)table_get(s->vp, m->var->id);
      if (number_equal(vp->lower, number_minus_infinity) && number_equal(vp->upper, number_infinity))
	{
	  best_m = m;
	  number_cpy(best_range, number_infinity);
	  break;
	}
      else
	{
	  number_sub(range, vp->upper, vp->lower);
	  if (number_greater(best_range, range))
	    {
	      number_cpy(best_range, range);
	      best_m = m;
	    }
	}

      ptr = list_cdr(ptr);
    }
  while (ptr != le->mons);

  number_free(best_range);
  number_free(range);

  return best_m;
}

/*-----------------------------------------------------------------------*/

/* DC The equation 'e' is about to be included in the simplex
 * and 'm->var' is about to become a basic variable, so
 * remove 'm->var' of the other equations by combining them with
 * 'e' using appropriated coefficients.
 */
static void
la_mon_combine_to_remove_from_equations(Tsimplex s, Tmon m, Tequation e){
  Tvar_prop vp =  (Tvar_prop)table_get(s->vp, m->var->id);

  /* DC For each equation 'm2->e' that contains 'm->var',
   * except for 'e' that is still not in 'vp->lm' */
  if (vp->lm != NULL)
    {
      Tnumber c2 = number_new();

      Tlist ptr = vp->lm;
      while (ptr != NULL)
	{
	  /* DC Combine 'm2->e2' with 'm->e' to remove 'm->var' */
	  Tmon m2 = (Tmon)list_car(ptr);
	  if (number_equal(m2->coef, number_zero))
	    {
	      /* DC Update 'equation linking list' */
	      la_mon_free(m2);
	      if (la_list_remove(&ptr, &vp->lm)) break;
	    }
	  else
	    {
	      number_cpy(c2, m2->coef);
	      number_neg(c2);
	      number_div(c2, c2, m->coef);

	      la_exp_combine(s, m2->e->le, e->le, number_one, c2);
	      la_exp_combine(s, m2->e->comb, e->comb, number_one, c2);

	      ptr = list_cdr(ptr);
	      if (ptr == vp->lm)
		break;
	    }
	}
      number_free(c2);
    }
}

/*-----------------------------------------------------------------------*/

/* DC Adds a new equation to the simplex. Also chooses one of its variables
   to be a basic variable. If the equation contains only one
   variable then its bound is checked and no equation is added. */
static void
la_equation_add(Tsimplex s, Tequation e)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_equation_add()\n");
#endif
  
  /* DC If there is no variable */
  if (list_cdr(e->le->mons) == e->le->mons)
    {
      assert(number_equal(((Tmon)list_car(e->le->mons))->coef, number_zero));
    }
  /* DC If there is only one variable in the equation */
  else if (list_cdr(list_cdr(e->le->mons)) == e->le->mons)
    {
      la_equation_check_bound(s, e);
      la_equation_inc(s);
    }
  else
    {
      /* DC Get variable to become basic */
      Tmon m = la_mon_get_best_to_become_basic_variable(s, e->le);
      Tvar_prop vp =  (Tvar_prop)table_get(s->vp, m->var->id);

      /* DC Set 'm->var' variable as basic */
      vp->basic = table_length(s->eq)-1;
      e->bmon = m;
      
      la_mon_combine_to_remove_from_equations(s, m, e);
      la_exp_update_monomial_linking_list_of_its_variables(e->le, s);      
    }
}

/*-----------------------------------------------------------------------*/

/* DC Adds a new equation to the simplex, knowing that originally 
   the given equation was an inequality. If the equation contains only one
   variable, its bound is changed and no equation is added. */
static void
la_inequality_add(Tsimplex s, Tequation e)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_inequality_add()\n");
  printf("From: "); la_exp_print(e->le); printf("\n");
#endif
  
  /* DC If there is no variable */
  if (list_cdr(e->le->mons) == e->le->mons)
    {
      assert(number_leq(((Tmon)list_car(e->le->mons))->coef, number_zero));
    }
  /* DC If there is only one variable in the equation */
  else if (list_cdr(list_cdr(e->le->mons)) == e->le->mons)
    {
      la_inequality_check_bound(s, e);
      la_equation_inc(s);
    }
  else
    {
      if (la_exp_is_all_var_int(e->le, s))
	{
	  /* DC Create new slack int variable */
	  Tnumber lcm = number_new(), cons = number_new();
	  Tmon m = la_mon_new(number_one, (Tvar_id) table_length(s->vp), e);
	  Tmon m2 = la_mon_new(number_one, (Tvar_id) table_length(s->vp), e);
	  Tvar_prop vp;
	  
#ifdef DEBUG_LA
	  fprintf(stderr, "la_inequality_add(): Creating int basic variable\n");
#endif
	  
	  la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term(e->le, lcm, cons, s);
	  number_div(m->coef, number_one, lcm);
	  number_div(m2->coef, number_one, lcm);
	  
	  list_add(e->le->mons, m);
	  list_add(e->user_le->mons, m2);
	  
	  la_increase_properties(s, -1, LA_INT);

	  vp = (Tvar_prop)table_get(s->vp, m->var->id);
	  number_cpy(vp->lower, number_zero);
	  number_mul(vp->value, la_solution_value(s), lcm);
	  number_neg(vp->value);

	  /* DC Get variable to become basic */
	  m = la_mon_get_best_to_become_basic_variable(s, e->le);
	  vp = (Tvar_prop)table_get(s->vp, m->var->id);

	  /* DC Set 'm->var' variable as basic */
	  vp->basic = table_length(s->eq)-1;
	  e->bmon = m;
	  
	  la_mon_combine_to_remove_from_equations(s, m, e);
	  la_exp_update_monomial_linking_list_of_its_variables(e->le, s);
	  	  
	  number_free(lcm);
	  number_free(cons);
	}
      else
	{
	  /* DC Create new (basic) variable */
	  Tmon m = la_mon_new(number_one, (Tvar_id) table_length(s->vp), e);
	  Tmon m2 = la_mon_new(number_one, (Tvar_id) table_length(s->vp), e);
	  Tvar_prop vp;
	  
	  /* DC Add explanation to the bound of the slack variable */
	  /*Tnumber n = number_cpy(number_new(), number_one);
	   Tmon m2 = la_mon_new(n, 1000+m->var->id, e);
	   int v[1]; Tnumber c[1];*/
	  
#ifdef DEBUG_LA
	  fprintf(stderr, "la_inequality_add(): Creating basic variable\n");
#endif
	    
	  list_add(e->le->mons, m);
	  list_add(e->user_le->mons, m2);
	  
	  la_increase_properties(s, -1, LA_RATIONAL);

	  vp = (Tvar_prop)table_get(s->vp, m->var->id);
	  number_cpy(vp->lower, number_zero);
	  number_cpy(vp->value, la_solution_value(s));
	  number_neg(vp->value);
	  
	  /* DC Add explanation to the bound of the slack variable */
	  /*v[0] = 1000+m->var->id; c[0] = number_cpy(number_new(), number_one);
	   la_exp_free(vp->exp_lower);
	   vp->exp_lower = la_exp_new(s, c, v, 1, LA_INTERNAL, NULL);
	   list_add(e->comb->mons, m2);*/
	  
	  /* DC Get variable to become basic */
	  m = la_mon_get_best_to_become_basic_variable(s, e->le);
	  vp = (Tvar_prop)table_get(s->vp, m->var->id);

	  vp->basic = table_length(s->eq)-1;
	  e->bmon = m;
	  
	  la_mon_combine_to_remove_from_equations(s, m, e);
	  la_exp_update_monomial_linking_list_of_its_variables(e->le, s);
	}
    }
}

/*-----------------------------------------------------------------------*/

/* DC Used when the problem is already inconsistent, it increments the counter
   of pushed equations */
static void
la_equation_inc(Tsimplex s)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_equation_inc()\n");
#endif
  
  ;
}

/*-----------------------------------------------------------------------*/

/* DC Returns the number of pushed equations */
static int
la_equation_size(Tsimplex s)
{
  return s->level;
}

/*-----------------------------------------------------------------------*/

/* DC Returns the equation associated to the variable 'v'.
 PRE-CONDITION: it exists such association */
static Tequation
la_equation_from_var(Tsimplex s, Tvar v)
{
  return (Tequation)table_get(s->eq, v->id-1);
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if there is only one variable in the equation. The
 * constant term, variable id = 0, does not count. */
static bool
la_equation_has_one_variable(Tequation e)
{
  return list_cdr(list_cdr(e->le->mons)) == e->le->mons &&
    list_cdr(e->le->mons) != e->le->mons;
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new disequality */
static Tdisequality
la_disequality_new(Tsimplex s, Tvar_id var_id1, Tvar_id var_id2)
{
  Tdisequality d;
  MY_MALLOC(d, sizeof(struct TSdisequality));
  d->var_id1 = var_id1;
  d->var_id2 = var_id2;
  d->id = s->level;
  return d;
}

/*-----------------------------------------------------------------------*/

/* DC Frees a disequality */
static void
la_disequality_free(Tdisequality d)
{
  free(d);
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new equality */
static Tequality
la_equality_new(Tsimplex s, Tvar_id var_id1, Tvar_id var_id2)
{
  Tequality e;
  MY_MALLOC(e, sizeof(struct TSequality));
  e->var_id1 = la_var_id_recover(s, var_id1);
  e->var_id2 = la_var_id_recover(s, var_id2);
  if (e->var_id1 > e->var_id2)
    {
      Tvar_id t = e->var_id1;
      e->var_id1 = e->var_id2;
      e->var_id2 = t;
    }
  return e;
}

/*-----------------------------------------------------------------------*/

/* DC Frees an equality */
static void
la_equality_free(Tequality e)
{
  free(e);
}

/*-----------------------------------------------------------------------*/

/* DC Searches for model equalities. If there is no conflict 
   with disequalities store them, otherwise save the conflicting disequality */
static void
la_search_model_equalities(Tsimplex s)
{
  int i, j;
  /* DC number of variables */
  Tunsigned size;
  /* DC pair of variable and model value used to be sorted and find model equalities */
  Tnumber_int_pair *var_dist;

  /* DC Don't generate model equalities if the model needs to be corrected */
  if (!table_empty(s->model_conflict))
    return;

  /* DC Init */
  size = table_length(s->vp);
  MY_MALLOC (var_dist, size * sizeof (Tnumber_int_pair));

  /* DC Pre-process: ignore variable 0, copy and sort */
  for (i = 1, j = 0; i < size; ++i)
    {
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, i);
      if (vp->user_id != -1)
	{
	  var_dist[j].first = vp->value;
	  var_dist[j++].second = vp->user_id;
	}
    }
  size = j;
  qsort (var_dist, size, sizeof (Tnumber_int_pair), compare_Tnumber_int_pair);

  /* DC find model equalities */
  for (i = 1; i < size; ++i)
    if (number_equal (var_dist[i].first, var_dist[i - 1].first))	/* DC x == y */
      {
	/* DC Create the equality and save it */
	Tequality e = la_equality_new(s, var_dist[i].second, var_dist[i-1].second);

	/* DC If it is not already found */
	if (set_lookup (s->returned_eq, (void *) e) == NULL)
          table_push (s->model_eq, (void *) e);
	else
	  la_equality_free (e);
      }
      
  /*for (i = 0; i < table_length(s->disequalities); ++i){
    printf("X%d != X%d\n", ((Tdisequality)table_get(s->disequalities, i))->var_id1, ((Tdisequality)table_get(s->disequalities, i))->var_id2);
  }*/

  /* DC Searches for a conflict between a disequality and model equalities */
  for (i = 0; i < table_length(s->disequalities); ++i)
    {
      Tdisequality d = (Tdisequality) table_get (s->disequalities, i);
      Tvar_prop vp1 = (Tvar_prop) table_get(s->vp, d->var_id1);
      Tvar_prop vp2 = (Tvar_prop) table_get(s->vp, d->var_id2);
      if (number_equal(vp1->value, vp2->value))
        table_push(s->model_conflict, d);
    }
    
  /* DC Model equalities are only really saved if there are no problems with disequalities */
  if (table_empty(s->model_conflict)) 
    for (i = 0; i < table_length(s->model_eq); ++i)
      history_equality_found (s, (Tequality)table_get(s->model_eq, i));
  else
    {
      for (i = 0; i < table_length(s->model_eq); ++i)
        {
          Tequality e = (Tequality) table_get(s->model_eq, i);
          set_remove (s->returned_eq, e);
          la_equality_free(e);
        }
      table_erase (s->model_eq);
    }
    
  /* DC free */
  free (var_dist);
}  

/*-----------------------------------------------------------------------*/

/* DC Function that compare two equalities */
static int
la_equality_compare (Tequality a, Tequality b)
{
  if (a->var_id1 == a->var_id2)
    return 0;
  return (a->var_id1 > a->var_id2 ? 1 : -1);
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new expression in the correct format. */
static Texp
la_exp_new(Tsimplex s, Tnumber coef[], Tvar_id var_id[], 
	   Tunsigned size, Texp_kind ek, Tequation eq)
{
  Texp e;
  Tlist lm; /* DC Final sorted list of monomials */
  Tsigned i;
  /* DC this is an insertion sort in a circular list. 
     Complexity: worst case O(n2) (reversed); best case O(n) (already sorted);
     'lm' should point to the first element of the sorted list of monomials. */
  lm = list_cons(la_mon_new(number_zero, 0, eq), NULL);
  for (i = size - 1; i >= 0; --i)
    if (!number_equal(coef[i], number_zero))
      {
	Tmon new_mon = la_mon_new(coef[i], var_id[i], eq);
	Tlist ptr = lm;
	while (true)
	  {
	    Tmon m = (Tmon)list_car(ptr);
	    if (la_mon_less(new_mon, m))
	      {
		list_cons(new_mon, ptr);
		break;
	      }
	    else if (la_mon_less(m, new_mon))
	      {
		ptr = list_cdr(ptr);
		if (ptr == lm)
		  {
		    list_cons(new_mon, lm);
		    break;
		  }
	      }
	    else
	      {
		number_add(m->coef, m->coef, coef[i]);
		if (m->var->id != 0 && number_equal(m->coef, number_zero))
		  {
		    la_mon_free(m);
		    list_remove(ptr);
		  }
		la_mon_free(new_mon);
		break;
	      }
	  }
      }
  MY_MALLOC(e, sizeof(struct TSexp));
  e->mons = lm;
  e->kind = ek;  
#ifdef DEBUG_LA
  /*fprintf(stderr, "la_exp_new(): ");
  la_exp_print(e);
  fprintf(stderr, "\n");*/
#endif
  return e;
}

/*-----------------------------------------------------------------------*/

/* DC makes a copy of the expression */
static Texp
la_exp_cpy(Texp e)
{
  Texp ne;
  Tlist ptr;
  MY_MALLOC(ne, sizeof(struct TSexp));
  ne->kind = e->kind;
  ne->mons = NULL;
  ptr = e->mons;
  do 
    {
      Tmon m = (Tmon)list_car(ptr);
      Tmon m2 = la_mon_new(m->coef, m->var->id, m->e);
      ne->mons = list_add(ne->mons, m2);
      ptr = list_cdr(ptr);
    }
  while (ptr != e->mons);
  return ne;
}

/*-----------------------------------------------------------------------*/

/* DC Frees the expression */
static void       
la_exp_free(Texp e)
{
  Tlist ptr;
  ptr = e->mons;
  do
    {
      la_mon_free((Tmon)list_car(ptr));
      ptr = list_cdr(ptr);
    }
  while (ptr != e->mons);
  list_free(&e->mons);
  free(e);
}

/*-----------------------------------------------------------------------*/

/* DC Combines two expresions: e1 = n1 * e1 + n2 * e2.
   Complexity linear: O(|e1|+|e2|) */
static void
la_exp_combine(Tsimplex s, Texp e1, Texp e2, Tnumber n1, Tnumber n2)
{
  Tlist lm1 = e1->mons;
  Tlist lm2 = e2->mons;
  Tequation eq = ((Tmon)list_car(lm1))->e;
  
#ifdef DEBUG_LA
  /*fprintf(stderr, "la_exp_combine(begin): ");
  la_exp_print(e1);
  fprintf(stderr, "\n");*/
#endif
  
  /* DC Merge the 2 lists doing the necessary combination. */
  do 
    {
      Tmon m1 = (Tmon)list_car(lm1);
      Tmon m2 = (Tmon)list_car(lm2);
      if (la_mon_less(m1, m2))
	{
	  number_mul(m1->coef, m1->coef, n1);
	  if (m1->var->id != 0 && number_equal(m1->coef, number_zero))
	    {
	      /*printf("removing link1: "); la_mon_print(m1, 'x'); printf("\n");*/
	      lm1 = list_remove(lm1);
	      /* DC If there is no link to the monomial, i.e. :
	         if the variable doesn't exist anymore;
	         OR if it is from a equation that there's no link to it (goal);
	         OR if it is an internal expression used for temporary computation.
	      */
	      if ((e1->kind == LA_USER && m1->var->id >= la_var_id_register_count(s)) ||
		  (e1->kind == LA_USER && eq->bmon == NULL) ||
		  (e1->kind == LA_INTERNAL && eq == NULL))		
		la_mon_free(m1);
	    }
	  else
	    lm1 = list_cdr(lm1);
	}
      else if (la_mon_less(m2, m1))
	{
	  Tnumber n = number_new();
	  number_mul(n, m2->coef, n2);
	  if (m2->var->id == 0 || !number_equal(n, number_zero))
	    {
	      Tmon m = la_mon_new(n, m2->var->id, eq);
    	      list_cons(m, lm1);
	      if (e1->kind == LA_USER)
		{
		  Tvar_prop vp = ((Tvar_prop)table_get(s->vp, m2->var->id));
		  /* DC If 'e1' is not the goal */
	          if (eq->bmon != NULL)
		    /* DC Update the equation linking list of the variable */
		    vp->lm = list_add(vp->lm, m);
		  else
		    /* DC Update the monomial goal of the variable */
		    vp->goal_mon = m;
		}
	      else if (eq != NULL)
		/* DC Update the equation linking list of the equation */
		list_add(la_equation_from_var(s, m->var)->lm, m);
	    }
	  lm2 = list_cdr(lm2);
	  number_free(n);
	}
      else
	{
	  Tnumber n = number_new();
	  number_mul(n, m2->coef, n2);
	  
	  number_mul(m1->coef, m1->coef, n1);
	  number_add(m1->coef, m1->coef, n);
	  
	  if (m1->var->id != 0 && number_equal(m1->coef, number_zero))
            {
	      /*printf("removing link2: "); la_mon_print(m1, 'x');*/
	      /*printf(" from:"); la_exp_print(e1); printf("\n");*/
	      lm1 = list_remove(lm1);
	      /* DC If there is no link to the monomial, i.e. :
	         if the variable doesn't exist anymore;
	         OR if it is from a equation that there's no link to it (goal);
	         OR if it is an internal expression used for temporary computation.
	       */
	      if ((e1->kind == LA_USER && m1->var->id >= la_var_id_register_count(s))
		  || (e1->kind == LA_USER && eq->bmon == NULL)
		  || (e1->kind == LA_INTERNAL && eq == NULL))
	      	la_mon_free(m1);
	    }
	  else
	    lm1 = list_cdr(lm1);
	  lm2 = list_cdr(lm2);
	  number_free(n);
	}
    }
  while (!la_list_mon_begin(lm1) && !la_list_mon_begin(lm2));
  
  /* DC Append the remaining of the list 1 */
  while (lm1 != e1->mons)
    {
      Tmon m1 = (Tmon)list_car(lm1);
      number_mul(m1->coef, m1->coef, n1);
      if (m1->var->id != 0 && number_equal(m1->coef, number_zero))
        {
	  /*printf("removing link3: "); la_mon_print(m1, 'x'); printf("\n");*/
	  lm1 = list_remove(lm1);
	  /* DC If there is no link to the monomial, i.e. :
	         if the variable doesn't exist anymore;
	         OR if it is from a equation that there's no link to it (goal);
	         OR if it is an internal expression used for temporary computation.
	       */
	  if ((e1->kind == LA_USER && m1->var->id >= la_var_id_register_count(s))
	      || (e1->kind == LA_USER && eq->bmon == NULL)
	      || (e1->kind == LA_INTERNAL && eq == NULL))
	    la_mon_free(m1);
	}
      else
	lm1 = list_cdr(lm1);
    }
  
  /*printf("current\n");
  la_exp_print(e1); printf("\n");
  la_exp_print(e2); printf("\n");*/
  
  /* DC Append the remaining of the list 2 */
  while (lm2 != e2->mons)
    {
      Tmon m2 = (Tmon)list_car(lm2);
      Tnumber n = number_new();
      number_mul(n, m2->coef, n2); 
      if (m2->var->id == 0 || !number_equal(n, number_zero))
	{
	  Tmon m = la_mon_new(n, m2->var->id, eq);
    	  list_cons(m, lm1);
	  if (e1->kind == LA_USER)
	    {
	      Tvar_prop vp = ((Tvar_prop)table_get(s->vp, m2->var->id));
	      /* DC If 'e1' is not the goal */
	      if (eq->bmon != NULL)
		/* DC Update the equation linking list of the variable */
		vp->lm = list_add(vp->lm, m);
	      else
		/* DC Update the monomial goal of the variable */
		vp->goal_mon = m;
	    }
	  else if (eq != NULL)
	    /* DC Update the equation linking list of the equation */
	    list_add(la_equation_from_var(s, m->var)->lm, m);
	}
      lm2 = list_cdr(lm2);
      number_free(n);
    }
#ifdef DEBUG_LA
  /*fprintf(stderr, "la_exp_combine(end): ");
  la_exp_print(e1);
  fprintf(stderr, "\n");*/
#endif
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if all the non fixed variable in the expression are
   integer */
static bool
la_exp_is_all_var_int(Texp le, Tsimplex s)
{
  Tlist ptr = list_cdr(le->mons);

  /*printf("la_exp_is_all_var_int()\n");*/
  
  do
    {
      Tmon m = (Tmon)list_car(ptr);
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
      
      if (vp->is_int)
	/*printf("%dx is int. It has upper and lower bounds %s, %s and value %s\n", m->var->id, number_to_str(vp->upper), number_to_str(vp->lower), number_to_str(vp->value))*/;
      else if (number_equal(vp->value, vp->upper) && number_equal(vp->value, vp->lower))
	/*printf("%dx is fixed. It has upper and lower bounds %s, %s and value %s\n", m->var->id, number_to_str(vp->upper), number_to_str(vp->lower), number_to_str(vp->value))*/;
      else
	{
	  /*printf("%dx is neither int or fixed. It has upper and lower bounds %s, %s and value %s\n", m->var->id, number_to_str(vp->upper), number_to_str(vp->lower), number_to_str(vp->value));*/
	  return false;
	}
      
      ptr = list_cdr(ptr);
    }
  while (ptr != le->mons);
  
  return true;
}

/*-----------------------------------------------------------------------*/

/* DC Gets the lcm (least common multiple) of the coefficient denominators of
   the non-fixed variables; also gets the constant term of the expression: 
   the constant term includes the fixed variables and the term with no
   variable */
static void
la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term(Texp le, Tnumber lcm, Tnumber cons, Tsimplex s)
{
  Tlist ptr = le->mons;
  Tnumber tmp = number_new();

  /*printf("la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term()\n");*/
  
  number_cpy(lcm, number_one);
  number_cpy(cons, ((Tmon)list_car(ptr))->coef);
  
  ptr = list_cdr(ptr);
  do
    {
      Tmon m = (Tmon)list_car(ptr);
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
      
      if (!number_equal(vp->value, vp->upper) || !number_equal(vp->value, vp->lower))
	{
	  number_denominator(tmp, m->coef);
	  number_lcm(lcm, lcm, tmp);
	}
      else
        {
	  number_mul(tmp, m->coef, vp->value);
	  number_add(cons, cons, tmp);
	}
      ptr = list_cdr(ptr);
    }
  while (ptr != le->mons);
  
  number_free(tmp);
}

/*-----------------------------------------------------------------------*/

/* DC Gets the gcd (greatest common divisor) of the coefficient of the
   non-fixed variables after normalization, i.e., gcd_of('mult'*'le').
   The multiplication number is suppose to transform the rational numbers
   in integer numbers. */
static void
la_exp_get_gcd_after_normalization(Texp le, Tnumber gcd, Tnumber mult, Tsimplex s)
{
  Tlist ptr = list_cdr(le->mons);
  Tnumber tmp = number_new();
  
  do
    {
      Tmon m = list_car(ptr);
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
      
      if (!number_equal(vp->value, vp->upper) || !number_equal(vp->value, vp->lower))
	{
	  number_mul(tmp, mult, m->coef);
	  number_gcd(gcd, gcd, tmp);
	}
      if (number_equal(gcd, number_one))
	break;
      ptr = list_cdr(ptr);
    }
  while (ptr != le->mons);
  
  number_free(tmp);
}

/*-----------------------------------------------------------------------*/

/* DC Checks if the expression (of int variables) has an integer solution.
   The check is complete. */
static bool
la_exp_has_int_solution(Texp le, Tsimplex s)
{
  Tnumber lcm = number_new(), gcd = number_new(), cons = number_new();
  bool has_int_solution = true;
  
  /* DC The check is: get the lmc of the denominators of
     the coefficients (they should be changed to integers),
     the constant part should be divisible by the gcd. */
  
#ifdef DEBUG_LA
  printf("Checking for integer solutions in: ");
  la_exp_print(le);
  printf("\n");
#endif
    
  la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term(le, lcm, cons, s);
  la_exp_get_gcd_after_normalization(le, gcd, lcm, s);
  
  number_mul(cons, cons, lcm);
#ifdef DEBUG_LA
  printf("The constant number is %s\n", number_to_str(cons));
  printf("The LCM number is %s\n", number_to_str(lcm));
  printf("The GCD is %s\n", number_to_str(gcd));
  printf("Checking if %s is divisible by %s\n", number_to_str(cons), number_to_str(gcd));
#endif
  if (number_is_int(cons))
    {
      if (!number_equal(gcd, number_zero))
	number_mod(cons, cons, gcd);
      if (!number_equal(cons, number_zero))
	has_int_solution = false;
      /*else
        printf("Have integer solution\n");*/
    }
  else
    has_int_solution = false;
  
  number_free(lcm);
  number_free(gcd);
  number_free(cons);
  
  return has_int_solution;
}

/*-----------------------------------------------------------------------*/

/* DC Updates the 'monomial link list' of each variable in the expression */
static void
la_exp_update_monomial_linking_list_of_its_variables(Texp le, Tsimplex s)
{
  /* DC For each variable in 'e' */
  Tlist ptr = list_cdr(le->mons);
  if (ptr != le->mons)
    do
      {
	/* DC Update its 'monomial linking list' */
	Tmon m = list_car(ptr);
	Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
	vp->lm = list_add(vp->lm, m);
	
	ptr = list_cdr(ptr);
      }
    while (ptr != le->mons);
}

/*-----------------------------------------------------------------------*/

/* DC Removes the monomials of all the fixed variables from an equation. 
   It assumes there are no 'links' to the monomials */
static void
la_exp_remove_unlinked_fixed_variables(Tequation e, Tsimplex s)
{
  Texp le = e->le, comb = e->comb;
  Tlist ptr = list_cdr(le->mons);
  
  do
    {
      Tmon m = (Tmon)list_car(ptr);
      Tvar_prop vp = (Tvar_prop)table_get(s->vp, m->var->id);
      if (number_equal(vp->value, vp->lower) && number_equal(vp->value, vp->upper))
	{
	  la_exp_combine(s, comb, vp->exp_upper, number_one, number_one);
	  la_exp_combine(s, comb, vp->exp_lower, number_one, number_one);
	  la_mon_free(m);
	  ptr = list_remove(ptr);
	}
      else
	ptr = list_cdr(ptr);
    }
  while (ptr != le->mons);
  
}

/*-----------------------------------------------------------------------*/

/* DC Rewrites the inequality by rounding down the constant part.
   If the coefficient and variable are integers, they should sum up to an
   integer, so do the necessary calculation for include this eager cut. */
static void
la_exp_round_down_inequality_of_integers(Tequation e, Tsimplex s)
{
  Texp le = e->le;
  Tnumber lcm = number_new(), cons = number_new();
  Tnumber constant_term = ((Tmon)list_car(le->mons))->coef;
  
  la_exp_get_lcm_coefficient_denominators_int_var_and_constant_term(le, lcm, cons,  s);
  /*printf("The LCM number is %s\n", number_to_str(lcm));
  printf("The constant part is %s\n", number_to_str(cons));*/
  number_mul(constant_term, cons, lcm);
  number_ceil(constant_term);
  number_div(constant_term, constant_term, lcm);
  /*printf("It will be: %s\n", number_to_str(constant_term));*/
  la_exp_remove_unlinked_fixed_variables(e, s);
  /*printf("Final: "); la_exp_print(le); printf("\n");*/
  
  number_free(lcm);
  number_free(cons);
}

/*-----------------------------------------------------------------------*/

/* DC Increases the table of variable properties, 
   allowing one more (user or basic) variable in the simplex. */
static Tvar_prop
la_increase_properties(Tsimplex s, Tvar_id user_id, Tvar_kind var_type)
{
  Tvar_prop vp;
  MY_MALLOC(vp, sizeof(struct TSvar_prop));

  vp->upper = number_new();
  vp->lower = number_new();
  vp->inc = number_new();
  vp->value = number_new();
  vp->sol_inc = number_new();
  
  vp->exp_upper = la_exp_new(s, NULL, NULL, 0, LA_INTERNAL, NULL);
  vp->exp_lower = la_exp_new(s, NULL, NULL, 0, LA_INTERNAL, NULL);
  
  vp->is_int = (var_type == LA_INT ? true : false);
  number_cpy(vp->upper, number_infinity);
  number_cpy(vp->lower, number_minus_infinity);
  vp->var_lim = NULL;
  vp->goal_mon = NULL;
  vp->lm = NULL;
  vp->basic = -1;
  vp->user_id = user_id;
  
  table_push(s->vp, (void *)vp);
  history_properties_increased(s);
  return vp;
}

/*-----------------------------------------------------------------------*/

/* DC Frees the variable properties */
static void
la_var_prop_free(Tvar_prop vp)
{
  /* DC remove remaining (zero) monomial from the equation linking list
     that have not been removed so far */
  Tlist ptr = vp->lm;
  while (ptr != NULL) 
    {
      Tmon m = (Tmon)list_car(ptr);
      if (number_equal(m->coef, number_zero))
        {
	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&ptr, &vp->lm)) break;
	}
      else
	{
	  ptr = list_cdr(ptr);
	  if (ptr == vp->lm)
	    break;
	}		
    }
  
  la_exp_free(vp->exp_lower);
  la_exp_free(vp->exp_upper);
  number_free(vp->sol_inc);
  number_free(vp->value);
  number_free(vp->inc);
  number_free(vp->lower);
  number_free(vp->upper);
  list_free(&vp->lm);
  free(vp);
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new variable with no properties */
static Tvar
la_var_new(Tvar_id var_id)
{
  Tvar v;
  MY_MALLOC(v, sizeof(struct TSvar));
  v->id = var_id;
  return v;
}

/*-----------------------------------------------------------------------*/

/* DC Frees the variable */
static void
la_var_free(Tvar v)
{
  free(v);
}

/*-----------------------------------------------------------------------*/

/* DC Returns the current value of the variable 'v' */
static Tnumber 
la_var_value(Tsimplex s, Tvar v)
{
  return ((Tvar_prop)table_get(s->vp, v->id))->value;
}

/*-----------------------------------------------------------------------*/

/* DC Checks for new variables in the equation. If there is a new variable then
   its properties are initialize. In the end, all the user variable ids are
   replaced by internal ids. */
static void
la_check_var(Tsimplex s, Tvar_id var_id[], Tvar_kind var_type[], Tunsigned size)
{
  Tunsigned i;

#ifdef DEBUG_LA
  fprintf(stderr, "la_check_var()\n");
#endif

  /* DC For each variable */
  for (i = 0; i < size; ++i)
    {
      Tvar_id* la_id = la_var_id_lookup(s, var_id[i]);
      /* DC If it is not present in the simplex yet */
      if (la_id == NULL)
	{
	  Tunsigned new_id = la_var_id_register(s, var_id[i], var_type[i]);
	  var_id[i] = new_id;
	}
      else
	var_id[i] = *la_id;
    }
}

/*-----------------------------------------------------------------------*/

/* DC For each constraint that the variable 'var-id' appears,
   check if there is an integer solution. Not complet check. */
static bool
la_var_has_int_solution(Tvar_id var_id, Tsimplex s)
{
  bool has_int_solution = true;
  Tvar_prop vp = (Tvar_prop)table_get(s->vp, var_id);
  Tlist mons = vp->lm;

  /*printf("\nx%d is int and has value = %s\n", var_id, number_to_str(vp->value));*/

  mons = vp->lm;
  while (mons != NULL)
    {
      Tmon m = (Tmon)list_car(mons);

      if (number_equal(m->coef, number_zero))
	{
	  /*printf("la_adjust(%dx): !!!: ", m->var->id);
	  la_exp_print(m->e->le);
	  printf("\n");*/

	  /* DC Update equation linking list */
	  la_mon_free(m);
	  if (la_list_remove(&mons, &vp->lm)) break;
	}
      else
	{

	  /*printf("(%dx): Pre-checking for integer solutions in: ", m->var->id);
	  la_exp_print(m->e->le);
	  printf("\n");*/

	  if (la_exp_is_all_var_int(m->e->le, s))
	    {
	      /*printf("Expression has all int variables\n");*/
	      if (la_exp_has_int_solution(m->e->le, s) == false)
		has_int_solution = false/*, printf("Expression has no int solution\n")*/;
	      /*else
		printf("Have integer solution\n");*/
	    }
	  if (has_int_solution == false)
	    break;
	  mons = list_cdr(mons);
	  if (mons == vp->lm)
	    break;
	}
    }

  return has_int_solution;
}

/*-----------------------------------------------------------------------*/

/* DC Returns a pointer to the internal identification of the user Tvar_id,
 *    or NULL if it was never registered. */
static Tvar_id*
la_var_id_lookup(Tsimplex s, Tvar_id user_id)
{
  return (Tvar_id *) hashmap_lookup(s->hmid, (void *) user_id);
}

/*-----------------------------------------------------------------------*/

/* DC Returns the internal identification of the user Tvar_id. */
static Tvar_id
la_var_id_recover(Tsimplex s, Tvar_id user_id){
  return (Tvar_id) *hashmap_lookup(s->hmid, (void *) user_id);
}

/*-----------------------------------------------------------------------*/

/* DC Registers the user Tvar_id returning a unique internal identification. */
static Tvar_id
la_var_id_register(Tsimplex s, Tvar_id user_id, Tvar_kind var_type)
{
  Tunsigned new_id = (Tunsigned)table_length(s->vp);
  hashmap_insert(s->hmid, (void *) user_id, (void *) new_id);
  history_variable_associated(s, user_id);
  la_increase_properties(s, user_id, var_type);
  return new_id;
}

/*-----------------------------------------------------------------------*/

/* DC Unregister the user Tvar_id. This is necessary for backtrack support. */
static void
la_var_id_unregister(Tsimplex s, Tvar_id user_id)
{
  hashmap_remove(s->hmid, (void *) user_id);
}

/*-----------------------------------------------------------------------*/

/* DC Returns the number of Tvar_id that are currently registered. */
static Tunsigned
la_var_id_register_count(Tsimplex s)
{
  return table_length(s->vp);
}

/*-----------------------------------------------------------------------*/

/* DC Initializes the submodule that controls user variables identification
 *    numbers */
static void
la_var_id_init(Tsimplex s)
{
  s->hmid = hashmap_new(TABLE_INIT_SIZE, (TFhash) int_hash, (TFequal) int_equal, NULL, NULL);
}

/*-----------------------------------------------------------------------*/

/* DC Resets the submodule that controls user variables identification
 *    numbers by removing all current registrations. */
static void
la_var_id_reset(Tsimplex s)
{
  hashmap_erase(s->hmid);
}

/*-----------------------------------------------------------------------*/

/* DC Finilizes the submodule that controls the variables identification
 *    numbers */
static void
la_var_id_free(Tsimplex s)
{
  hashmap_free(&s->hmid);
}

/*-----------------------------------------------------------------------*/

/* DC Returns true is the variable 'v' is basic */
static bool
la_var_is_basic(Tsimplex s, Tvar v)
{
  return ((Tvar_prop)table_get(s->vp, v->id))->basic != -1;
}

/*-----------------------------------------------------------------------*/

/* DC Returns the basic variable of the equation 'e' */
static Tvar
la_get_basic_var(Tsimplex s, Tequation e)
{
  if (e == NULL)
    return NULL;
  if (e->bmon == NULL)
    return NULL;
  return e->bmon->var;
}

/*-----------------------------------------------------------------------*/

/* DC Returns the coefficient of the basic variable in the equation 'e' */
static Tnumber
la_get_basic_coef(Tsimplex s, Tequation e)
{
  return e->bmon->coef; 
}

/*-----------------------------------------------------------------------*/

/* DC Returns the equation where 'bv' is the basic variable.
   PRE-CONDITION: bv is a basic variable */
static Tequation
la_get_basic_equation(Tsimplex s, Tvar bv)
{
  Tsigned index = ((Tvar_prop)table_get(s->vp, bv->id))->basic;
  assert(index >= 0);
  return (Tequation)table_get(s->eq, index); 
}

/*-----------------------------------------------------------------------*/

/* DC Creates a new monomial */
static Tmon
la_mon_new(Tnumber coef, Tvar_id var_id, Tequation e)
{
  Tmon m;
  MY_MALLOC(m, sizeof(struct TSmon));
  m->coef = number_new();
  number_cpy(m->coef, coef);
  m->var = la_var_new(var_id);
  m->e = e;
  return m;
}

/*-----------------------------------------------------------------------*/

/* DC Frees the monomial */
static void
la_mon_free(Tmon m)
{
  la_var_free(m->var);
  number_free(m->coef);
  free(m);
}

/*-----------------------------------------------------------------------*/

/* DC Compare 2 monomial and returns true if the first one is 'smaller' */
static bool
la_mon_less(Tmon a, Tmon b)
{
  return a->var->id < b->var->id;
}

/*-----------------------------------------------------------------------*/

/* DC Adds to a list, variable IDs from a list o monomials */

static void
la_list_add_mons(Tlist *res, Tlist lm)
{
  Tlist ptr = lm;
  if (ptr != NULL)
    do
      {
	Tvar_id i = ((Tmon)list_car(ptr))->var->id - 1;
	if (i >= 0)
	  *res = list_add(*res, (void*) i);
	ptr = list_cdr(ptr);
      }
    while (ptr != lm);
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if the list of monomials is at the begining */
static bool
la_list_mon_begin(Tlist l)
{
  return ((Tmon)list_car(l))->var->id == 0;
}

/*-----------------------------------------------------------------------*/

/* DC Removes the element 'ptr' of the list, updating the 'beginning' of the 
   list if it was the element removed. Returns true if 'ptr' is different of
   'begin' before removing and equal to it after removing; It also returns true
   when the remaining list is NULL. */
static bool
la_list_remove(Tlist *ptr, Tlist *begin)
{
  if (*ptr == *begin)
    {
      *ptr = list_remove(*ptr);
      *begin = *ptr;
      if (*ptr == NULL)
	return true;
    }
  else
    {
      *ptr = list_remove(*ptr);
      if (*ptr == *begin)
	return true;
    }
  return false;
}

/*-----------------------------------------------------------------------*/

/* DC Hash function for int */
static unsigned
int_hash (int n)
{
  return n;
}

/*-----------------------------------------------------------------------*/

/* DC Equal hash function for int */
static int
int_equal (void *a, void *b)
{
  return (intptr_t) a == (intptr_t) b;
}

/*-----------------------------------------------------------------------*/

/* DC Function that compare a pair used in a qsort, first by the Tnumber then by the int */
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
  else 
    return p1.second > p2.second ? 1 : -1;
}

/*-----------------------------------------------------------------------*/
/* Global functions                                                      */
/*-----------------------------------------------------------------------*/

/* DC Initializes */
void
la_init (void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_init()\n");
#endif
  Tvar_id const_var;
  
  /* DC Build simplex */
  MY_MALLOC (la_s, sizeof (struct TSsimplex));
  la_s->level = 0;
  la_s->consistent = true;
  la_s->conflict = NULL;
  la_s->sol = number_new();
  la_s->goal = NULL;
  la_s->eq = table_new (TABLE_INIT_SIZE, TABLE_INCREMENT);
  la_s->vp = table_new (TABLE_INIT_SIZE, TABLE_INCREMENT);
  la_s->disequalities = table_new (TABLE_INIT_SIZE, TABLE_INCREMENT);
  la_s->model_eq = table_new (TABLE_INIT_SIZE, TABLE_INCREMENT);
  la_s->model_conflict = table_new(TABLE_INIT_SIZE, TABLE_INCREMENT);
  la_var_id_init(la_s);
  la_s->search_model_equalities = false;
  la_s->cannot_find_solution = false;
  la_s->returned_eq = set_new ((TFcmp) la_equality_compare, (TFfree) NULL);

  history_init (la_s);
  
  /* DC first 'variable' is reserved to constant numbers */
  const_var = la_var_id_register(la_s, 0, LA_RATIONAL);
  assert(const_var == 0);
 
#ifdef DEBUG_LA
  /*la_do_tests();*/
#endif
}

/*-----------------------------------------------------------------------*/

/* DC Resets */
void
la_reset (void)
{
  Tvar_id const_var;

  la_s->level = 0;
  la_s->consistent = true;
  number_cpy(la_s->sol, number_zero);
  la_s->goal = NULL;
  la_s->search_model_equalities = false;
  la_s->cannot_find_solution = false;
  
  history_reset(la_s); 
  
  table_erase(la_s->eq);
  table_erase(la_s->vp);
  table_erase(la_s->disequalities);
  table_erase(la_s->model_eq);
  table_erase(la_s->model_conflict);
  set_erase(la_s->returned_eq);

  /* DC first 'variable' is reserved to constant numbers */
  la_var_id_reset(la_s);
  const_var = la_var_id_register(la_s, 0, LA_RATIONAL);
  assert(const_var == 0);
}

/*-----------------------------------------------------------------------*/

/* DC Finishes */
void
la_done (void)
{
  la_s->level = 0;
  history_done (la_s);
  
  number_free(la_s->sol);
  table_free(&la_s->eq);
  table_free(&la_s->vp);
  table_free(&la_s->disequalities);
  table_free(&la_s->model_eq);
  table_free(&la_s->model_conflict);
  set_free(&la_s->returned_eq);
  la_var_id_free(la_s);
  
  free(la_s);
}

/*-----------------------------------------------------------------------*/

/* DC Adds a equation to the problem.

 description:
 Adds a equation to the current set of constraints.
 Each position in the array corresponds to a monomial.
 The right side of the equation is always zero and
 the constant term is identified by variable_id zero.

 parameters:
 'size' is the number of monomials.
 'coef[]' are the coefficients of the monomials.
 'var_id[]' are the variable identifications for the monomials.
 'var_type[]' are the variable types {LA_INT, LA_RATIONAL}.
 'returns' a number that identifies this constraint.

 example:
 1 x + 2 y - 3 z + 7 = 0
 la_push_equation({1, 2, -3, 7}, {1, 2, 3, 0}, 4)
 */
int
la_push_equation (Tnumber coef[], Tvar_id var_id[], Tvar_kind var_type[],
	 Tunsigned size)
{
  Tequation e;
  bool one_var = false;
#ifdef DEBUG_LA
  fprintf(stderr, "la_push()\n");
#endif
  la_s->level++;
  if (la_consistent(la_s) == false)
    {
      la_equation_inc(la_s);
#ifdef DEBUG_LA
      la_simplex_print(la_s);
      fprintf(stderr, "la_push(): completed\n");
#endif
      return la_equation_size(la_s)-1;
    }
  la_check_var(la_s, var_id, var_type, size);
  e = la_equation_new(la_s, coef, var_id, size);
#ifdef DEBUG_LA
  fprintf(stderr, "Pushed equation: "); la_exp_print(e->le); printf("\n");
#endif
  table_push(la_s->eq, e);
  
  if (la_exp_is_all_var_int(e->le, la_s) &&
      !la_exp_has_int_solution(e->le, la_s))
    {
#ifdef DEBUG_LA
      fprintf(stderr, "LA Conflict. There is no integer solution!\n");
      fprintf(stderr, "Expression: "); la_exp_print(e->le); printf("\n");
      fprintf(stderr, "Explanation: "); la_exp_print(e->comb); printf("\n");
#endif
      history_status_changed(la_s);
      la_list_add_mons(&la_s->conflict, e->comb->mons);
      la_s->conflict =
	list_merge (la_s->conflict,
		    la_colect_explanation_of_fixed_variables(la_s, e->le));
      la_s->consistent = false;
      la_s->goal = NULL;
      la_equation_inc(la_s);
      history_equation_added(la_s);
#ifdef DEBUG_LA
      la_simplex_print(la_s);
      fprintf(stderr, "la_push(): completed\n");
#endif
      return la_equation_size(la_s)-1;
    }

  if (la_equation_has_one_variable(e))
    {
      one_var = true;
      la_equation_check_bound(la_s, e);
    }
  la_equation_normalize(la_s, e);
  if (one_var == false && la_equation_has_one_variable(e))
    {
      one_var = true;
      la_equation_check_bound(la_s, e);
    }
  la_s->goal = e;
  la_update_sol(la_s);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
#endif
  la_reach(la_s);
  if (one_var || la_s->consistent == false)
    la_equation_inc(la_s);
  else
    la_equation_add(la_s, e);
  history_equation_added(la_s);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
#endif

#ifdef DEBUG_LA
  fprintf(stderr, "la_push(): completed\n");
#endif

  return la_equation_size(la_s)-1;
}

/*-----------------------------------------------------------------------*/

/* DC Adds a inequality to the problem.

 description:
 Adds a inequality to the current set of constraints.
 Each position in the array corresponds to a monomial.
 The right side of the inequality is always zero and
 the constant term is identified by variable_id zero.

 parameters:
 'size' is the number of monomials.
 'coef[]' are the coefficients of the monomials.
 'var_id[]' are the variable identifications for the monomials.
 'var_type[]' are the variable types {LA_INT, LA_RATIONAL}.
 'returns' a number that identifies this constraint.

 example:
 1 x + 3 z - 4 w - 5 <= 0
 la_push_inequality({1, 3, -4, -5}, {1, 3, 4, 0}, 4)
*/
int
la_push_inequality (Tnumber coef[], Tvar_id var_id[], Tvar_kind var_type[],
	 Tunsigned size)
{
  Tequation e;
  bool one_var = false;
#ifdef DEBUG_LA
  fprintf(stderr, "la_push()\n");
#endif
  la_s->level++;
  if (la_consistent(la_s) == false)
    {
      la_equation_inc(la_s);
#ifdef DEBUG_LA
      la_simplex_print(la_s);
      fprintf(stderr, "la_push(): completed\n");
#endif
      return la_equation_size(la_s)-1;
    }

  la_check_var(la_s, var_id, var_type, size);
  e = la_equation_new(la_s, coef, var_id, size);
#ifdef DEBUG_LA
  printf("Pushed inequality: "); la_exp_print(e->le); printf("\n");
#endif
  table_push(la_s->eq, e);

  if (la_exp_is_all_var_int(e->le, la_s))
    {
      la_exp_round_down_inequality_of_integers(e, la_s);
      la_exp_round_down_inequality_of_integers(e, la_s);
    }

  /* DC If there is only one variable */
  if (la_equation_has_one_variable(e))
    {
      one_var = true;
      la_inequality_check_bound(la_s, e);
    }
  la_equation_normalize(la_s, e);

  if (one_var == false && la_equation_has_one_variable(e))
    {
      one_var = true;
      la_inequality_check_bound(la_s, e);
    }
  la_s->goal = e;
  la_update_sol(la_s);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
#endif
  la_minimize(la_s);
  if (one_var || la_s->consistent == false)
    la_equation_inc(la_s);
  else
    la_inequality_add(la_s, e);
  history_equation_added(la_s);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
  fprintf(stderr, "la_push(): completed\n");
#endif
  return la_equation_size(la_s) - 1;
}

/*-----------------------------------------------------------------------*/

/* DC Adds a disequality between two variables to the problem.

 description:
 Adds a disequality between two variables to the current set of constraints.
 Each position in the array corresponds to a monomial.
 For more information see examples.

 parameters:
 'var_id1' and 'var_id2' are the disequality variable identifications.
 'var_type1' and 'var_type2' are the variable types {LA_INT, LA_RATIONAL}.
 'returns' a number that identifies this constraint.

 example:
 x != z
 la_push_disequality(1, 3, LA_INT, LA_INT)

 */
int
la_push_disequality (Tvar_id var_id1, Tvar_id var_id2, Tvar_kind var_type1, Tvar_kind var_type2)
{
  Tvar_id var_ids[2];
#ifdef DEBUG_LA
  fprintf(stderr, "la_push()\n");
#endif
  la_s->level++;
  if (la_consistent(la_s) == false)
    {
      la_equation_inc(la_s);
#ifdef DEBUG_LA
      la_simplex_print(la_s);
      fprintf(stderr, "la_push(): completed\n");
#endif
      return la_equation_size(la_s)-1;
    }
  var_ids[0] = var_id1;
  var_ids[1] = var_id2;
  la_check_var(la_s, var_ids, (Tvar_kind[]){var_type1, var_type2}, 2);
  table_push(la_s->disequalities,
	     la_disequality_new(la_s, var_ids[0], var_ids[1]));
  table_push(la_s->eq, NULL);
  history_disequality_added(la_s);
#ifdef DEBUG_LA
  la_simplex_print(la_s);
  fprintf(stderr, "la_push(): completed\n");
#endif
  return la_equation_size(la_s) - 1;
}

/*-----------------------------------------------------------------------*/

/* DC Pops the last constraint pushed */
void
la_pop(void)
{
#ifdef DEBUG_LA  
  fprintf(stderr, "la_pop()\n");
#endif
    
  --la_s->level;
  history_backtrack (la_s);
  la_s->search_model_equalities = false;
  la_s->cannot_find_solution = false;

  /*fprintf(stderr, "la_pop(), constraints = %d, level = %d, disequalities = %d\n", table_length(la_s->eq), la_s->level, table_length(la_s->disequalities));*/
  
#ifdef DEBUG_LA  
  la_simplex_print(la_s);
#endif  
}

/*-----------------------------------------------------------------------*/

/* DC Returns the current state of concistency.
   The consistency check itself is done incrementally during the 'push', 
   so this function returns the current status in constant time.
   After using 'la_check', model equalities can be extracted.
   returns 0 if inconcistent, 1 otherwise */
Tstatus
la_solve(void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_solve()\n");
#endif
  bool ret = la_adjust_model(la_s, 0);
  if (la_s->cannot_find_solution)
    return UNDEF;
  if (ret == false)
    {
      history_status_changed(la_s);
      la_s->conflict = NULL;
      la_s->consistent = false;
      la_s->goal = NULL;
    }
  la_s->search_model_equalities = true;
#ifdef DEBUG_LA
  fprintf(stderr, "la_solve(finish)\n");
  la_simplex_print(la_s);
#endif  
  return (la_consistent(la_s) ? SAT : UNSAT);
}

/*-----------------------------------------------------------------------*/

/* DC Returns the current state of consistency */
Tstatus la_status (void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_status()\n");
#endif
#ifdef PRINT_LA
  if (la_consistent(la_s) == false)
    la_simplex_print(la_s);
#endif
  return (la_consistent(la_s) ? SAT : UNSAT);
}

/*-----------------------------------------------------------------------*/

/* DC Returns the ids of the constraints that are inconsistent.
   It should be used when la_solve() returns false.
 
   out parameters:
   'constrant_id' are the ids from the constraints that produced
     the inconsistency.
   'size' is the number of elements in 'constrant_id'.
 */
Tlist
la_conflict (void)
{
  Tlist ret = NULL;
#ifdef DEBUG_LA
  fprintf(stderr, "la_conflict()\n");
#endif
  assert(la_s->consistent == false);
  /* DC If the unsatisfiability was detected previously, but no (minimal)
     conflict set was collected then get as conflict all the constraints. */
  if (la_s->conflict == NULL)
    {
      intptr_t i;
      for (i = 0; i < table_length(la_s->eq); ++i)
	ret = list_add(ret, (void*)i);
      return ret;
    }
  return list_cpy(la_s->conflict);
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if there is a deduced equality that was not poped yet.
   Deduced equalities are poped using 'la_eq_queue_pop' */
bool
la_eq_queue_empty (void)
{
  return true;
}

/*-----------------------------------------------------------------------*/

/* DC Returns one deduced equality if there is some to return.
   Each equality is returned only once.

   out parameters:
   'var_id1' and 'var_id2' are the original ids
     from the variables that form the deduced equality.
   'premisses' are the ids from the constraints that produced the equality.
 */
void 
la_eq_queue_pop (Tvar_id * id1, Tvar_id * id2, Tlist * premisses)
{
  /* DC No equality is been deduced so far */
  assert(false);
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if there is a model equality that was not poped yet.
   Model equalities are poped using 'la_eq_queue_pop' */
bool
la_model_eq_queue_empty (void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_model_eq_queue_empty()\n");
#endif
  if (la_status() == UNSAT)
    return true;
  if (la_s->search_model_equalities)
    {
      la_search_model_equalities(la_s);
      la_s->search_model_equalities = false;
    }
  return !table_empty(la_s->model_conflict) || table_empty(la_s->model_eq);
}

/*-----------------------------------------------------------------------*/

/* DC Returns one model equality if there is some to return.
   Each equality is returned only once.

   out parameters:
   'var_id1' and 'var_id2' are the original ids
     from the variables that form the model equality.
*/
void
la_model_eq_queue_pop (Tvar_id * var_id1, Tvar_id * var_id2)
{
  Tequality e;
  assert(!table_empty(la_s->model_eq));

#ifdef DEBUG_LA
  fprintf(stderr, "la_model_eq_queue_pop()\n");
#endif
  
  e = (Tequality) table_pop(la_s->model_eq);
  *var_id1 = ((Tvar_prop) table_get(la_s->vp, e->var_id1))->user_id;
  *var_id2 = ((Tvar_prop) table_get(la_s->vp, e->var_id2))->user_id;
}

/*-----------------------------------------------------------------------*/

/* DC Returns true if there is a conflict between the current model and a 
   disequality. The conflicting disequalities are poped using 'la_model_conflict_pop' */
bool
la_model_has_conflict (void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_model_has_conflict()\n");
#endif
  if (la_status() == UNSAT)
    return false;
  return !table_empty(la_s->model_conflict);
}

/*-----------------------------------------------------------------------*/

/* DC Returns one disequality that is conflicting with the current model. */
int
la_model_conflict_pop (void)
{
#ifdef DEBUG_LA
  fprintf(stderr, "la_model_conflict_pop()\n");
#endif
  
  assert(!table_empty(la_s->model_conflict));
  
  return (((Tdisequality)table_pop(la_s->model_conflict))->id)-1;
}
