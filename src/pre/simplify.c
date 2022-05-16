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
  Module for simplifying formulas and terms
  --------------------------------------------------------------
*/

#include <stdlib.h>

#include "general.h"
#include "statistics.h"

#include "DAG-print.h"
#include "DAG.h"
#include "DAG-tmp.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "number.h"
#include "polarities.h"
#include "recursion.h"
#include "simplify.h"
#include "simp-formula-sat.h"

#define symb_misc(s) DAG_symb_misc(s)
#define symb_interpreted(s) DAG_symb_interpreted(s)
#define symb_set_misc(s,v) DAG_symb_set_misc(s,v)
#define symb_name(s) DAG_symb_name(s)
#define symb_of_ptr(p) DAG_symb_of_ptr(p)
#define ptr_of_symb(s) DAG_ptr_of_symb(s)
#define symb_type(s) DAG_symb_type(s)

/* #define DEBUG_SIMPLIFY_AC */
/* #define SIMP_STAT */

#ifdef SIMP_STAT

static int stat_AC;		/* AC */
static int stat_unary_nihil_twice;	/* OO(A) -> A */
static int stat_reflexivity;	/* a O a -> TRUE */
static int stat_irreflexivity;	/* a O a -> FALSE */
static int stat_neutral;	/* a O b O c, c -> a O b */
static int stat_idempotent;	/* a O a O b -> a O b */
static int stat_absorbing;	/* a O ABSORBING O b -> ABSORBING */
static int stat_and;		/* FALSE AND A -> FALSE
				   (AND ) -> TRUE */
static int stat_or;		/* TRUE OR A -> TRUE
				   (OR ) -> FALSE */
static int stat_not;		/* NOT FALSE -> TRUE, NOT TRUE -> FALSE */
static int stat_implies;	/* (NOT A) => (NOT B) --> B => A
				   FALSE => A, A => TRUE --> TRUE
				   TRUE => A --> A
				   A => FALSE --> NOT A
				   A => A --> TRUE
				   (NOT A) => A --> A
				   A => NOT A --> NOT A */
static int stat_equiv;		/* (NOT A) EQV (NOT B) --> B EQV A
				   A EQV A --> TRUE
				   A EQV NOT A, NOT A EQV A --> FALSE
				   TRUE EQV A --> A
				   A EQV TRUE --> A
				   FALSE EQV A --> NOT A
				   A EQV FALSE --> NOT A */
static int stat_ite;		/* if T then c1 else c2 --> c1
				   if F then c1 else c2 --> c2
				   if c then TRUE else FALSE --> c 
				   if c then FALSE else TRUE --> NOT c
				   if c1 then c2 else c2 --> c2
				   if c1 then T else c2 --> c1 OR c2
				   if c1 then c2 else F --> c1 AND c2
				   if c1 then F else c2 --> NOT c1 AND c2
				   if c1 then c2 else T --> NOT c1 OR c2
				   if NOT c1 then c2 else c3 -->
				   if c1 then c3 else c2 */
static int stat_eq;		/* a1 = a2, a1 a2 int
				   e = e --> TRUE */
static int stat_less;		/* a1 < a2, a1 a2 int
				   e < e --> FALSE */
static int stat_leq;		/* a1 <= a2, a1 a2 int
				   e <= e --> TRUE */
static int stat_fite;		/* ite(T,e1,e2) --> e1
				   ite(F,e1,e2) --> e2
				   ite(c,e,e) --> e
				   ite(NOT c,e1,e2) --> ite(c,e2,e1) */
static int stat_plus;		/* 1 + 1 -> 2 */
static int stat_minus;		/* a1 - a2, a1 a2 int
				   e - 0 -> e
				   0 - e -> -e */
static int stat_uminus;		/* - a1 -> -a1
                                   - - e -> e */
static int stat_div;            /* (/ 2 4) -> 1/2 
                                   (/ t t) -> 1
                                   (/ t 1) -> t */
static int stat_prod;
static int stat_arith;		/* arithmetic equalities (unsat/valid) */
static int stat_itelift;	/* e1 = ite (c, e2, e3) --> if c then... */
static int stat_subst;		/* unary clauses, substitutions */

static int stat_tuple_pat;       /* ! x1...xn (/\ xi = ti <=> /\ xi = vi) -> /\ ti = vi */

#define STAT_NEW( A, B ) stat_ ## A = stats_counter_new(#A, B, "%4d")
#define STAT_INC( A ) stats_counter_inc(stat_ ## A )
#else
#define STAT_NEW( A, B ) ;
#define STAT_INC( A ) ;
#endif

static TDAG simplify_node(TDAG src);
static void simplify_AC(TDAG src);

/*
  --------------------------------------------------------------
  General simplification functions
  --------------------------------------------------------------
*/

/**
   \pre symb is an associative and commutative operator */
static unsigned
simplify_AC_count_args(Tsymb symb, TDAG src)
{
  unsigned result;
  if (DAG_flag(src)) return 0;
  DAG_flag_set(src, 1);
  if (DAG_symb(src) == symb)
    {
      unsigned i;
      result = 0;
      for (i = 0; i < DAG_arity(src); ++i)
	result += simplify_AC_count_args(symb, DAG_arg(src, i));
    }
  else
    result = 1;
  return result;
}

/*--------------------------------------------------------------*/

/**
   \pre symb is an associative and commutative operator */
static void
simplify_AC_collect_args(Tsymb symb, TDAG src, TDAG ** PPDAG)
{
  if (!DAG_flag(src)) return;
  DAG_flag_set(src, 0);
  if (DAG_symb(src) == symb)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(src); ++i)
	simplify_AC_collect_args(symb, DAG_arg(src, i), PPDAG);
    }
  else
    {
      **PPDAG = src;
      *PPDAG += 1;
    }
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is not an associative and commutative operator */
static TDAG
simplify_AC_args(TDAG src)
{
  TDAG result;
  unsigned i;
  bool changed;

  assert(!DAG_Pflag(src));
  changed = false;
  for (i = 0; i < DAG_arity(src); ++i)
    {
      simplify_AC(DAG_arg(src, i));
      changed |= (DAG_arg(src, i) != DAG_of_ptr(DAG_Pflag(DAG_arg(src, i))));
    }
  if (changed)
    {
      TDAG * PDAG;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); ++i)
	PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(src, i)));
      result = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
    }
  else
    result = src;
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_args\n*** src = %D\n*** result = %D\n", src, result);
#endif
  return result;
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is an associative and commutative operator
   \brief The simplifications performed are illustrated by the
   following examples, where f is an AC symbol with idempotence:
   * (f (f x1 (f x2 x3) x4) -> (f x1 x2 x3 x4)
   * (f x1 x1 x2) -> (f x1 x2)
   * (f x1 x1) -> x1
   \obs we do not worry about commutativity actually */
static void
simplify_AC_aux_AC(TDAG src)
{
  TDAG DAG0, DAG1;
  unsigned new_arity, i;
  int changed;

#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n", src);
#endif
  assert(!DAG_Pflag(src));

  new_arity = simplify_AC_count_args(DAG_symb(src), src);
  changed = (DAG_arity(src) != new_arity);
  for (i = 0; i < DAG_arity(src) && !changed; ++i)
    changed |= (DAG_symb(src) == DAG_symb(DAG_arg(src, i)));

  if (!changed)
    {
      DAG_reset_flag(src);
      DAG0 = DAG_dup(src);
    }
  else
    {
      TDAG * ptr;
      TDAG * PDAG;
      STAT_INC(AC);
      MY_MALLOC(PDAG, new_arity * sizeof(TDAG));
      ptr = PDAG;
      simplify_AC_collect_args(DAG_symb(src), src, &ptr);
      if (new_arity == 1)
	{
	  DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(PDAG[0])));
	  free(PDAG);
	  return;
	}
      DAG0 = DAG_dup(DAG_new(DAG_symb(src), new_arity, PDAG));
    }

  /* DAG0 is result of applying simplification to src */
  assert(DAG_symb(DAG0) == DAG_symb(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n *** DAG0 = %D\n", src, DAG0);
#endif
  if (DAG_Pflag(DAG0))
    {
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG_of_ptr(DAG_Pflag(DAG0)))));
      DAG_free(DAG0);
      return;
    }

  DAG1 = DAG_dup(simplify_AC_args(DAG0));
  DAG_free(DAG0);

  if (DAG_Pflag(DAG1))
    {
      assert(!DAG_Pflag(src));
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG_of_ptr(DAG_Pflag(DAG1)))));
      DAG_free(DAG1);
      return;
    }

  /* DAG1 is result of applying simplification to DAG0 descendants */
  assert(DAG_symb(DAG1) == DAG_symb(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n *** DAG1 = %D\n", src, DAG1);
#endif
  changed = 0;
  for (i = 0; i < DAG_arity(DAG1); ++i)
    changed |= (DAG_symb(src) == DAG_symb(DAG_arg(DAG1, i)));
  assert(!DAG_Pflag(src));
  if (changed)
    {
      TDAG * ptr;
      TDAG * PDAG;
      TDAG tmp;
      STAT_INC(AC);
      new_arity = simplify_AC_count_args(DAG_symb(DAG1), DAG1);
      MY_MALLOC(PDAG, new_arity * sizeof(TDAG));
      ptr = PDAG;
      simplify_AC_collect_args(DAG_symb(src), DAG1, &ptr);
      assert(ptr - PDAG == new_arity);
      if (new_arity == 1)
	{
	  DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(PDAG[0])));
	  free(PDAG);
	  DAG_free(DAG1);
	  return;
	}
      qsort(PDAG, new_arity, sizeof(TDAG), (TFcmp) DAG_cmp_q);
      tmp = DAG_dup(DAG_new(DAG_symb(DAG1), new_arity, PDAG));
      DAG_Pflag_set(src, DAG_ptr_of(tmp));
    }
  else
    DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG1)));

  DAG_free(DAG1);
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n*** src = %D\n*** DAG_Pflag(src) = %D\n",
		  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is not an associative and commutative operator */
static void
simplify_AC_aux_not_AC(TDAG src)
{
  TDAG tmp;
  assert(!DAG_Pflag(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_not_AC\n*** src = %D\n", src);
#endif
  tmp = DAG_dup(simplify_AC_args(src));
  DAG_Pflag_set(src, DAG_ptr_of(tmp));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_not_AC\n*** src = %D *** DAG_Pflag(src) = %D\n",
		  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is an associative and commutative operator */
static void
simplify_AC(TDAG src)
{
  if (DAG_Pflag(src))
    return;
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC\n *** src = %D\n", src);
#endif
  if (DAG_symb(src) != CONNECTOR_OR && DAG_symb(src) != CONNECTOR_AND)
    simplify_AC_aux_not_AC(src);
  else
    simplify_AC_aux_AC(src);
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC\n *** src = %D *** DAG_Pflag(src) = %D\n",
		  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

#if 0
static TDAG
simplify_AC(TDAG src)
/* PF For AC operators
   Examples * + AND OR */
{
  usigned i, j, k, new_arity = 0;
  TDAG *DAGs, dest;
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_symb(src) == DAG_symb(DAG_arg(src, i)))
      {
	new_arity += DAG_arity(DAG_arg(src, i));
	j++;
      }
  if (!j)
    return src;
  STAT_INC(AC);
  new_arity += DAG_arity(src) - j;
  MY_MALLOC(DAGs, new_arity * sizeof(TDAG));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_symb(src) == DAG_symb(DAG_arg(src, i)))
      for (k = 0; k < DAG_arity(DAG_arg(src, i)); k++)
	DAGs[j++] = DAG_arg(DAG_arg(src, i), k);
    else
      DAGs[j++] = DAG_arg(src, i);
  assert(j == new_arity);
  dest = DAG_dup(DAG_new(DAG_symb(src), new_arity, DAGs));
  DAG_free(src);
  return dest;
}
#endif

/*--------------------------------------------------------------*/

static TDAG
simplify_unary_nihil_twice(TDAG src)
/* PF Unary operator DAG_symb(src) annihilates when applied twice
   Examples (- (- a)) -> a
   (not (not p)) -> p */
{
  TDAG dest;
  if (DAG_arity(src) != 1 ||
      DAG_arity(DAG_arg0(src)) != 1 || DAG_symb(src) != DAG_symb(DAG_arg0(src)))
    return src;
  STAT_INC(unary_nihil_twice);
  dest = DAG_dup(DAG_arg0(DAG_arg0(src)));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/* PF Binary operator is TRUE if both arguments are equal
   Examples a = a -> TRUE
   a <= a -> TRUE */
static TDAG
simplify_reflexivity(TDAG src)
{
  if (DAG_arity(src) != 2 || DAG_arg0(src) != DAG_arg1(src))
    return src;
  STAT_INC(reflexivity);
  DAG_free(src);
  return DAG_dup(DAG_TRUE);
}

/*--------------------------------------------------------------*/

/* PF Binary operator is FALSE if both arguments are equal
   Examples a != a -> FALSE
   a < a -> FALSE */
static TDAG
simplify_irreflexivity(TDAG src)
{
  if (DAG_arity(src) != 2 || DAG_arg0(src) != DAG_arg1(src))
    return src;
  STAT_INC(irreflexivity);
  DAG_free(src);
  return DAG_dup(DAG_FALSE);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontain
   \brief eliminate every direct subDAG of src equal to sub
   \param src the term
   \param sub the subterm to eliminate
   \remark useful for eliminating TRUE in conjunction, FALSE in disjunction,
   0 in sum, 1 in products */
static TDAG
simplify_neutral(TDAG src, TDAG sub)
{
  unsigned i, j;
  unsigned n = DAG_arity(src);
  TDAG dest, *DAGs;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) == sub)
      n--;
  if (n == DAG_arity(src))
    return src;
  STAT_INC(neutral);
  MY_MALLOC(DAGs, n * sizeof(TDAG *));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) != sub)
      DAGs[j++] = DAG_arg(src, i);
  assert(j == n);
  dest = DAG_dup(DAG_new(DAG_symb(src), n, DAGs));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe
   \brief find if subterm is a direct argument (or subterm) of src
   \remark useful for simplifying TRUE in disjunction, FALSE in conjunction,
   ZERO in products */
static bool
find_arg(TDAG src, TDAG subterm)
{
  unsigned i;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) == subterm)
      return true;
  return false;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief eliminate duplicate args and sort
   \param[in] src the DAG
   \return the simplified DAG
   \remark destructive
   \remark Useful for A AND A AND B -> A AND B and A OR A OR B -> A OR B */
static int
DAG_compar(TDAG * PDAG0, TDAG * PDAG1)
{
  if ((DAG_symb(*PDAG0) != CONNECTOR_NOT &&
       DAG_symb(*PDAG1) != CONNECTOR_NOT) ||
      (DAG_symb(*PDAG0) == CONNECTOR_NOT &&
       DAG_symb(*PDAG1) == CONNECTOR_NOT))
    return (int)*PDAG0 - (int)*PDAG1;
  if (DAG_symb(*PDAG0) == CONNECTOR_NOT)
    return (int)DAG_arg0(*PDAG0) - (int)(*PDAG1);
  return (int)(*PDAG0) - (int)DAG_arg0(*PDAG1);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief eliminate duplicate args and sort
   \param[in] src the DAG
   \return the simplified DAG
   \remark destructive
   \remark Useful for A AND A AND B -> A AND B and A OR A OR B -> A OR B */
static TDAG
simplify_ACidem(TDAG src)
{
  unsigned i, j;
  unsigned n = DAG_arity(src);
  TDAG dest, *PDAG;
  if (!n)
    return src;
  MY_MALLOC(PDAG, n * sizeof(TDAG));
  memcpy(PDAG, DAG_args(src), n * sizeof(TDAG));
  qsort(PDAG, n, sizeof(TDAG), (TFcmp) DAG_compar);
  for (i = 1, j = 0; i < n; i++)
    if (PDAG[i] != PDAG[j])
      PDAG[++j] = PDAG[i];
  j++;
  MY_REALLOC(PDAG, j * sizeof(TDAG));
  dest = DAG_dup(DAG_new(DAG_symb(src), j, PDAG));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief find if there is a complementary pair of subterms
   \param[in] src the DAG
   \return true if there exists a complementary pair of subterms
   \pre arguments should be sorted, e.g. with simplify_ACidem
   \remark Useful for A and not A, A or not A */
static bool
find_comp(TDAG src)
{
  unsigned i;
  unsigned n = DAG_arity(src);
  for (i = 1; i < n; i++)
    if ((DAG_symb(DAG_arg(src, i)) == CONNECTOR_NOT &&
	 DAG_arg0(DAG_arg(src, i)) == DAG_arg(src, i - 1)) ||
	(DAG_symb(DAG_arg(src, i - 1)) == CONNECTOR_NOT &&
	 DAG_arg0(DAG_arg(src, i - 1)) == DAG_arg(src, i)))
      return true;
  return false;
}

/*
  --------------------------------------------------------------
  lifting ite
  --------------------------------------------------------------
*/

static TDAG
simplify_lift_ite(TDAG src)
     /* PF apply simple case where ite function can be lifted to
        ite connector without risk of explosion:
        e1 = ite (c, e2, e3) --> if c then e1 = e2 else e1 = e3 */
{
  TDAG dest, tmp1, tmp2, tmp3, tmp4;
  if (DAG_symb(src) != PREDICATE_EQ ||
      (DAG_symb(DAG_arg0(src)) != FUNCTION_ITE &&
       DAG_symb(DAG_arg1(src)) != FUNCTION_ITE) ||
      (DAG_symb(DAG_arg0(src)) == FUNCTION_ITE &&
       DAG_symb(DAG_arg1(src)) == FUNCTION_ITE))
    return src;
  STAT_INC(itelift);
  if (DAG_symb(DAG_arg0(src)) == FUNCTION_ITE)
    {
      tmp1 = DAG_arg0(src);
      tmp2 = DAG_arg1(src);
    }
  else
    {
      tmp1 = DAG_arg1(src);
      tmp2 = DAG_arg0(src);
    }
  tmp3 = simplify_node(DAG_dup(DAG_eq(DAG_arg(tmp1, 1), tmp2)));
  tmp4 = simplify_node(DAG_dup(DAG_eq(DAG_arg(tmp1, 2), tmp2)));
  dest = DAG_dup(DAG_ite(DAG_arg(tmp1, 0), tmp3, tmp4));
  DAG_free(src);
  DAG_free(tmp3);
  DAG_free(tmp4);
  return simplify_node(dest);
}

/*
  --------------------------------------------------------------
  Specialized simplification functions
  --------------------------------------------------------------
*/

static TDAG
simplify_and(TDAG src)
{
  src = simplify_neutral(src, DAG_TRUE);
  src = simplify_ACidem(src);
  if (find_arg(src, DAG_FALSE) || find_comp(src))
    {
      STAT_INC(and);
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (!DAG_arity(src))
    {
      STAT_INC(and);
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  if (DAG_arity(src) == 1)
    {
      TDAG dest;
      dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_or(TDAG src)
{
  /* A_1 OR ... A_j OR FALSE OR A_{j+1} OR ... A_n --> A_1 OR ... A_n */
  src = simplify_neutral(src, DAG_FALSE);
  src = simplify_ACidem(src);
  if (find_arg(src, DAG_TRUE) || find_comp(src))
    {
      STAT_INC(or);
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  if (!DAG_arity(src))
    {
      STAT_INC(or);
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (DAG_arity(src) == 1)
    {
      TDAG dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_not(TDAG src)
{
  /* NOT NOT A --> A */
  src = simplify_unary_nihil_twice(src);
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      /* NOT FALSE --> TRUE */
      if (DAG_arg0(src) == DAG_FALSE)
	{
	  STAT_INC(not);
	  DAG_free(src);
	  return DAG_dup(DAG_TRUE);
	}
      /* NOT TRUE --> FALSE */
      if (DAG_arg0(src) == DAG_TRUE)
	{
	  STAT_INC(not);
	  DAG_free(src);
	  return DAG_dup(DAG_FALSE);
	}
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_implies(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_IMPLIES);
  /* (NOT A) => (NOT B) --> B => A */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT &&
      DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT)
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_implies(DAG_arg0(DAG_arg1(src)), DAG_arg0(DAG_arg0(src))));
      DAG_free(src);
      src = dest;
    }
  /* FALSE => A, A => TRUE --> TRUE */
  if (DAG_arg0(src) == DAG_FALSE || DAG_arg1(src) == DAG_TRUE)
    {
      STAT_INC(implies);
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* TRUE => A --> A */
  else if (DAG_arg0(src) == DAG_TRUE)
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* A => FALSE --> NOT A */
  else if (DAG_arg1(src) == DAG_FALSE)
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_not(DAG_arg0(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  /* A => A --> TRUE */
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(implies);
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* (NOT A) => A --> A */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT &&
      DAG_arg0(DAG_arg0(src)) == DAG_arg1(src))
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* A => NOT A --> NOT A */
  if (DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT &&
      DAG_arg0(src) == DAG_arg0(DAG_arg1(src)))
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* (P => Q) => Q --> P OR Q */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_IMPLIES &&
      DAG_arg1(DAG_arg0(src)) == DAG_arg1(src))
    {
      STAT_INC(implies);
      dest = DAG_dup(DAG_or2(DAG_arg0(DAG_arg0(src)), DAG_arg1(src)));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_equiv(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_EQUIV);
  /* (NOT A) EQV (NOT B) --> B EQV A */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT &&
      DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT)
    {
      STAT_INC(equiv);
      dest = DAG_dup(DAG_equiv(DAG_arg0(DAG_arg0(src)), DAG_arg0(DAG_arg1(src))));
      DAG_free(src);
      src = dest;
    }
  /* A EQV A --> TRUE */
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(equiv);
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* A EQV NOT A, NOT A EQV A --> FALSE */
  if ((DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT && DAG_arg0(DAG_arg0(src)) == DAG_arg1(src)) ||
      (DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT && DAG_arg0(DAG_arg1(src)) == DAG_arg0(src)))
    {
      STAT_INC(equiv);
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  /* TRUE EQV A --> A */
  if (DAG_arg0(src) == DAG_TRUE)
    {
      STAT_INC(equiv);
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* A EQV TRUE --> A */
  if (DAG_arg1(src) == DAG_TRUE)
    {
      STAT_INC(equiv);
      dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  /* FALSE EQV A --> NOT A */
  if (DAG_arg0(src) == DAG_FALSE)
    {
      STAT_INC(equiv);
      dest = DAG_dup(DAG_not(DAG_arg1(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  /* A EQV FALSE --> NOT A */
  if (DAG_arg1(src) == DAG_FALSE)
    {
      STAT_INC(equiv);
      dest = DAG_dup(DAG_not(DAG_arg0(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  return src;
}

/*--------------------------------------------------------------*/

#define IF(DAG) DAG_arg0(DAG)
#define THEN(DAG) DAG_arg1(DAG)
#define ELSE(DAG) DAG_arg(DAG,2)
static TDAG
simplify_ite(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_ITE);
  /* IF TRUE THEN A ELSE B --> A */
  if (IF(src) == DAG_TRUE)
    {
      STAT_INC(ite);
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* IF FALSE THEN A ELSE B --> B */
  if (IF(src) == DAG_FALSE)
    {
      STAT_INC(ite);
      dest = DAG_dup(ELSE(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN TRUE ELSE FALSE --> C */
  if (THEN(src) == DAG_TRUE && ELSE(src) == DAG_FALSE)
    {
      STAT_INC(ite);
      dest = DAG_dup(IF(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN FALSE ELSE TRUE --> NOT C */
  if (THEN(src) == DAG_FALSE && ELSE(src) == DAG_TRUE)
    {
      STAT_INC(ite);
      dest = DAG_dup(DAG_not(IF(src)));
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN A ELSE A --> A */
  if (THEN(src) == ELSE(src))
    {
      STAT_INC(ite);
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN TRUE ELSE B --> C OR B */
  if (THEN(src) == DAG_TRUE)
    {
      STAT_INC(ite);
      dest = DAG_dup(DAG_or2(IF(src), ELSE(src)));
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN A ELSE FALSE --> C AND A */
  if (ELSE(src) == DAG_FALSE)
    {
      STAT_INC(ite);
      dest = DAG_dup(DAG_and2(IF(src), THEN(src)));
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN FALSE ELSE B --> NOT C AND B */
  if (THEN(src) == DAG_FALSE)
    {
      TDAG tmp;
      STAT_INC(ite);
      tmp = simplify_node(DAG_dup(DAG_not(IF(src))));
      dest = DAG_dup(DAG_and2(tmp, ELSE(src)));
      DAG_free(tmp);
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN A ELSE TRUE --> NOT C OR A */
  if (ELSE(src) == DAG_TRUE)
    {
      TDAG tmp;
      STAT_INC(ite);
      tmp = simplify_node(DAG_dup(DAG_not(IF(src))));
      dest = DAG_dup(DAG_or2(tmp, THEN(src)));
      DAG_free(tmp);
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF NOT C THEN A ELSE B --> IF C THEN B ELSE A */
  if (DAG_symb(IF(src)) == CONNECTOR_NOT)
    {
      STAT_INC(ite);
      dest = DAG_dup(DAG_ite(DAG_arg0(IF(src)), ELSE(src), THEN(src)));
      DAG_free(src);
      return dest;
    }
  return src;
}
#undef IF
#undef THEN
#undef ELSE
                     
/*--------------------------------------------------------------*/

static TDAG
simplify_eq(TDAG src)
{
  if (DAG_is_integer(DAG_arg0(src)) && DAG_is_integer(DAG_arg1(src)))
    {
      TDAG dest =
	(strcmp(symb_name(DAG_symb(DAG_arg0(src))), 
		symb_name(DAG_symb(DAG_arg1(src)))) == 0) ?
	DAG_TRUE : DAG_FALSE;
      STAT_INC(eq);
      DAG_free(src);
      src = DAG_dup(dest);
    }
  else
    src = simplify_reflexivity(src);
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_less(TDAG src)
{
  if (DAG_is_integer(DAG_arg0(src)) && DAG_is_integer(DAG_arg1(src)))
    {
      Tnumber n0 = number_new(), n1 = number_new();
      TDAG dest;
      
      number_from_DAG(n0, DAG_arg0(src));
      number_from_DAG(n1, DAG_arg1(src));
      dest = number_less(n0, n1) ? DAG_TRUE : DAG_FALSE;
      STAT_INC(less);
      DAG_free(src);
      src = DAG_dup(dest);
      number_free(n0);
      number_free(n1);
    }
  src = simplify_irreflexivity(src);
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_leq(TDAG src)
{
  if (DAG_is_integer(DAG_arg0(src)) && DAG_is_integer(DAG_arg1(src)))
    {
      Tnumber n0 = number_new(), n1 = number_new();
      TDAG dest;
      
      number_from_DAG(n0, DAG_arg0(src));
      number_from_DAG(n1, DAG_arg1(src));
      dest = number_leq(n0, n1) ? DAG_TRUE : DAG_FALSE;
      STAT_INC(leq);
      DAG_free(src);
      src = DAG_dup(dest);
      number_free(n0);
      number_free(n1);
    }
  src = simplify_reflexivity(src);
  return src;
}

/*--------------------------------------------------------------*/

#define IF(DAG) DAG_arg0(DAG)
#define THEN(DAG) DAG_arg1(DAG)
#define ELSE(DAG) DAG_arg(DAG, 2)

static TDAG
simplify_fite(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == FUNCTION_ITE);
  /* ITE TRUE T1 T2 --> T1 */
  if (IF(src) == DAG_TRUE)
    {
      STAT_INC(fite);
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* ITE FALSE T1 T2 --> T1 */
  if (IF(src) == DAG_FALSE)
    {
      STAT_INC(fite);
      dest = DAG_dup(ELSE(src));
      DAG_free(src);
      return dest;
    }
  /* ITE C T1 T1 --> T1 */
  if (THEN(src) == ELSE(src))
    {
      STAT_INC(fite);
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* ITE NOT C T1 T2 --> ITE C T2 T1 */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT)
    {
      STAT_INC(fite);
      dest = DAG_dup(DAG_new_args(FUNCTION_ITE, DAG_arg0(IF(src)),
				  ELSE(src), THEN(src), DAG_NULL));
      DAG_free(src);
      src = dest;
    }
  return src;
}
#undef IF
#undef ELSE
#undef THEN

/*--------------------------------------------------------------*/

static TDAG
simplify_arith(TDAG src, Tnumber neutral, Tnumber (* op)(Tnumber, Tnumber, Tnumber))
{
  unsigned i;
  unsigned resize = 0;
  Tnumber acc;

  acc = number_new();
  number_cpy(acc, neutral);
  for (i = 0; i < DAG_arity(src); ++i)
    {
      Tnumber number = number_new();
      if (DAG_is_number(DAG_arg(src, i)))
	{
	  number_from_DAG(number, DAG_arg(src, i));
	  op(acc, acc, number);
	  resize += 1;
	}
      number_free(number);
    }
  if (resize)
    {
      unsigned arity = DAG_arity(src) - resize;
      TDAG * PDAG;
      TDAG * PDAG1;
      TDAG dest;
      STAT_INC(plus);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      if (arity == 0)
	{
	  dest = DAG_dup(number_to_DAG(acc));
          DAG_free(src);
	  number_free(acc);
          return dest;
	}
      if (!number_equal(acc, neutral))
	arity += 1;
      if (arity == 1)
	{
	  assert(number_equal(acc, neutral));
	  for (i = 0; i < DAG_arity(src); ++i)
	    if (!DAG_is_number(DAG_arg(src, i)))
	      break;
	  assert(i < DAG_arity(src));
	  dest = DAG_dup(DAG_arg(src, i));
	}
      else
	{
	  MY_MALLOC(PDAG, arity * sizeof(TDAG));
	  PDAG1 = PDAG;
	  if (!number_equal(acc, neutral))
	    *PDAG1++ = number_to_DAG(acc);
	  for (i = 0; i < DAG_arity(src); ++i)
	    if (!DAG_is_number(DAG_arg(src, i)))
	      *PDAG1++ = DAG_arg(src, i);
	  dest = DAG_dup(DAG_new(DAG_symb(src), arity, PDAG));
	}
      DAG_free(src);
      number_free(acc);
      return dest;
    }
  number_free(acc);
  return src;
}
/*--------------------------------------------------------------*/

static TDAG
simplify_sum(TDAG src)
{
  src = simplify_arith(src, number_zero, number_add);
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_prod(TDAG src)
{
  if (find_arg(src, DAG_ZERO))
    {
      DAG_free(src);
      return DAG_dup(DAG_ZERO);
    }
  src = simplify_arith(src, number_one, number_mul);
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_minus(TDAG src)
{
  TDAG dest = DAG_NULL;
  if (DAG_arity(src) != 2)
    my_error("simplify_minus: strange arity for src\n");

  /* DD with a GMP-like API */

  /* (- num1 num2) -> num1-num2 */
  if (DAG_is_number(DAG_arg0(src)) && DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand1, operand2, difference;
      STAT_INC(minus);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      operand1 = number_new();
      operand2 = number_new();
      difference = number_new();
      number_from_DAG(operand1, DAG_arg0(src));
      number_from_DAG(operand2, DAG_arg1(src));
      number_sub(difference, operand1, operand2);
      dest = DAG_dup(number_to_DAG(difference));
      number_free(difference);
      number_free(operand1);
      number_free(operand2);
      DAG_free(src);
      return dest;
    }
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(minus);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      DAG_free(src);
      return DAG_dup(DAG_ZERO);
    }
  /* (- t 0) -> t */
  if (DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand2;
      operand2 = number_new();
      number_from_DAG(operand2, DAG_arg1(src));
      if (number_equal(operand2, number_zero))
	{
	  STAT_INC(minus);
#ifdef PROOF
	  my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
	  number_free(operand2);
	  dest = DAG_dup(DAG_arg0(src));
	  DAG_free(src);
	  return dest;
	}
      else
	number_free(operand2);
    }
  /* (- 0 t) -> (~ t) */
  else if (DAG_is_number(DAG_arg0(src)))
    {
      Tnumber operand1;
      operand1 = number_new();
      number_from_DAG(operand1, DAG_arg0(src));
      if (number_equal(operand1, number_zero))
	{
	  STAT_INC(minus);
#ifdef PROOF
	  my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
	  number_free(operand1);
	  dest = DAG_dup(DAG_new_args(FUNCTION_UNARY_MINUS, DAG_arg1(src), DAG_NULL));
	  DAG_free(src);
	  return dest;
	}
      number_free(operand1);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_unary_minus(TDAG src)
{
  /* PF This has been shown to have dramatic effects, perhaps by
     reducing sharing? */
  if (DAG_is_number(DAG_arg0(src)))
    {
      TDAG dest = DAG_NULL;
      Tnumber result;
      STAT_INC(uminus);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      result = number_new();
      number_from_DAG(result, DAG_arg0(src));
      number_neg(result);
      dest = DAG_dup(number_to_DAG(result));
      number_free(result);
      DAG_free(src);
      return dest;
    }
  else if (unary_minus(DAG_symb(DAG_arg0(src))))
    {
      TDAG dest = DAG_dup(DAG_arg0(DAG_arg0(src)));
      STAT_INC(uminus);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_div(TDAG src)
{
  TDAG dest = DAG_NULL;
  if (DAG_arity(src) != 2)
    my_error("simplify_div: strange arity for src\n");

  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(div);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      DAG_free(src);
      dest = DAG_dup(DAG_ONE);
      return dest;
    }
  if (DAG_is_number(DAG_arg0(src)) && DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand1, operand2;
      Tnumber div;
      STAT_INC(div);
#ifdef PROOF
      my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
      operand1 = number_new();
      operand2 = number_new();
      div = number_new();
      number_from_DAG(operand1, DAG_arg0(src));
      number_from_DAG(operand2, DAG_arg1(src));
      number_div(div, operand1, operand2);
      dest = DAG_dup(number_to_DAG(div));
      number_free(div);
      number_free(operand1);
      number_free(operand2);
      DAG_free(src);
      return dest;
    }
  if (DAG_is_number(DAG_arg1(src)))
    {
      Tnumber operand2;
      operand2 = number_new();
      number_from_DAG(operand2, DAG_arg1(src));
      if (number_equal(operand2, number_one))
	{
	  STAT_INC(div);
#ifdef PROOF
	  my_warning("Applying a rewrite rule that is not proof producing.\n");
#endif
	  number_free(operand2);
	  dest = DAG_dup(DAG_arg0(src));
	  DAG_free(src);
	  return dest;
	}
      else
	number_free(operand2);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_quantifier(TDAG src)
{
  TDAG matrix;
  if (DAG_symb(src) != QUANTIFIER_FORALL && DAG_symb(src) != QUANTIFIER_EXISTS)
    return src;
  matrix = DAG_argn(src);
  if (matrix == DAG_FALSE)
    {
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (matrix == DAG_TRUE)
    {
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_node(TDAG src)
{
  if (DAG_symb(src) == CONNECTOR_AND)
    return simplify_and(src);
  if (DAG_symb(src) == CONNECTOR_OR)
    return simplify_or(src);
  if (DAG_symb(src) == CONNECTOR_NOT)
    return simplify_not(src);
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    return simplify_implies(src);
  if (DAG_symb(src) == CONNECTOR_EQUIV)
    return simplify_equiv(src);
  if (DAG_symb(src) == CONNECTOR_ITE)
    return simplify_ite(src);
  if (DAG_symb(src) == PREDICATE_EQ)
    return simplify_lift_ite(simplify_eq(src));
  if (DAG_symb(src) == PREDICATE_LESS)
    return simplify_less(src);
  if (DAG_symb(src) == PREDICATE_LEQ)
    return simplify_leq(src);
  if (DAG_symb(src) == FUNCTION_ITE)
    return simplify_fite(src);
  if (DAG_symb(src) == FUNCTION_SUM)
    return simplify_sum(src);
  if (DAG_symb(src) == FUNCTION_MINUS)
    return simplify_minus(src);
  if (unary_minus(DAG_symb(src)))
    return simplify_unary_minus(src);
  if (DAG_symb(src) == FUNCTION_PROD)
    return simplify_prod(src);
  if (DAG_symb(src) == FUNCTION_DIV)
    return simplify_div(src);
  if (quantifier(DAG_symb(src)))
    return simplify_quantifier(src);
  return src;
}

/*--------------------------------------------------------------*/

static void
simplify_free_tmp_all_rec(TDAG src)
{
  unsigned i;
  if (DAG_flag(src))
    return;
  DAG_flag_set(src, 1);
  for (i = 0; i < DAG_arity(src); i++)
    simplify_free_tmp_all_rec((TDAG) DAG_arg(src, i));
  if (DAG_Pflag(src))
    {
      DAG_free(DAG_of_ptr(DAG_Pflag(src)));
      DAG_Pflag_set(src, NULL);
    }
}

/*--------------------------------------------------------------*/

static void
simplify_free_tmp_all(TDAG src)
{
  simplify_free_tmp_all_rec(src);
  DAG_reset_flag(src);
}

/*
  --------------------------------------------------------------
  x = a and phi(x) --> phi(a)
  --------------------------------------------------------------
*/

/* x = t and phi(x) --> phi(t), if x \notin t */
/* p EQV G and H(p) --> H(G), if p \notin G */
/* forall i. p(i) EQV G(i) and H(p(*)) --> H(G(*)), if p \notin G */
/* forall i. f(i) EQV g(i) and H(f(*)) --> H(g(*)), if f \notin g */

/*--------------------------------------------------------------*/

#if 0
static TDAG target, source;

static int
simplify_collect_rewrite(TDAG src, int pol)
/* PF returns 1 if there is something that defines a symbol in
   src taken with pol(arity).
   Sets target and source to what is defined and to what. */
{
  int i;
  if (DAG_symb(src) == CONNECTOR_NOT)
    return simplify_collect_rewrite(DAG_arg0(src), INV_POL(pol));
  if ((pol == POL_POS && DAG_symb(src) == CONNECTOR_AND) ||
      (pol == POL_NEG && DAG_symb(src) == CONNECTOR_OR))
    {
      for (i = 0; i < DAG_arity(src); i++)
	if (simplify_collect_rewrite(DAG_arg(src, i), pol))
	  return 1;
    }
  else if (pol == POL_NEG && DAG_symb(src) == CONNECTOR_IMPLIES)
    return simplify_collect_rewrite(DAG_arg0(src), POL_POS) ||
      simplify_collect_rewrite(DAG_arg1(src), POL_NEG);
  else if (pol == POL_POS && DAG_symb(src) == PREDICATE_EQ)
    {
      if (!DAG_arity(DAG_arg0(src))
	  && !DAG_symb_interpreted(DAG_symb(DAG_arg0(src))))
	{
	  target = DAG_arg0(src);
	  source = DAG_arg1(src);
	  return !DAG_contain(source, target) && !DAG_quant(source);
	}
      else if (!DAG_arity(DAG_arg1(src)) &&
	       !DAG_symb_interpreted(DAG_symb(DAG_arg1(src))))
	{
	  target = DAG_arg1(src);
	  source = DAG_arg0(src);
	  return !DAG_contain(source, target) && !DAG_quant(source);
	}
    }
  else if (pol == POL_POS && DAG_symb(src) == CONNECTOR_EQUIV)
    {
      /* PF Boolean proposition equivalent to something */
      if (!DAG_arity(DAG_arg0(src)) &&
	  !DAG_symb_interpreted(DAG_symb(DAG_arg0(src))))
	{
	  target = DAG_arg0(src);
	  source = DAG_arg1(src);
	  return !DAG_contain(source, target) && !DAG_quant(source);
	}
      else if (!DAG_arity(DAG_arg1(src)) &&
	       !DAG_symb_interpreted(DAG_symb(DAG_arg1(src))))
	{
	  target = DAG_arg1(src);
	  source = DAG_arg0(src);
	  return !DAG_contain(source, target) && !DAG_quant(source);
	}
    }
  else if (!DAG_arity(src) && !DAG_symb_interpreted(DAG_symb(src)))
    {
      /* PF Boolean proposition */
      target = src;
      source = (pol == POL_POS) ? DAG_TRUE : DAG_FALSE;
      return 1;
    }
  return 0;
}
#endif

/*--------------------------------------------------------------*/

static TDAG
simplify_boolean_node(TDAG src)
{
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      TDAG DAG0 = DAG_arg0(src);
      /* !(P -> Q) ==> P & !Q */
      if (DAG_symb(DAG0) == CONNECTOR_IMPLIES)
	return DAG_and2(DAG_arg0(DAG0),
			DAG_not(DAG_arg1(DAG0)));
      /* !(P | Q) ==> !P & !Q */
      if (DAG_symb(DAG0) == CONNECTOR_OR && DAG_arity(src) == 2)
	return DAG_and2(DAG_not(DAG_arg0(DAG0)), DAG_not(DAG_arg1(DAG0)));
      /* !(P & Q) ==> !P | !Q */
      if (DAG_symb(DAG0) == CONNECTOR_AND && DAG_arity(src) == 2)
	return DAG_or2(DAG_not(DAG_arg0(DAG0)), DAG_not(DAG_arg1(DAG0)));
      return src;
    }
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      TDAG DAG0 = DAG_arg0(src);
      TDAG DAG1 = DAG_arg1(src);
      /* P -> (Q -> R) ==> (P & Q) -> R */
      if (DAG_symb(DAG1) == CONNECTOR_IMPLIES)
	return DAG_implies(DAG_and2(DAG0, DAG_arg0(DAG1)), DAG_arg1(DAG1));
      /* (P -> Q) -> Q ==> P | Q */
      if (DAG_symb(DAG0) == CONNECTOR_IMPLIES && DAG_arg1(DAG0) == DAG1)
        return DAG_or2(DAG_arg0(DAG0), DAG1);
      return src;
    }  
  if (DAG_symb(src) == CONNECTOR_AND)
    {
      /* P & (P -> Q) ==> P & Q */
      if (DAG_arity(src) == 2 &&
	  DAG_symb(DAG_arg1(src)) == CONNECTOR_IMPLIES &&
	  DAG_arg0(src) == DAG_arg0(DAG_arg1(src)))
	return DAG_and2(DAG_arg0(src), DAG_arg1(DAG_arg1(src)));
      return src;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_boolean(TDAG src)
{
  TDAG dest;
  dest = structural_recursion(src, simplify_boolean_node);
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Structural recursion
  --------------------------------------------------------------
*/

static void
structural_simplify(TDAG src)
{
  unsigned i;
  TDAG *PDAG, dest, tmp;
  if (DAG_tmp_DAG[src])
    return;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    {
      /* PF TODO maybe here we can improve by only rebuilding if
	 some change occurred */
      structural_simplify(DAG_arg(src, i));
      PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
    }
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  tmp = simplify_node(dest);
  DAG_tmp_DAG[src] = tmp;
}

/*
  --------------------------------------------------------------
  Elimination of duplicate args at top level
  --------------------------------------------------------------
*/

TDAG
eliminate_duplicate_arg(TDAG src)
{
  unsigned i, j;
  TDAG * PDAG;
  TDAG dest;
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (!DAG_tmp_DAG[DAG_arg(src, i)])
      {
	DAG_tmp_DAG[DAG_arg(src, i)] = DAG_arg(src, i);
	j++;
      }
  MY_MALLOC(PDAG, j * sizeof(TDAG));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_tmp_DAG[DAG_arg(src, i)])
      {
	PDAG[j++] = DAG_arg(src, i);
	DAG_tmp_DAG[DAG_arg(src, i)] = DAG_NULL;
      }
  dest = DAG_dup(DAG_new(DAG_symb(src), j, PDAG));
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

TDAG
simplify_formula(TDAG src)
{
  TDAG dest;
  unsigned i;
  TDAG * PDAG;
#ifdef PROOF
  my_warning("Simplification is not proof producing.\n");
#endif
  src = simplify_boolean(src);
  simplify_AC(src);
  dest = DAG_dup(DAG_of_ptr(DAG_Pflag(src)));
  simplify_free_tmp_all(src);
#ifdef SIMP_STAT
  if (DAG_count_nodes(src) != DAG_count_nodes(dest))
    fprintf(stderr, "Simplification AC: before %d nodes, after %d nodes\n",
	    DAG_count_nodes(src), DAG_count_nodes(dest));
#endif
  DAG_free(src);
  src = dest;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  memcpy(PDAG, DAG_args(src), DAG_arity(src) * sizeof(TDAG));
  DAG_tmp_reserve();
  /* PF for some reasons, shuffling the arguments of the top-level conjunction
     has a negative effect on efficiency */
  for (i = 0; i < DAG_arity(src); i++)
    {
      structural_simplify(PDAG[i]);
      PDAG[i] = DAG_tmp_DAG[PDAG[i]];
    }
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  DAG_tmp_DAG[src] = DAG_dup(dest);
  DAG_tmp_free_DAG(src);
  /* PF if top level symbol is or/and, eliminate duplicates */
  DAG_free(src);
  if (DAG_symb(dest) == CONNECTOR_OR || DAG_symb(dest) == CONNECTOR_AND)
    dest = eliminate_duplicate_arg(dest);
  DAG_tmp_release();  
  return dest;
}

/*
  --------------------------------------------------------------
  Simplify benchmark
  --------------------------------------------------------------
*/

/*
  computes the set of (function and predicate) symbols used in DAG
  as a list pointed to by Plist.

  uses DAG_flag(src) to make DAG traversal linear
  uses symb_misc(symb) to avoid duplicates
  allocates memory to store result at address Plist */
static void
collect_symb(TDAG src, Tlist * Plist)
{
  unsigned i;
  Tsymb symb;
  if (DAG_flag(src)) return;
  DAG_flag_set(src, 1);
  symb = DAG_symb(src);
  assert(symb_type(symb) != SYMB_MACRO);
  if (symb_misc(symb) == 0 && !symb_interpreted(symb) && 
      symb_type(symb) != SYMB_QUANTIFIER && 
      symb_type(symb) != SYMB_VARIABLE)
    {
      * Plist = list_add(* Plist, ptr_of_symb(symb));
      symb_set_misc(symb, 1);
    }
  for (i = 0; i < DAG_arity(src); ++i)
    collect_symb(DAG_arg(src, i), Plist);
}

/*--------------------------------------------------------------*/

static void collect_DAG_symb(Tsymb symb, Ttable table);

static void
collect_DAG_symb_list(Tlist list, Ttable table)
{
  if (list)
    {
      Tlist ptr = list;
      do
	{
	  Tsymb symb = symb_of_ptr(list_car(ptr));
	  collect_DAG_symb(symb, table);
	  ptr = list_cdr(ptr);
	}
      while (ptr != list);
    }
}

/*--------------------------------------------------------------*/

static void
collect_DAG_symb(Tsymb symb, Ttable table)
{
  Tlist list;
  if (symb_misc(symb) == 0) return;
  list = (Tlist) table_get(table, symb_misc(symb));
  symb_set_misc(symb, 0);
  if (list)
    {
      Tlist ptr = list;
      do
	{
	  TDAG DAG = DAG_of_ptr(list_car(ptr));
	  if (!DAG_flag(DAG))
	    {
	      DAG_flag_set(DAG, 1);
	      collect_DAG_symb_list(DAG_Pflag(DAG), table);
	    }
	  ptr = list_cdr(ptr);
	}
      while (ptr != list);
    }
}

/*--------------------------------------------------------------*/

/*
  Given a conjunction, returns a new conjunction where all conjuncts
  that are not 'related' to the last conjunct have been removed.
  If there are n conjuncts, the n-1 first are considered assumptions
  and the n-th is considered the goal.

  IMPROVE refine algorithm taking patterns into account.
  E.g. consider the set of symbols occuring in the patterns, if none
  appear elsewhere (goal or other assumptions), then the assumption
  is useless.
  
 */
TDAG
simplify_benchmark(TDAG src)
{
  unsigned i;
  unsigned id;
  Ttable table;
  Tlist list;
  TDAG result;

  if (DAG_symb(src) != CONNECTOR_AND) return src;

  /* for each DAG in DAG_args(src), compute the set of symbols it depends
     on (store it as a list in Pflag). */
  for (i = 0; i < DAG_arity(src); ++i)
    {
      Tlist list = NULL;
      collect_symb(DAG_arg(src, i), & list);
      DAG_reset_flag(DAG_arg(src, i));
      LIST_LOOP_BEGIN(list, void *, P);
      DAG_symb_reset_misc(symb_of_ptr(P));
      LIST_LOOP_END(list);
      DAG_Pflag_set(DAG_arg(src, i), list);
    }
  /* 
     for each symbol found in the benchmark, compute the set of assumptions it depends on.
     - a strictly positive integer is associated to each symbol.
     - the table records, for each symbol, the list of assumptions where it appears.
   */
  table = table_new(10, 10);
  table_push(table, NULL);
  id = 1;
  /* label symbols, create table entry with empty list */
  for (i = 0; i < DAG_arity(src); ++i)
    {
      Tlist list = (Tlist) DAG_Pflag(DAG_arg(src, i));
      if (list)
	{
	  Tlist ptr = list;
	  do
	    {
	      Tsymb symb = symb_of_ptr(list_car(ptr));
	      assert(id == table_length(table));
	      if (symb_misc(symb) == 0)
		{
		  symb_set_misc(symb, (int) id);
		  id += 1;
		  table_push(table, NULL);
		}
	      assert(0 < symb_misc(symb) &&
		      ((unsigned) symb_misc(symb)) < table_length(table));
	      ptr = list_cdr(ptr);
	    }
	  while (ptr != list);
	}
    }
  /* for each assumption a, for each symbol s occurring in a, add a to the table entry of s */
  for (i = 0; i < DAG_arity(src) - 1u; ++i)
    {
      Tlist list = (Tlist) DAG_Pflag(DAG_arg(src, i));
      if (list)
	{
	  Tlist ptr = list;
	  do
	    {
	      Tsymb symb = symb_of_ptr(list_car(ptr));
	      assert(0 < symb_misc(symb) &&
		      ((unsigned) symb_misc(symb)) < table_length(table));
	      table_set(table, symb_misc(symb),
			 list_add((Tlist) table_get(table, symb_misc(symb)), 
                                  DAG_ptr_of(DAG_arg(src, i))));
	      ptr = list_cdr(ptr);
	    }
	  while (ptr != list);
	}
    }
  /* now gather the assumptions that are related to the goal */
  list = (Tlist) DAG_Pflag(DAG_argn(src));
  if (list == NULL)
    {
      result = DAG_dup(DAG_argn(src));
    }
  else
    {
      Tlist ptr = list;
      Tlist list2;
      do
	{
	  Tsymb symb = symb_of_ptr(list_car(ptr));
	  if (symb_misc(symb))
	    collect_DAG_symb(symb, table);
	  ptr = list_cdr(ptr);
	}
      while (ptr != list);
      list2 = NULL;
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
	{
	  if (DAG_flag(DAG_arg(src, i)))
	    list2 = list_add(list2, DAG_ptr_of(DAG_arg(src, i)));
#ifdef DEBUG_SIMP_BENCH
	  else
	    my_DAG_message("removed: %D.\n", DAG_arg(src, i));
#endif
	}
      list2 = list_add(list2, DAG_ptr_of(DAG_argn(src)));
#ifdef DEBUG_SIMP_BENCH
      if (list_length(list2) != DAG_arity(src))
	{
	  my_DAG_message("simplify_benchmark: %d assumption(s) removed.\n",
			  DAG_arity(src) - list_length(list2));
	}
      else
	{
	  my_DAG_message("simplify_benchmark: no assumption removed.\n");
	}
#endif
      if (list_length(list2) != DAG_arity(src))
	{
	  result = DAG_dup(DAG_new_list(CONNECTOR_AND, list2));
	}
      else
	result = DAG_dup(src);
      list_free(&list2);
    }
  /* free all the allocated data, restore flags and miscellaneous fields */
  for (i = 0; i < DAG_arity(src); ++i)
    {
      Tlist list = (Tlist) DAG_Pflag(DAG_arg(src, i));
      while (list)
	{
	  Tsymb symb = symb_of_ptr(list_car(list));
	  DAG_symb_reset_misc(symb);
	  list = list_remove(list);
	}
      DAG_Pflag_set(DAG_arg(src, i), NULL);
    }
  for (i = 0; i < table_length(table); ++i)
    {
      Tlist list = table_get(table, i);
      list_free(& list);
    }
  table_free(& table);
  DAG_free(src);
  return result;
}

/*--------------------------------------------------------------*/

void
simplify_init(void)
{
  STAT_NEW(AC, "simp: AC");
  STAT_NEW(unary_nihil_twice, "simp: OO(A) -> A");
  STAT_NEW(reflexivity, "simp: a O a -> TRUE");
  STAT_NEW(irreflexivity, "simp: a O a -> FALSE");
  STAT_NEW(neutral, "simp: a O b O c, c -> a O b");
  STAT_NEW(idempotent, "simp: a O a O b -> a O b");
  STAT_NEW(and, "simp: boolean AND");
  STAT_NEW(or, "simp: boolean OR");
  STAT_NEW(not, "simp: boolean NOT");
  STAT_NEW(implies, "simp: boolean =>");
  STAT_NEW(equiv, "simp: boolean EQV");
  STAT_NEW(plus, "simp: 1 + 1 -> 2");
  STAT_NEW(minus, "simp: minus");
  STAT_NEW(uminus, "simp: uminus");
  STAT_NEW(prod, "simpl: product");
  STAT_NEW(div, "simpl: division");
  STAT_NEW(arith, "simp: unsat/valid linear arithmetic equalities");
  STAT_NEW(itelift, "simp: safe lifting (some) ite from terms to formulas");
  STAT_NEW(subst, "simp: unit clause equality propagation");
  STAT_NEW(tuple_pat, "simp: remove unnecessary quantification");
}

/*--------------------------------------------------------------*/

void
simplify_done(void)
{
  if (DAG_ONE)
    {
      DAG_free(DAG_ZERO);
      DAG_free(DAG_ONE);
    }
  DAG_ZERO = DAG_NULL;
  DAG_ONE = DAG_NULL;
}
