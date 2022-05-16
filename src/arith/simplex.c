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

/* PF


   VARIOUS REMARKS

   One could do constraints strengthening with root-level constraints

   Compare simplex with propagation: simplex modifies a model whereas
   propagation only deals about bounds.  However there may be some
   links because the model is at bounds

   It may be more advantageous to consider only non-strict
   inequalities and repair the values afterwards?  Consider the number
   of operations required to repair (pivots???) vs. avoid need of
   repairing

   The algorithm should be designed such that equalities should not
   introduce inefficiency.

   A hash table may be used to detect variables that are equal
   according to the set of equalities?

   ABOUT STRICT VS NON STRICT DISEQ

   I have a slight feeling that strict disequalities are not
   necessary.  On reals only, because of the convexity, this is clear.
   Assume S is unsatisfiable and contains constraint s1 < a1 ... sn <
   an.  Then s1 = a1 or s2 = a2 or ... sn = an is a logical
   consequence of S where si < ai has been replaced by si <= ai.  Thus
   si = ai should be generated for some i, and a contradiction would
   result in CC.  Completeness in equality generation allows not to
   handle strict equalities.

   For mixed integer and real arithm, using Branch and Bound and
   Cutting planes, maybe this still not holds?  The thing is, some
   strict ineqs can be stengthened directly into non-strict ones


   SOME NOTES ABOUT CVC4 IMPLEMENTATION (20120301)

   arith_priority_queue: heap
     They have three modes
     - collection (unsorted)
     - difference (sorted by difference between var and unsatisfied extremum)
     - variable (sorted by variable id)
     In difference mode, they furthermore have three pivot rules
     - minimum
     - break_ties
     - maximum
     The minimum, that takes the basic var with the minimum diff is by default
     Modes are changes in simplex.cpp (which strategy???)

   arith_prop_manager: propagations

   arith_rewriter: basic rewriting.  Do not understand everything, but
   I think there is nothing deep in this.

   arith_static_learner: preprocessing black magic.  Maybe along Kim2.

   arith_utilities: hash to map terms to arith variable and back,
   various simple utility functions, recognisers...

   arithvar_node_map: functions to map terms to arith variables and vice-versa

   arithvar_set: efficient datastructures (?, which?) for sets of variables

   atom_database: keeps track of all atoms, and does theory
   propagation on them.  Clauses are added to SAT solver and forgot
   after that.  So this module basically sleeps after every atom has
   been registered
   x < a ==> x < b if a < b.

   delta_rational: operations on DeltaRational c + d delta

   difference_manager: maintains links between vars such that s = x -
   y.  Useful for propagation of equalities.

   dio_solver: Diophantine equation solver.  Not read

   linear_equality: update(), pivotAndUpdate()

   normal_form: ???

   ordered_set: 

   partial_model: ???

   simplex: the real thing

   tableau: the data-structure for simplex

   theory_arith: main class

   theory_arith_type_rules

   The assertup/low are similar to D&dM06, but for a check for an
   inequality x != u if x>=u and x<=u are asserted.  Seem to be
   implemented as a list.  I believe it is better to implement as a hash
   (x u) for each x != u.  There is also a assert equal to assert x = c

   The differenceManager may be to handle new equalities???

   findShortestBasicRow.  For some reason, there is a function to
   extract the basic variable x with the shortest row L(x)...  Maybe a
   simplex acceleration?

   TheoryArith::propagate

   TheoryArith::notifyEq : empty function.

   TheoryArith::propagateCandidateBound
                propagateCandidateLowerBound

   It seems that for each var, they retain which bound was propagated
   (in the sense of Theory propagation).  If bound is not improved, no
   need to try to propagate again

   Safe arithmetic in C
   http://www.informit.com/content/images/0321335724/samplechapter/seacord_ch05.pdf
https://www.securecoding.cert.org/confluence/display/seccode/INT32-C.+Ensure+that+operations+on+signed+integers+do+not+result+in+overflow?showComments=false
   
   There exists flags in gcc to capture overflow ftrapv, fwrapv

   Use divexact in gmp when the division is known to be exact.  The
   exact division works transforming division to multiplication, based
   on the fact that we are working in representation modulo 2^64, and
   using the extended gcd

   mpz_swap to swap two mpz, for sorting

   for gcd, it is better to start with the smallest number

*/

#include <stdlib.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>

#include "general.h"
#include "types.h"
#include "stack.h"
#include "undo.h"
#include "veriT-status.h"

#include "numbers.h"
#include "simplex.h"

#define LA_DEBUG

#ifdef LA_DEBUG
static void LA_print(void);
static void LA_invariant(void);
#define CHECK_INVARIANT LA_print(); LA_invariant()
#else
#define CHECK_INVARIANT
#endif

static Tstatus LAstatus = UNDEF;

#define NORM_MAX ((1<<16) - 1)
#define NORM_MIN (-NORM_MAX)

/*
  --------------------------------------------------------------
  Variables
  --------------------------------------------------------------
*/

#define LAVAR_UNDEF 0

/**
   \author Pascal Fontaine
   \var LAvar_n
   \brief number of variables */
static TLAvar LAvar_n = 0;

/**
   \author Pascal Fontaine
   \typedef TLASvar
   \brief structure for variables
   \remark for a basic variable i, the diagonal element can be found in C[i] */
typedef struct TLASvar
{
  TLAdelta assign;       /*< value */
  TLAdelta assign2;      /*< value (backup) */
#ifdef PEDANTIC
  bool basic;          /*< variable is basic */
  bool passive;        /*< variable is passive */
  bool mark;           /*< backup value and value differ */
  bool mark_unsat;     /*< bounds are unsatisfied */
  unsigned char boundmask;  /*< up & lo bounds exist (3) up (2) lo (1) none (0) */
#else
  bool basic:1;          /*< variable is basic */
  bool passive:1;        /*< variable is passive */
  bool mark:1;           /*< backup value and value differ */
  bool mark_unsat:1;     /*< bounds are unsatisfied */
  unsigned boundmask:2;  /*< up & lo bounds exist (3) up (2) lo (1) none (0) */
#endif
  TLAdelta bound[2];     /*< lower [0] and upper [1] bound */
  Tlit reason[2];        /*< get the reason for lower [0] and upper [1] bound */
} TLASvar;

/**
   \author Pascal Fontaine
   \var LAvar
   \brief array of variables */
static TLASvar * LAvar;

/*
  --------------------------------------------------------------
  Monom Handler
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \typedef Tmon_id
   \brief identifier for monom */
typedef unsigned TLAmon_id;

/**
   \author Pascal Fontaine
   \struct LAmon
   \brief element of matrix
   \remark so c_b b + ... + c n + ... = 0 */
typedef struct TLAmon
{
  TLAmon_id cn; /*< move to next column */
  TLAmon_id ln; /*< move to next line */
  TLAmon_id lp; /*< move to prev line */
  TLAvar l;     /*< line index (usually basic var) */
  TLAvar c;     /*< colomn index (usually non-basic var) */
  TLAsigned a;  /*< the coefficient */
} TLAmon;

/**
   \author Pascal Fontaine
   \var mon_size
   \brief allocated size for mon */
static unsigned mon_size = 0;
/**
   \author Pascal Fontaine
   \var mon_head
   \brief points to first available element */
static unsigned mon_head = 0;
/**
   \author Pascal Fontaine
   \var mon
   \brief array of monom elements
   \brief for free elements, cp points to next available element */
static TLAmon * mon = NULL;

/**
   \author Pascal Fontaine
   \var L
   \brief first monom of definition for basic variable
   \brief indexed by basic variable
   \remark refers to a line in the tableau */
static unsigned * L;

/**
   \author Pascal Fontaine
   \var L
   \brief first monom of definition of basic variable containing non-basic lit
   \brief indexed by non-basic lit
   \remark refers to a column in the tableau */
static unsigned * C;

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief initialise monome handling */
static void
mon_init(void)
{
  unsigned i;
  TLAmon * Pmon;
  mon_size = 32;
  MY_MALLOC(mon, mon_size * sizeof(TLAmon));
  memset(mon, 0, mon_size * sizeof(TLAmon));
  mon_head = 1;
  for (Pmon = mon + 1, i = 2; i < mon_size; i++, Pmon++)
    Pmon->cn = i;
  Pmon->cn = 0; /* redundant but clearer */
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief release monome handling */
static void
mon_done(void)
{
  free(mon);
  mon_head = 0;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief get a new monom
   \return the monom id */
static inline TLAmon_id
mon_new(void)
{
  TLAmon_id res = mon_head;
  mon_head = mon[res].cn;
  mon[res].cn = 0;
  if (!mon_head)
    {
      unsigned i;
      TLAmon * Pmon;
      MY_REALLOC(mon, (mon_size << 1) * sizeof(TLAmon));
      memset(mon + mon_size, 0, mon_size * sizeof(TLAmon));
      mon_head = mon_size;
      for (Pmon = mon + mon_size, i = mon_size + 1, mon_size <<= 1;
	   i < mon_size; i++, Pmon++)
	Pmon->cn = i;
      Pmon->cn = 0;
    }
  return res;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief release a monom
   \param mon_id the monom id */
static inline void
mon_free(TLAmon_id mon_id)
{
  mon[mon_id].cn = mon_head;
  mon_head = mon_id;
  mon[mon_id].c = 0;
  mon[mon_id].l = 0;
  mon[mon_id].ln = 0;
  mon[mon_id].lp = 0;
  mon[mon_id].cn = 0;
}

/*--------------------------------------------------------------*/

/**
   \brief adds a monom in the column for its c field
   \param mon_id the monom to add */
static inline void
mon_C_add(TLAmon_id mon_id)
{
  if (!mon[mon_id].c)
    return;
  assert(mon_id);
  assert(mon[C[mon[mon_id].c]].lp == 0);
  mon[mon_id].lp = 0;
  mon[mon_id].ln = C[mon[mon_id].c];
  if (mon[mon_id].ln)
    mon[mon[mon_id].ln].lp = mon_id;
  C[mon[mon_id].c] = mon_id;
}

/*--------------------------------------------------------------*/

/**
   \brief removes monom from the column for its c field
   \param mon_id the monom to remove */
static inline void
mon_C_rm(TLAmon_id mon_id)
{
  assert(mon_id);
  if (mon[mon_id].lp)
    {
      assert(mon[mon[mon_id].lp].ln == mon_id);
      mon[mon[mon_id].lp].ln = mon[mon_id].ln;
      if (mon[mon_id].ln)
	mon[mon[mon_id].ln].lp = mon[mon_id].lp;
    }
  else
    {
      assert(C[mon[mon_id].c] == mon_id);
      C[mon[mon_id].c] = mon[mon_id].ln;
      /* if (mon[mon_id].ln) unnecessary */
      mon[mon[mon_id].ln].lp = 0;
    }
}

/*
  --------------------------------------------------------------
  Table of modified variables
  --------------------------------------------------------------
*/

static unsigned modified_n = 0;
static unsigned modified_size = 0;
static TLAvar * modified;

static void
modified_init(void)
{
  modified_n = 0;
  modified_size = 16;
  MY_MALLOC(modified, modified_size * sizeof(TLAvar));
}

/*--------------------------------------------------------------*/

static void
modified_done(void)
{
  modified_n = 0;
  modified_size = 0;
  free(modified);
}

/*--------------------------------------------------------------*/

static inline void
modified_insert(TLAvar i)
{
  if (LAvar[i].mark)
    return;
  LAvar[i].mark = 1;
  if (modified_n >= modified_size)
    {
      modified_size <<= 1;
      MY_REALLOC(modified, modified_size * sizeof(TLAvar));
    }
  modified[modified_n++] = i;
}

/*--------------------------------------------------------------*/

static void
modified_save(void)
{
  unsigned i;
  for (i = 0; i < modified_n; i++)
    {
      assert(LAvar[modified[i]].mark);
      LAvar[modified[i]].mark = 0;
      LAvar[modified[i]].assign2 = LAvar[modified[i]].assign;
    }
  modified_n = 0;
}

/*
  --------------------------------------------------------------
  var heap and activity
  Table of unsat basics
  --------------------------------------------------------------
*/

static unsigned heap_var_n = 0;
static unsigned heap_var_size = 0;
static TLAvar * heap_var = NULL;
static unsigned heap_index_size = 0;
static unsigned * heap_index = NULL;

#define HEAP_UNDEF UINT_MAX

static inline unsigned
left(unsigned i)
{
  return i*2+1;
}

/*--------------------------------------------------------------*/

static inline unsigned
right(unsigned i)
{
  return i*2+2;
}

/*--------------------------------------------------------------*/

static inline unsigned
parent(unsigned i)
{
  return (i-1)>>1;
}

/*--------------------------------------------------------------*/

static inline void
sift_up(unsigned i)
{
  TLAvar var = heap_var[i];
  unsigned p = parent(i);
  while (i && var < heap_var[p])
    {
      heap_var[i] = heap_var[p];
      heap_index[heap_var[p]] = i;
      i = p;
      p = parent(p);
    }
  heap_var[i] = var;
  heap_index[var] = i;
}

/*--------------------------------------------------------------*/

static inline void
sift_down(unsigned i)
{
  TLAvar var = heap_var[i];
  while (left(i) < heap_var_n)
    {
      unsigned child;
      if (right(i) < heap_var_n && heap_var[right(i)] < heap_var[left(i)])
	child = right(i);
      else
	child = left(i);
      if (heap_var[child] >= var)
	break;
      heap_var[i] = heap_var[child];
      heap_index[heap_var[child]] = i;
      i = child;
    }
  heap_var[i] = var;
  heap_index[var] = i;
}

/*--------------------------------------------------------------*/

static inline int
heap_var_in(TLAvar var)
{
  assert(var != LAVAR_UNDEF);
  return var < heap_index_size && heap_index[var] != HEAP_UNDEF;
}

/*--------------------------------------------------------------*/

static inline void
heap_var_insert(TLAvar var)
{
  assert(var != LAVAR_UNDEF);
  while (heap_var_size < heap_var_n + 1)
    {
      heap_var_size *= 2;
      MY_REALLOC(heap_var, heap_var_size * sizeof(TLAvar));
    }
  while (heap_index_size <= var)
    {
      unsigned i;
      heap_index_size *= 2;
      MY_REALLOC(heap_index, heap_index_size * sizeof(int));
      for (i = heap_index_size>>1; i < heap_index_size; ++i)
	heap_index[i] = HEAP_UNDEF;
    }
  assert(!heap_var_in(var));
  heap_var[heap_var_n] = var;
  heap_index[var] = heap_var_n;
  sift_up(heap_var_n++);
}

/*--------------------------------------------------------------*/

static inline TLAvar
heap_var_remove_min(void)
{
  TLAvar var = heap_var[0];
  heap_index[var] = HEAP_UNDEF;
  heap_var[0] = heap_var[--heap_var_n];
  if (heap_var_n)
    sift_down(0); /* index will be set in sift_down */
  return var;
}

/*--------------------------------------------------------------*/

#if 0
static inline TLAvar
heap_var_get_min(void)
{
  return heap_var[0];
}
#endif

/*--------------------------------------------------------------*/

static inline int
heap_var_empty(void)
{
  return heap_var_n == 0;
}

/*--------------------------------------------------------------*/

#if 0
static inline void
heap_var_build(TLAvar * vs, unsigned n)
{
  int i;
  heap_var_n = 0;

  for (i = 0; i < (int) n; i++)
    {
      heap_index[vs[i]] = i;
      heap_var[heap_var_n++] = vs[i];
    }

  for (i = heap_var_n / 2 - 1; i >= 0; i--)
    sift_down(i);
}
#endif

/*--------------------------------------------------------------*/

static inline void
heap_var_init(void)
{
  unsigned i;
  heap_var_n = 0;
  heap_var_size = 16;
  MY_MALLOC(heap_var, heap_var_size * sizeof(TLAvar));
  heap_index_size = 16;
  MY_MALLOC(heap_index, heap_index_size * sizeof(unsigned));
  for (i = 0; i < heap_index_size; ++i)
    heap_index[i] = HEAP_UNDEF;
}


/*--------------------------------------------------------------*/

static inline void
heap_var_done(void)
{
  heap_var_n = 0;
  free(heap_var);
  heap_var = NULL;
  heap_var_size = 0;
  free(heap_index);
  heap_index = NULL;
  heap_index_size = 0;
}

/*--------------------------------------------------------------*/

static inline void
heap_var_notify_var_table_increase(unsigned j)
{
  if (heap_index_size < j)
    {
      unsigned i;
      MY_REALLOC(heap_index, j * sizeof(int));
      for (i = heap_index_size; i < j; ++i)
	heap_index[i] = HEAP_UNDEF;
      heap_index_size = j;
    }
}

/*
  --------------------------------------------------------------
  LAvar
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief initialize variables
   \remark variable 0 is set to be constant 1 */
static void
LAvar_init(void)
{
  assert(LAvar_n == 0);
  LAvar_n = 1;
  MY_MALLOC(LAvar, sizeof(TLASvar));
  MY_MALLOC(L, 2 * LAvar_n * sizeof(TLAmon_id));
  MY_MALLOC(C, 2 * LAvar_n * sizeof(TLAmon_id));
  LAdelta_set_one(&LAvar[0].assign);
  LAdelta_set_one(&LAvar[0].assign2);
  LAvar[0].basic = 0;
  LAvar[0].mark = 0;
  LAvar[0].mark_unsat = 0;
  LAvar[0].boundmask = 2;
  C[0] = 0;
  L[0] = 0;
  LAdelta_set_one(&LAvar[0].bound[0]);
  LAdelta_set_one(&LAvar[0].bound[1]);
  LAvar[0].reason[0] = 0;
  LAvar[0].reason[1] = 0;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief release variables */
static void
LAvar_done(void)
{
  free(LAvar);
  LAvar_n = 0;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief create a new variable
   \return the new variable
   \remark all created variables are non-basic */
TLAvar
LAvar_new(void)
{
  assert(LAvar_n);
  if (!(LAvar_n & (LAvar_n - 1)))
    {
      MY_REALLOC(LAvar, 2 * LAvar_n * sizeof(TLASvar));
      MY_REALLOC(L, 2 * LAvar_n * sizeof(TLAmon_id));
      MY_REALLOC(C, 2 * LAvar_n * sizeof(TLAmon_id));
      heap_var_notify_var_table_increase(2 * LAvar_n);
    }
  LAdelta_set_zero(&LAvar[LAvar_n].assign);
  LAdelta_set_zero(&LAvar[LAvar_n].assign2);
  LAvar[LAvar_n].basic = 0;
  LAvar[LAvar_n].mark = 0;
  LAvar[LAvar_n].mark_unsat = 0;
  LAvar[LAvar_n].boundmask = 0;
  L[LAvar_n] = 0;
  C[LAvar_n] = 0;
  LAvar[LAvar_n].reason[0] = 0;
  LAvar[LAvar_n].reason[1] = 0;
  return LAvar_n++;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief update basic variable
   \param i a variable
   \param D a delta value
   \param num a numeric value
   \param den a numeric value
   \remark variable i will be set to its former value minus D * num /den
   \remark useful for updating basic variable on non-basic variable update */
static inline void
LAvar_update(TLAvar i, TLAdelta * D, TLAsigned * num, TLAsigned * den)
{
  int bound;
  signed long den3, sign;
  signed long long num2;
  signed long long num3;
  unsigned long long den2;
  TLASvar * Pvar = LAvar + i;
  modified_insert(i);
  /* v_i = v_i - D * num / den */
  /* (n_i', d_i') = (n_i, d_i) - (n_D, d_D) * num / den */
  /* n_i' = n_i * d_D * den - n_D * num * d_i */
  /* d_i' = d_i * d_D * den */
  /* n_i' = n_i * d_D * |den| - n_D * num * d_i * sign(den) */
  /* d_i' = d_i * d_D * |den| */
  /* num2 = den2 = d_D * |den|
     den2 *= d_i
     num2 *= n_i
     num3 = n_D * num * d_i * sign(den)
     num2 -= num3 */
  sign = (den->sval) >> (sizeof(signed long) * CHAR_BIT - 1); /* 0 or -1 */
  den3 = (den->sval + sign) ^ sign; /* den3 = |den| */
  den2 = D->val.sval.den * (unsigned long long) den3;
  overflow |= (den2 > INT_MAX);
  num2 = (signed int) den2;
  den2 *= Pvar->assign.val.sval.den;
  overflow |= (den2 > INT_MAX);
  num2 *= Pvar->assign.val.sval.num;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);

  num3 = D->val.sval.num * num->sval;
  overflow |= (num3 > INT_MAX) || (num3 <= INT_MIN);
  num3 *= Pvar->assign.val.sval.den;
  overflow |= (num3 > INT_MAX) || (num3 <= INT_MIN);
  num3 = (num3 + sign) ^ sign;
  num2 -= num3;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);

  if (overflow)
    my_error("LA overflow\n");

  Pvar->assign.val.sval.num = (signed int) num2;
  Pvar->assign.val.sval.den = (unsigned int) den2;
  /* (Pvar->assign.val.sval.num > SHRT_MAX ||
     Pvar->assign.val.sval.den > SHRT_MAX) */
  LArational_normalize(&Pvar->assign.val);
  /* 0 if nothing is added
     1 if lower bound may be violated (increment is negative)
     -1 if upper bound may be violated (increment is positive) */
  bound = (int)
    (((signed long)num3 >> (sizeof(signed long) * CHAR_BIT - 1)) << 1)
    + (num3 != 0);

  den2 = D->delta.sval.den * (unsigned long long) den3;
  overflow |= (den2 > INT_MAX);
  num2 = (signed int) den2;
  den2 *= Pvar->assign.delta.sval.den;
  overflow |= (den2 > INT_MAX);
  num2 *= Pvar->assign.delta.sval.num;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);

  num3 = D->delta.sval.num * num->sval;
  overflow |= (num3 > INT_MAX) || (num3 <= INT_MIN);
  num3 *= Pvar->assign.delta.sval.den;
  overflow |= (num3 > INT_MAX) || (num3 <= INT_MIN);
  num3 = (num3 + sign) ^ sign;
  num2 -= num3;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);

  if (overflow)
    my_error("LA overflow\n");

  Pvar->assign.delta.sval.num = (signed int) num2;
  Pvar->assign.delta.sval.den = (unsigned int) den2;
  /*if (Pvar->assign.delta.sval.num > SHRT_MAX ||
    Pvar->assign.delta.sval.den > SHRT_MAX) */
  LArational_normalize(&Pvar->assign.delta);
  if (!bound)
    {
      assert(num3);
      bound = (int)((signed long)num3 >> (sizeof(signed long) * CHAR_BIT - 1));
    }

  if (!Pvar->mark_unsat &&
      ((bound == -1 && (Pvar->boundmask & 2) && LAdelta_less(&Pvar->bound[1], &Pvar->assign)) ||
       (bound != -1 && (Pvar->boundmask & 1) && LAdelta_less(&Pvar->assign, &Pvar->bound[0]))))
    {
      Pvar->mark_unsat = 1;
      heap_var_insert(i);
    }
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief update non-basic variable
   \param i a variable
   \param v a delta value
   \remark variable i will be set to v */
static inline void
LAvar_assign(TLAvar i, TLAdelta * v)
{
  TLASvar * Pvar = LAvar + i;
  Pvar->assign = *v;
  modified_insert(i);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief check if bound is not reached
   \param i is a non-basic variable
   \param pol is a polarity
   \return 1 iff non-basic variable i can be increased (pol = 1) or decreased (pol == 0) and remain within bound */
static inline int
LAvar_notied_bound(TLAvar i, unsigned pol)
{
  /* non-basic variables should be within bound, the test:
     pol?
     LAdelta_less(&LAvar[i].assign, &LAvar[i].bound[1]):
     LAdelta_less(&LAvar[i].bound[0], &LAvar[i].assign)
     can be rewritten as
     pol?
     LAdelta_neq(&LAvar[i].assign, &LAvar[i].bound[1]):
     LAdelta_neq(&LAvar[i].bound[0], &LAvar[i].assign)
     i.e.
     LAdelta_neq(&LAvar[i].assign, &LAvar[i].bound[pol]) */
  assert(!LAvar[i].basic);
  return !(LAvar[i].boundmask & (1 << pol)) ||
    !LAdelta_eq(&LAvar[i].assign, &LAvar[i].bound[pol]);
}

/*
  --------------------------------------------------------------
  Linear expression
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief normalize L[k] by dividing all coefficients by gcd */
static void
linear_expr_normalize(TLAmon_id m)
{
  TLAmon * Pmon;
  unsigned long min_val, tmp;
  signed long mask;
  TLAvar min;
  assert(m);
  Pmon = mon + m;
  min = Pmon->c;
  mask = Pmon->a.sval >> (sizeof(signed long) * CHAR_BIT - 1);
  min_val = (unsigned long) ((Pmon->a.sval + mask) ^ mask);
  /* identify smallest coefficient */
  for (Pmon = mon + Pmon->cn; Pmon != mon; Pmon = mon + Pmon->cn)
    {
      mask = Pmon->a.sval >> (sizeof(signed long) * CHAR_BIT - 1);
      tmp = (unsigned long) ((Pmon->a.sval + mask) ^ mask);
      if (tmp < min_val)
	{
	  min = Pmon->c;
	  min_val = tmp;
	}
    }
  /* compute gcd */
  for (Pmon = mon + m; min_val != 1 && Pmon != mon; Pmon = mon + Pmon->cn)
    if (Pmon->c != min)
      {
	mask = Pmon->a.sval >> (sizeof(signed long) * CHAR_BIT - 1);
	tmp = (unsigned long) ((Pmon->a.sval + mask) ^ mask);
	min_val = gcd(min_val, tmp);
      }
  if (min_val != 1)
    for (Pmon = mon + m; Pmon != mon; Pmon = mon + Pmon->cn)
      Pmon->a.sval /= (signed long) min_val;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief replace L[k] by a L[k] - b L[i] updating the C[j] accordingly */
static void
linear_expr_update(TLAvar k, TLAvar i, TLAsigned a, TLAsigned b)
{
  TLAmon_id m1, m2;
  TLAmon_id pc = 0;
  m1 = L[k];
  m2 = L[i];
  while (m1 || m2)
    if (!m1 || (m2 && mon[m2].c < mon[m1].c))
      /* mon[m1].c > mon[m2].c */ /* variable appears */
      {
	TLAmon_id m3 = mon_new();
	/* copy monome m2 */
	mon[m3].a = mon[m2].a;
	mon[m3].c = mon[m2].c;
	mon[m3].l = k;
	mon[m3].cn = m1;
	LAsigned_mult(&mon[m3].a, &b);
	LAsigned_neg(&mon[m3].a);
	if (pc)
	  mon[pc].cn = m3;
	else
	  L[k] = m3;
	/* insert m3 in same column as m2 */
	mon_C_add(m3);
	/* next column for second linear expression */
	m2 = mon[m2].cn;
      }
    else if (!m2 || mon[m1].c < mon[m2].c)
      {
	LAsigned_mult(&mon[m1].a, &a);
	pc = m1;
	/* next column for first linear expressions */
	m1 = mon[m1].cn;
      }
    else /* if (mon[m1].c == mon[m2].c) */
      {
	LAsigned_com(&mon[m1].a, &mon[m2].a, &a, &b);
	if (LAsigned_is_zero(&mon[m1].a))
	  /* variable disappears, both in L[k] and C[Pmon1->c] */
	  {
	    TLAmon_id tmp = m1;
	    /* remove in row */
	    if (pc)
	      mon[pc].cn = mon[m1].cn;
	    else
	      L[k] = mon[m1].cn;
	    /* remove in column */
	    mon_C_rm(m1);
	    /* next column for both linear expressions */
	    m1 = mon[m1].cn;
	    m2 = mon[m2].cn;
	    mon_free(tmp);
	  }
	else
	  {
	    pc = m1;
	    m1 = mon[m1].cn;
	    m2 = mon[m2].cn;
	  }
      }
  /* IMPROVE: we could avoid normalizing systematically */
  linear_expr_normalize(L[k]);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief replace m by a m - b L[i] */
static TLAmon_id
linear_expr_update2(TLAmon_id m, TLAvar i, TLAsigned a, TLAsigned b)
{
  TLAmon_id m1, m2;
  TLAmon_id pc = 0;
  m1 = m;
  m2 = L[i];
  while (m1 || m2)
    if (!m1 || (m2 && mon[m2].c < mon[m1].c))
      /* mon[m1].c > mon[m2].c */ /* variable appears */
      {
	TLAmon_id m3 = mon_new();
	/* copy monome m2 */
	mon[m3].a = mon[m2].a;
	mon[m3].c = mon[m2].c;
	mon[m3].cn = m1;
	LAsigned_mult(&mon[m3].a, &b);
	LAsigned_neg(&mon[m3].a);
	if (pc)
	  mon[pc].cn = m3;
	else
	  m = m3;
	/* next column for second linear expression */
	m2 = mon[m2].cn;
      }
    else if (!m2 || mon[m1].c < mon[m2].c)
      {
	LAsigned_mult(&mon[m1].a, &a);
	pc = m1;
	/* next column for first linear expressions */
	m1 = mon[m1].cn;
      }
    else /* if (mon[m1].c == mon[m2].c) */
      {
	LAsigned_com(&mon[m1].a, &mon[m2].a, &a, &b);
	if (LAsigned_is_zero(&mon[m1].a))
	  /* variable disappears */
	  {
	    TLAmon_id tmp = m1;
	    /* remove in row */
	    if (pc)
	      mon[pc].cn = mon[m1].cn;
	    else
	      m = mon[m1].cn;
	    /* next column for both linear expressions */
	    m1 = mon[m1].cn;
	    m2 = mon[m2].cn;
	    mon_free(tmp);
	  }
	else
	  {
	    pc = m1;
	    m1 = mon[m1].cn;
	    m2 = mon[m2].cn;
	  }
      }
  /* IMPROVE: we could avoid normalizing systematically */
  linear_expr_normalize(m);
  return m;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief remove all basic variables from equation */
static TLAmon_id
linear_expr_eliminate_basic(TLAmon_id m)
{
  TLAmon_id b1, b2;
  for (b1 = m; b1 != 0; b1 = mon[b1].cn)
    if (mon[b1].c && LAvar[mon[b1].c].basic)
      break;
  while (b1)
    {
      TLAvar bvar = mon[b1].c;
      for (b2 = mon[b1].cn; b2 != 0; b2 = mon[b2].cn)
	if (LAvar[mon[b2].c].basic)
	  break;
      m = linear_expr_update2(m, bvar, mon[C[bvar]].a, mon[b1].a);
      b1 = b2;
    }
#ifdef LA_DEBUG
  for (b1 = m; b1 != 0; b1 = mon[b1].cn)
    assert(!LAvar[mon[b1].c].basic);    
#endif
  return m;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief compute value of variable i
   \param m linear expression
   \param i variable
   \param delta the value */
static void
linear_expr_val(TLAmon_id m, TLAvar i, TLAdelta * delta)
{
  TLAmon * Pmon, * Pmon2;
  LAdelta_set_zero(delta);
  for (Pmon = mon + m; Pmon != mon; Pmon = mon + Pmon->cn)
    if (Pmon->c != i)
      LAdelta_addmult(delta, &LAvar[Pmon->c].assign, &Pmon->a);
    else
      Pmon2 = Pmon;
  LAdelta_div_opp(delta, &Pmon2->a);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief print linear expression
   \param m linear expression */
static void
linear_expr_print(TLAmon_id m)
{
  TLAmon * Pmon;
  for (Pmon = mon + m; Pmon != mon; Pmon = mon + Pmon->cn)
    {
      printf("%ld", Pmon->a.sval);
      if (Pmon->c)
	printf("x_%u", Pmon->c);
      printf("%s", Pmon->cn?" + ":"");
    }
  printf("\n");
}

/*
  --------------------------------------------------------------
  Conflict
  --------------------------------------------------------------
*/

/* PF
   there are two ways to have a conflict:
   a new bound that contradicts an old one
   a variable that cannot be updated */

static TLAvar simplex_conflict_var = 0;
static bool simplex_conflict_upper = false;
static Tlit simplex_conflict_new_lit = LIT_UNDEF;

Tstack_lit
simplex_conflict(void)
{
  Tstack_lit conflict;
  stack_INIT(conflict);
  assert(LAstatus == UNSAT);
  if (simplex_conflict_new_lit)
    {
      stack_push(conflict, simplex_conflict_new_lit);
      stack_push(conflict,
		 LAvar[simplex_conflict_var].reason[simplex_conflict_upper]);
    }
  else
    {
      TLAmon * Pmon = mon + L[simplex_conflict_var];
      TLAsigned c = mon[C[simplex_conflict_var]].a;
      if (!Pmon->c)
	Pmon = mon + Pmon->cn;
      if (simplex_conflict_upper)
	{
	  for (; Pmon != mon; Pmon = mon + Pmon->cn)
	    if (Pmon->c != simplex_conflict_var)
	      stack_push(conflict,
			 LAvar[Pmon->c].reason[LAsigned_sign_diff(&Pmon->a, &c)]);
	  stack_push(conflict, LAvar[simplex_conflict_var].reason[1]);
	}
      else
	{
	  for (; Pmon != mon; Pmon = mon + Pmon->cn)
	    if (Pmon->c != simplex_conflict_var)
	      stack_push(conflict,
			 LAvar[Pmon->c].reason[!LAsigned_sign_diff(&Pmon->a, &c)]);
	  stack_push(conflict, LAvar[simplex_conflict_var].reason[0]);
	}
    }
  return conflict;
}

/*
  --------------------------------------------------------------
  Backtracking
  --------------------------------------------------------------
*/

enum {ARITH_LOWER_BOUND = UNDO_ARITH,
      ARITH_UPPER_BOUND,
      ARITH_STATUS};

typedef struct Tsimplex_bound {
  TLAvar var;
  TLAdelta bound;
  Tlit reason;
} Tsimplex_bound;

/*--------------------------------------------------------------*/

static void
backtrack_upper_bound(TLAvar var, Tlit reason, TLAdelta *bound)
{
  Tsimplex_bound *Psimplex_bound =
    (Tsimplex_bound *)undo_push(ARITH_UPPER_BOUND);
  Psimplex_bound->var = var;
  Psimplex_bound->reason = reason;
  Psimplex_bound->bound = *bound;
}

/*--------------------------------------------------------------*/

static void
backtrack_lower_bound(TLAvar var, Tlit reason, TLAdelta *bound)
{
  Tsimplex_bound *Psimplex_bound =
    (Tsimplex_bound *)undo_push(ARITH_LOWER_BOUND);
  Psimplex_bound->var = var;
  Psimplex_bound->reason = reason;
  Psimplex_bound->bound = *bound;
}

/*--------------------------------------------------------------*/

static void
backtrack_status(void)
{
  undo_push(ARITH_STATUS);
}

/*--------------------------------------------------------------*/

static void
arith_hook_set_lower_bound(Tsimplex_bound *Psimplex_bound)
{
  assert(LAvar[Psimplex_bound->var].boundmask ^ 1u);
  LAvar[Psimplex_bound->var].bound[0] = Psimplex_bound->bound;
#ifdef PEDANTIC
  LAvar[Psimplex_bound->var].boundmask =
    (unsigned char)(LAvar[Psimplex_bound->var].boundmask ^
		    !Psimplex_bound->reason);
#else
  LAvar[Psimplex_bound->var].boundmask ^= !Psimplex_bound->reason;
#endif
  LAvar[Psimplex_bound->var].reason[0] = Psimplex_bound->reason;
}

/*--------------------------------------------------------------*/

static void
arith_hook_set_upper_bound(Tsimplex_bound *Psimplex_bound)
{
  assert(LAvar[Psimplex_bound->var].boundmask ^ 2u);
  LAvar[Psimplex_bound->var].bound[1] = Psimplex_bound->bound;
#ifdef PEDANTIC
  LAvar[Psimplex_bound->var].boundmask =
    (unsigned char)(LAvar[Psimplex_bound->var].boundmask ^
		    ((!Psimplex_bound->reason) << 1u));
#else
  LAvar[Psimplex_bound->var].boundmask ^= !Psimplex_bound->reason;
#endif
  LAvar[Psimplex_bound->var].reason[1] = Psimplex_bound->reason;
}

/*--------------------------------------------------------------*/

static void
arith_hook_status(void)
{
  simplex_conflict_new_lit = LIT_UNDEF;
  LAstatus = UNDEF;
}

/*--------------------------------------------------------------*/

static void
backtrack_init(void)
{
  undo_set_hook(ARITH_LOWER_BOUND, (Tundo_hook)arith_hook_set_lower_bound,
		sizeof(Tsimplex_bound));
  undo_set_hook(ARITH_UPPER_BOUND, (Tundo_hook)arith_hook_set_upper_bound,
		sizeof(Tsimplex_bound));
  undo_set_hook(ARITH_STATUS, (Tundo_hook)arith_hook_status, 0);
}

/*--------------------------------------------------------------*/

static void
backtrack_done(void)
{
}

/*
  --------------------------------------------------------------
  Simplex internal
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief update value of basic variables
   \param i non-basic variable to update
   \param v value */
static inline void
update(TLAvar i, TLAdelta * v)
{
  TLAmon * Pmon;
  TLAdelta D;
  /* D = v - Beta_i */
  LAdelta_minus(&D, v, &(LAvar[i].assign));
  if (D.val.sval.num == 0 && D.delta.sval.num == 0)
    return;
  for (Pmon = mon + C[i]; Pmon != mon; Pmon = mon + Pmon->ln)
    {
      TLAvar j = Pmon->l; /* basic variable affected */
      TLAmon * Pmon2 = mon + C[j]; /* monom to get its coefficient */
      /* Pmon relate to the modified literal */
      assert(Pmon->c == i);
      /* Pmon2 relate to the basic variable */
      assert(Pmon2->l == Pmon->l);
      assert(Pmon2->l == Pmon2->c);
      /* Beta_j : LAvar[j].assign */
      /* a_ji : Pmon->a */
      /* a_jj : Pmon2->a */
      /* Beta_j' - Beta_j = - aji * (v - Beta_i) / ajj */
      LAvar_update(j, &D, &Pmon->a, &Pmon2->a);
    }
  LAvar_assign(i, v);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief exchange role of a basic and a non-basic variable
   \param i basic variable
   \param j non-basic variable */
static void
pivot(TLAvar i, TLAvar j)
{
  TLAmon * Pmon;
  TLAsigned diag;
  assert(!L[j]);
  assert(C[i] && mon[C[i]].c == i && mon[C[i]].l == i && !mon[C[i]].ln);
  assert(LAvar[i].basic && !LAvar[j].basic);
  LAvar[i].basic = 0;
  LAvar[j].basic = 1;
  L[j] = L[i];
  L[i] = 0;
  for (Pmon = mon + L[j]; Pmon != mon; Pmon = mon + Pmon->cn)
    {
      /* save a_jj in LAvar[j] */
      if (Pmon->c == j)
	diag = Pmon->a; /* diag = a_jj */
      /* change variable in the whole linear expression */
      Pmon->l = j;
    }
  for (Pmon = mon + C[j]; Pmon != mon;)
    {
      TLAvar k = Pmon->l; /* basic var k definition is modified */
      TLAsigned c = Pmon->a; /* c = a_kj*/
      assert(Pmon->c == j);
      Pmon = mon + Pmon->ln;
      if (k != j)
	linear_expr_update(k, j, diag, c); /* L_k = a_jj L_k - a_kj L_j */
    }
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief exchange role of a basic and a non-basic variable, and update
   \param i basic variable
   \param j non-basic variable
   \param v value of variable i */
static void
pivot_and_update(TLAvar i, TLAvar j, TLAdelta * v)
{
  pivot(i, j);
  update(i, v);
}

/*
  --------------------------------------------------------------
  Simplex interface
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief find an assignment satisfying all constraints
   \return SAT or UNSAT depending of the status */
Tstatus
simplex_solve(void)
{
  TLAvar i;
  TLAmon * Pmon;
  if (LAstatus == UNSAT)
    return LAstatus;
  while (1)
    {
      TLAsigned c;
    next_var:
      CHECK_INVARIANT;
      if (heap_var_empty())
	break;
      i = heap_var_remove_min();
      assert(LAvar[i].basic && LAvar[i].mark_unsat);
      LAvar[i].mark_unsat = 0;
      c = mon[C[i]].a;
      if ((LAvar[i].boundmask & 1) &&
	  LAdelta_less(&LAvar[i].assign, &LAvar[i].bound[0]))
	{
	  /* Find a variable to increase */
	  Pmon = mon + L[i];
	  /* Skip constant term */
	  if (!Pmon->c)
	    Pmon = mon + Pmon->cn;
	  for (; Pmon != mon; Pmon = mon + Pmon->cn)
	    if (Pmon->c != i &&
		LAvar_notied_bound(Pmon->c, LAsigned_sign_diff(&Pmon->a, &c)))
	      {
		pivot_and_update(i, Pmon->c, &LAvar[i].bound[0]);
		goto next_var;
	      }
	  backtrack_status();
	  simplex_conflict_var = i;
	  simplex_conflict_upper = 0;
	  LAstatus = UNSAT;
	  CHECK_INVARIANT;
	  return LAstatus;
	}
      if ((LAvar[i].boundmask & 2) &&
	  LAdelta_less(&LAvar[i].bound[1], &LAvar[i].assign))
	{
	  Pmon = mon + L[i];
	  /* Skip constant term */
	  if (!Pmon->c)
	    Pmon = mon + Pmon->cn;
	  for (; Pmon != mon; Pmon = mon + Pmon->cn)
	    if (Pmon->c != i &&
		LAvar_notied_bound(Pmon->c, !LAsigned_sign_diff(&Pmon->a, &c)))
	      {
		pivot_and_update(i, Pmon->c, &LAvar[i].bound[1]);
		goto next_var;
	      }
	  backtrack_status();
	  simplex_conflict_var = i;
	  simplex_conflict_upper = 1;
	  LAstatus = UNSAT;
	  CHECK_INVARIANT;
	  return LAstatus;
	}
    }
  LAstatus = SAT;
  modified_save();
  CHECK_INVARIANT;
  return LAstatus;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief assert upper bound
   \return UNDEF, SAT or UNSAT depending of the status
   \remark simplex_solve() is required for completeness if UNDEF is returned */
Tstatus
simplex_assert_upper_bound(TLAvar i, TLAdelta delta, Tlit reason)
{
  if (LAstatus == UNSAT)
    return LAstatus;
  LAstatus = UNDEF;

  CHECK_INVARIANT;
  if ((LAvar[i].boundmask & 2u) && LAdelta_leq(&LAvar[i].bound[1], &delta))
    return (LAstatus = SAT);
  if ((LAvar[i].boundmask & 1u) && LAdelta_less(&delta, &LAvar[i].bound[0]))
    {
      backtrack_status();
      simplex_conflict_var = i;
      simplex_conflict_new_lit = reason;
      simplex_conflict_upper = 0;
      return (LAstatus = UNSAT);
    }
  if (LAdelta_less(&delta, &LAvar[i].assign))
    {
      if (LAvar[i].basic)
	{
	  LAvar[i].mark_unsat = 1;
	  heap_var_insert(i);
	}
      else
	update(i, &delta);
    }
  assert(((LAvar[i].boundmask & 2u) != 0) ^ (LAvar[i].reason[1] == 0));
  backtrack_upper_bound(i, LAvar[i].reason[1], &LAvar[i].bound[1]);
  LAvar[i].bound[1] = delta;
  LAvar[i].reason[1] = reason;
  LAvar[i].boundmask |= 2u;
  CHECK_INVARIANT;
  return LAstatus;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief assert upper bound
   \return UNDEF, SAT or UNSAT depending of the status
   \remark simplex_solve() is required for completeness if UNDEF is returned */
Tstatus
simplex_assert_lower_bound(TLAvar i, TLAdelta delta, Tlit reason)
{
  if (LAstatus == UNSAT)
    return LAstatus;
  LAstatus = UNDEF;

  CHECK_INVARIANT;
  if ((LAvar[i].boundmask & 1) && LAdelta_leq(&delta, &LAvar[i].bound[0]))
    return (LAstatus = SAT);
  if ((LAvar[i].boundmask & 2) && LAdelta_less(&LAvar[i].bound[1], &delta))
    {
      backtrack_status();
      simplex_conflict_var = i;
      simplex_conflict_new_lit = reason;
      simplex_conflict_upper = 1;
      return (LAstatus = UNSAT);
    }
  if (LAdelta_less(&LAvar[i].assign, &delta))
    {
      if (LAvar[i].basic)
	{
	  LAvar[i].mark_unsat = 1;
	  heap_var_insert(i);
	}
      else
	update(i, &delta);
    }
  assert(((LAvar[i].boundmask & 1u) != 0) ^ (LAvar[i].reason[0] == 0));
  backtrack_lower_bound(i, LAvar[i].reason[0], &LAvar[i].bound[0]);
  LAvar[i].bound[0] = delta;
  LAvar[i].reason[0] = reason;
  LAvar[i].boundmask |= 1u;
  CHECK_INVARIANT;
  return LAstatus;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief assert a new equality
   \return UNDEF, SAT or UNSAT depending of the status
   \remark simplex_solve() is required for completeness if UNDEF is returned */
static int
assert_equality(TLAmon_id m)
{
  TLAmon * Pmon;
  TLAvar i;
  TLAsigned diag;
  TLAdelta delta;

  if (LAstatus == UNSAT)
    return LAstatus;

  CHECK_INVARIANT;
  /* eliminate basic variables */
  m = linear_expr_eliminate_basic(m);
  /* 0 = 0 */
  if (!m)
    return LAstatus;
  Pmon = mon + m;
  if (!Pmon->c)
    Pmon = mon + Pmon->cn;
  /* c = 0 */
  if (Pmon == mon)
    {
      backtrack_status();
      LAstatus = UNSAT;
      CHECK_INVARIANT;
      return LAstatus;
    }
  /* choose one non-basic variable and make it basic */
  /* IMPROVE: we could chose another one than the first */
  i = Pmon->c;
  diag = Pmon->a;
  L[i] = m;
  LAvar[i].basic = 1;
  /* compute its value */
  linear_expr_val(L[i], i, &delta);
  update(i, &delta);
  /* add in C[i] for all vars i */
  for (m = L[i]; m; m = mon[m].cn)
    {
      mon_C_add(m);
      mon[m].l = i;
    }
  /* remove definition from all constraints */
  Pmon = mon + C[i];
  assert(Pmon->l == i);
  /* skip the added constraint */
  Pmon = mon + Pmon->ln;
  for (; Pmon != mon;)
    {
      TLAvar k = Pmon->l; /* basic var k definition is modified */
      TLAsigned c = Pmon->a; /* c = a_kj*/
      assert(k && k != i);
      Pmon = mon + Pmon->ln;
      linear_expr_update(k, i, diag, c); /* L_k = a_jj L_k - a_kj L_j */
    }
  CHECK_INVARIANT;
  return LAstatus;
}

/*
  --------------------------------------------------------------
  Internal interface
  --------------------------------------------------------------
*/

static unsigned buf_n = 0;
static unsigned buf_size = 0;
static TLAmon_id * buf_mon;

void
simplex_constraint_push(unsigned n, TLAvar *vars, TLAsigned *coefs)
{
  unsigned i;
  TLAmon_id first, tmp;
  if (!n)
    my_error("simplex_constraint_push: inconsistency\n");
  first = mon_new();
  mon[first].cn = 0;
  mon[first].ln = 0;
  mon[first].lp = 0;
  mon[first].l = 0;
  mon[first].c = vars[0];
  mon[first].a = coefs[0];
  tmp = first;
  for (i = 1; i < n; i++)
    {
      TLAmon_id current = mon_new();
      mon[current].cn = 0;
      mon[current].ln = 0;
      mon[current].lp = 0;
      mon[current].l = 0;
      mon[current].c = vars[0];
      mon[current].a = coefs[0];
      mon[tmp].cn = current;
      if (mon[tmp].c >= mon[tmp].c)
	my_error("simplex_constraint_push: inconsistency\n");
     tmp = current;
    }
  assert_equality(first);
}

/*
  --------------------------------------------------------------
  Public interface
  --------------------------------------------------------------
*/

void
simplex_init(void)
{
  if ((-1 >> 1) != -1 ||
      sizeof(long long) != 2 * sizeof(long) ||
      ((((unsigned long) -253) >> (sizeof(signed long) * CHAR_BIT - 1)) != 1)
      )
    my_error("Linear arithmetic incompatible with compiler or architecture\n");
  LAvar_init();
  heap_var_init();
  mon_init();
  modified_init();
  backtrack_init();
  buf_size = 4;
  buf_n = 0;
  MY_MALLOC(buf_mon, buf_size * sizeof(TLAmon_id));
}

/*--------------------------------------------------------------*/

void
simplex_done(void)
{
  free(buf_mon);
  backtrack_done();
  heap_var_done();
  LAvar_done();
  modified_done();
  mon_done();
}

#if 0

/*--------------------------------------------------------------*/

void
LA_push(Tclue clue)
{
  
}

/*--------------------------------------------------------------*/

#ifdef PROOF
Tlist
LA_conflict(Tproof_id * proof_id)
{
}

#else
Tlist
LA_conflict(void)
{
}

#endif

/*--------------------------------------------------------------*/

Tlist
LA_premisses(const Tclue clue)
{
}

/*--------------------------------------------------------------*/

void
LA_lemmas(Ttable table)
{
}

/*--------------------------------------------------------------*/

bool
LA_has_lemma(void)
{
}

/*--------------------------------------------------------------*/

bool
LA_eq_queue_empty(void)
{
}

/*--------------------------------------------------------------*/

Tclue
LA_eq_queue_pop(void)
{
}

/*--------------------------------------------------------------*/

bool
LA_model_eq_queue_empty(void)
{
}

/*--------------------------------------------------------------*/

Tclue
LA_model_eq_queue_pop(void)
{
}
#endif

/*
  --------------------------------------------------------------
  Invariant
  --------------------------------------------------------------
*/

static void
LA_invariant(void)
{
  TLAvar i;
  TLAmon * Pmon;
  unsigned tmp;
  assert(mon->cn == 0);
  assert(mon->ln == 0);
  assert(mon->lp == 0);
  assert(mon->l == 0);
  assert(mon->c == 0);
  for (i = 1; i < LAvar_n; i++)
    {
      /* First element in column should have no previous element */
      assert(!C[i] || mon[C[i]].lp == 0);
      /* Basic variables should be refered in one and only one constraint */
      if (LAvar[i].basic)
	assert(L[i] && C[i] && mon[C[i]].ln == 0);
      for (Pmon = mon + C[i]; Pmon != mon; Pmon = mon + Pmon->ln)
	{
	  /* Column C[i] only contains monoms with column index i */
	  assert(Pmon->c == i);
	  /* the lp element should be the previous element */
	  if (Pmon->ln)
	    assert(Pmon == mon + mon[Pmon->ln].lp);
	}
      tmp = 0;
      for (Pmon = mon + L[i]; Pmon != mon; Pmon = mon + Pmon->cn)
	{
	  /* Line L[i] only contains monoms with line index i */
	  assert(Pmon->l == i);
	  /* Line L[i] contains monoms sorted with respect to column index */
	  if (Pmon->cn)
	    assert(mon[Pmon->cn].c > Pmon->c);
	  tmp += LAvar[Pmon->c].basic;
	}
      /* Line L[i] should countain at most one basic variable */
      assert (!L[i] || tmp == 1);
      /* Bounds should be consistent */
      if (LAvar[i].boundmask == 3)
	assert(LAdelta_leq(&LAvar[i].bound[0], &LAvar[i].bound[1]));
      /* if SAT status, no variable should be marked (unsat) */
      if (LAstatus == SAT)
	{
	  assert(!LAvar[i].mark_unsat);
	  assert(!LAvar[i].mark);
	  assert(LAdelta_leq(&LAvar[i].bound[0], &LAvar[i].assign));
	  assert(LAdelta_leq(&LAvar[i].assign, &LAvar[i].bound[1]));
	}
      if (!LAvar[i].basic || !LAvar[i].mark_unsat)
	{
	  /* Nonbasic vars should be within bounds */
	  /* Basic vars should be within bounds or marked unsat */
	  if (LAvar[i].boundmask == 1)
	    assert(LAdelta_eq(&LAvar[i].bound[0], &LAvar[i].assign));
	  if (LAvar[i].boundmask == 2)
	    assert(LAdelta_eq(&LAvar[i].bound[1], &LAvar[i].assign));
	  if (LAvar[i].boundmask == 3)
	    assert(LAdelta_eq(&LAvar[i].bound[0], &LAvar[i].assign) ||
		   LAdelta_eq(&LAvar[i].bound[1], &LAvar[i].assign));
	}

      /* non marked variables should have backup and current assign equal */
      if (!LAvar[i].mark)
	assert(LAdelta_eq(&LAvar[i].assign, &LAvar[i].assign2));
      /* equality constraints should always be satisfied */
      if (LAvar[i].basic)
	{
	  TLAdelta delta;
	  LAdelta_set_zero(&delta);
	  for (Pmon = mon + L[i]; Pmon != mon; Pmon = mon + Pmon->cn)
	    LAdelta_addmult(&delta, &LAvar[Pmon->c].assign, &Pmon->a);
	  assert(LAdelta_is_zero(&delta));
	}
    }
}

/*
  --------------------------------------------------------------
  Tests
  --------------------------------------------------------------
*/

void
LA_print(void)
{
  TLAvar i;
  for (i = 1; i < LAvar_n; i++)
    if (LAvar[i].basic)
      {
	printf("x_%d %s: ",i, (i<10)?"  ":(i<100)?" ":"");
	linear_expr_print(L[i]);
      }
  for (i = 1; i < LAvar_n; i++)
    {
      printf("x_%d %s= ",i, (i<10)?"  ":(i<100)?" ":"");
      LAdelta_print(&LAvar[i].assign);
      printf("\n");
    }
  for (i = 1; i < LAvar_n; i++)
    if (LAvar[i].boundmask)
      {
	if (LAvar[i].boundmask & 1)
	  {
	    LAdelta_print(&LAvar[i].bound[0]);
	    printf(" <= ");
	  }
	printf("x_%d", i);
	if (LAvar[i].boundmask & 2)
	  {
	    printf(" <= ");
	    LAdelta_print(&LAvar[i].bound[1]);
	  }
	printf("\n");
      }

}

#if 0

/*--------------------------------------------------------------*/

static int
cmp_column(const TLAmon_id * Pm1, const TLAmon_id * Pm2)
{
  return (((int)(mon[*Pm1].c)) - ((int)(mon[*Pm2].c)));
}

/*--------------------------------------------------------------*/

static void
LA_constraint_push_part(unsigned var, signed coef)
{
  if (!coef)
    return;
  if (buf_n + 1 == buf_size)
    {
      buf_size <<= 1;
      MY_REALLOC(buf_mon, buf_size * sizeof(TLAmon_id));
    }
  buf_mon[buf_n] = mon_new();
  mon[buf_mon[buf_n]].cn = 0;
  mon[buf_mon[buf_n]].ln = 0;
  mon[buf_mon[buf_n]].lp = 0;
  mon[buf_mon[buf_n]].l = 0;
  mon[buf_mon[buf_n]].c = var;
  mon[buf_mon[buf_n]].a.sval = coef;
  buf_n++;
}

/*--------------------------------------------------------------*/

static void
LA_constraint_push_end(void)
{
  unsigned i;
#ifdef DEBUG
  /* sort and remove monoms on same variable */
  qsort(buf_mon, buf_n, sizeof(TLAmon_id), (TFcmp)cmp_column);
  for (i = 1; i < buf_n; i++)
    if (mon[buf_mon[i]].c == mon[buf_mon[i - 1]].c)
      my_error("LA_constraint_push: misuse\n");
#endif
  /* link the monoms */
  for (i = 0; i < buf_n - 1; i++)
    mon[buf_mon[i]].cn = buf_mon[i + 1];
  assert_equality(buf_mon[0]);
  /* ready for next constraint */
  buf_n = 0;
}

/*--------------------------------------------------------------*/

static void
LA_test1(void)
{
  /*
     3x + 2y -  z =  1
     2x - 2y + 4z =  2
    -2x +  y - 2z =  0
  */
  LA_init();
  LA_constraint_push_part(0,-1);
  LA_constraint_push_part(1, 3);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_print();
  LA_constraint_push_part(0,-2);
  LA_constraint_push_part(1, 2);
  LA_constraint_push_part(2,-2);
  LA_constraint_push_part(3, 4);
  LA_constraint_push_end();
  LA_print();
  LA_constraint_push_part(0, 0);
  LA_constraint_push_part(1,-2);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(3,-2);
  LA_constraint_push_end();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_done();
}

/*--------------------------------------------------------------*/

static void
LA_test2(void)
{
  TLAdelta delta;
  /*
    2x + y >= 2
    4x + 3y <= 12
    (1/2) <= x <= 2
    y >= 0
  */
  LA_init();
  LA_constraint_push_part(1, 2);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1, 4);
  LA_constraint_push_part(2, 3);
  LA_constraint_push_part(4,-1);
  LA_constraint_push_end();
  LAdelta_int(&delta, 2);
  assert_upper_bound(LA_ext_var(1), delta);
  LAdelta_rat(&delta, 1, 2);
  assert_lower_bound(LA_ext_var(1), delta);
  LAdelta_int(&delta, 0);
  assert_lower_bound(LA_ext_var(2), delta);
  LAdelta_int(&delta, 2);
  assert_lower_bound(LA_ext_var(3), delta);
  LAdelta_int(&delta, 12);
  assert_upper_bound(LA_ext_var(4), delta);
  LA_print();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_print();
  LA_done();
}

/*--------------------------------------------------------------*/

static void
LA_test3(void)
{
  TLAdelta delta;
  /*
    y - x >= 0
    x - y - 1 >= 0
  */
  LA_init();
  LA_constraint_push_part(1,-1);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(0,-1);
  LA_constraint_push_part(1, 1);
  LA_constraint_push_part(2,-1);
  LA_constraint_push_part(4,-1);
  LA_constraint_push_end();
  LAdelta_int(&delta, 0);
  assert_lower_bound(LA_ext_var(3), delta);
  assert_lower_bound(LA_ext_var(4), delta);
  LA_print();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_print();
  LA_done();
}

/*--------------------------------------------------------------*/

static void
LA_test4(void)
{
  TLAdelta delta;
  /*
    2y - 2x >= 1
    y - 2x <= -1
  */
  LA_init();
  LA_constraint_push_part(1,-2);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1,-2);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(4,-1);
  LA_constraint_push_end();
  LAdelta_int(&delta, 1);
  assert_lower_bound(LA_ext_var(3), delta);
  LAdelta_int(&delta, -1);
  assert_upper_bound(LA_ext_var(4), delta);
  LA_print();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_print();
  LA_done();
}

/*--------------------------------------------------------------*/

static void
LA_test5(void)
{
  TLAdelta delta;
  /*
    y - x >= 0
    2y - x <= -1
    2y + x >= 1
  */
  LA_init();
  LA_constraint_push_part(1,-1);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1,-1);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(4,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1, 1);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(5,-1);
  LA_constraint_push_end();
  LAdelta_int(&delta, 0);
  assert_lower_bound(LA_ext_var(3), delta);
  LAdelta_int(&delta, -1);
  assert_upper_bound(LA_ext_var(4), delta);
  LAdelta_int(&delta, 1);
  assert_lower_bound(LA_ext_var(5), delta);
  LA_print();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_print();
  LA_done();
}

/*--------------------------------------------------------------*/

static void
LA_test6(void)
{
  TLAdelta delta;
  /*
    y - x >= 0
    2y - x <= -1
    2y + x >= -3
  */
  LA_init();
  LA_constraint_push_part(1,-1);
  LA_constraint_push_part(2, 1);
  LA_constraint_push_part(3,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1,-1);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(4,-1);
  LA_constraint_push_end();
  LA_constraint_push_part(1, 1);
  LA_constraint_push_part(2, 2);
  LA_constraint_push_part(5,-1);
  LA_constraint_push_end();
  LAdelta_int(&delta, 0);
  assert_lower_bound(LA_ext_var(3), delta);
  LAdelta_int(&delta, -1);
  assert_upper_bound(LA_ext_var(4), delta);
  LAdelta_int(&delta, -3);
  assert_lower_bound(LA_ext_var(5), delta);
  LA_print();
  printf("Returned %s\n", simplex_solve()==SAT?"SAT":"UNSAT");
  LA_print();
  LA_done();
}

/*--------------------------------------------------------------*/

int
main(void)
{
  LA_test6();
  return 1;
}

#endif
