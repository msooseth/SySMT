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
   Module for representing formulas and terms
*/

/* -------------------------------------------------------------- */
/* #define DEBUG_TYPE_VARIABLES */
/* #define DEBUG_DAG */
#ifdef DEBUG
#define DAG_CHECK
#endif
#warning misc, Pflag, DAG, properties should now be outside TSsymb
#warning 2DD: changed dp_mask to unsigned for compatibility

#include "config.h"

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "options.h"

#include "general.h"
#include "assoc.h"
#include "hash.h"
#include "list.h"
#include "table.h"
#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "DAG-print.h"
#include "DAG-prop.h"
#include "DAG-tmp.h"
#include "DAG-symb-DAG.h"

/* #define DMEM */
#ifdef MEM
#include "DAG-stat.h"
#warning compiling with memory checking
#endif

/* PF option to disable taking symmetry of equality into account */
/**
   \addtogroup arguments_user

   - --disable-sym-eq

   Disables symmetry of equality (EXPERIMENTAL - DO NOT USE).*/
static bool disable_sym_eq = false;
static int attr_max;

/* PF mask of arithmetic constants
   should be set by arithmetic itself */
unsigned dp_mask_arith = 0;

Tsort     SORT_BOOLEAN = 0;
char    * SORT_BOOLEAN_STR = "Bool";

Tsymb     BOOLEAN_TRUE = DAG_SYMB_NULL;
Tsymb     BOOLEAN_FALSE = DAG_SYMB_NULL;
char    * BOOLEAN_TRUE_STR = "true";
char    * BOOLEAN_FALSE_STR = "false";

Tsymb     CONNECTOR_NOT = DAG_SYMB_NULL;
Tsymb     CONNECTOR_OR = DAG_SYMB_NULL;
Tsymb     CONNECTOR_XOR = DAG_SYMB_NULL;
Tsymb     CONNECTOR_AND = DAG_SYMB_NULL;
Tsymb     CONNECTOR_IMPLIES = DAG_SYMB_NULL;
Tsymb     CONNECTOR_EQUIV = DAG_SYMB_NULL;
Tsymb     CONNECTOR_ITE = DAG_SYMB_NULL;
char    * CONNECTOR_NOT_STR = "not";
char    * CONNECTOR_OR_STR = "or";
char    * CONNECTOR_XOR_STR = "xor";
char    * CONNECTOR_AND_STR = "and";
char    * CONNECTOR_IMPLIES_STR = "=>";
char    * CONNECTOR_EQUIV_STR = "=";
char    * CONNECTOR_ITE_STR = "ite";

Tsymb     PREDICATE_EQ = DAG_SYMB_NULL;
char    * PREDICATE_EQ_STR = "=";

Tsymb     PREDICATE_DISTINCT = DAG_SYMB_NULL;
char    * PREDICATE_DISTINCT_STR = "distinct";

Tsymb     FUNCTION_ITE = DAG_SYMB_NULL;
char    * FUNCTION_ITE_STR = "ite";

Tsymb     QUANTIFIER_EXISTS = DAG_SYMB_NULL;
Tsymb     QUANTIFIER_FORALL = DAG_SYMB_NULL;

/** \brief String of the predefined symbol for existential quantification. */
char    * QUANTIFIER_EXISTS_STR = "exists";
/** \brief String of the predefined symbol for universal quantification. */
char    * QUANTIFIER_FORALL_STR = "forall";

/** \brief String of the predefined symbol for let construction. */
char    * LET_STR = "let";
/** \brief Predefined symbol for let construction. */
Tsymb     LET = DAG_SYMB_NULL;

/** \brief Predefined symbol for lambda-abstraction operator. */
Tsymb     LAMBDA = DAG_SYMB_NULL;
/** \brief Predefined symbol for beta reduction. */
Tsymb     APPLY_LAMBDA = DAG_SYMB_NULL;

/** \brief String of the predefined symbol for lambda abstraction. */
char    * LAMBDA_STR = "lambda";
/** \brief String of the predefined symbol for beta reduction. */
char    * APPLY_LAMBDA_STR = "apply";

TDAG      DAG_TRUE = DAG_SYMB_NULL;
TDAG      DAG_FALSE = DAG_SYMB_NULL;

/** \brief The DAG table: stored in a single chunk of memory */
Tstack_SDAG DAG_table;
/** \brief Hook functions called when DAG table is resized
    and when DAG is freed */

TSstack(_hook_resize, TDAG_hook_resize);
TSstack(_hook_free, TDAG_hook_free);

Tstack_hook_resize stack_hook_resize;
Tstack_hook_free stack_hook_free;

/** \brief Freed entry in the DAG table */
TDAG DAG_freed = DAG_NULL;

#ifdef MEM
/* #define DAG_SPY(DAG) (DAG==230 || DAG==133) */
#define DAG_SPY(DAG) (DAG == 50)
/* #define DAG_SPY(DAG) (false) */
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
DAG_table_print(void)
{
  TDAG DAG;
  fprintf(stderr, "DAG_table: size = %u, address = %p\n",
          DAG_table->size, DAG_table);
  fprintf(stderr, " DAG symb sort refs args\n");
  for (DAG = 1; DAG < DAG_table->size; ++DAG)
    {
      if (DAG_table->data[DAG].symb != DAG_SYMB_NULL)
	{
	  int i;
	  fprintf(stderr, "%4u %4u %4u %4u", 
		  DAG, DAG_table->data[DAG].symb,
		  DAG_table->data[DAG].sort,
		  DAG_table->data[DAG].gc_count);
	  fprintf(stderr, " {");
	  for (i = 0; i < DAG_table->data[DAG].arity; ++i)
	    if (i == 0)
	      fprintf(stderr, "%i", DAG_table->data[DAG].PDAG[i]);
	    else
	      fprintf(stderr, ",%i", DAG_table->data[DAG].PDAG[i]);
	  fprintf(stderr, "}\n");
	}
      else
	{
	  fprintf(stderr, "%4u **** **** ****\n", DAG);
	}
    }
  if (DAG_freed != DAG_NULL)
    {
      TDAG DAG = DAG_freed;
      fprintf(stderr, "Freed positions:");
      do
	{
	  fprintf(stderr, " %u", DAG);
	  DAG = (TDAG) DAG_table->data[DAG].hash_key;
	}
      while (DAG != DAG_NULL);
      fprintf(stderr, "\n");
    }
}
#endif

/*
  --------------------------------------------------------------
  DAG stuff
  --------------------------------------------------------------
*/

int
DAG_equal(TDAG DAG1, TDAG DAG2)
{
  return DAG1 == DAG2;
}

/*--------------------------------------------------------------*/

unsigned
DAG_hash(TDAG DAG)
{
  return DAG_table->data[DAG].hash_key;
}

/*--------------------------------------------------------------*/

static int
sort_cmp(Tsort sort1, Tsort sort2)
{
  unsigned i;
  int j;
  if ((j = strcmp(DAG_sort_name(sort1), DAG_sort_name(sort2))) != 0)
    return j;
  if (DAG_sort_arity(sort1) < DAG_sort_arity(sort2))
    return -1;
  if (DAG_sort_arity(sort1) > DAG_sort_arity(sort2))
    return 1;
  if (DAG_sort_arity(sort1) != DAG_SORT_NARY)
    {
      for (i = 0; i < DAG_sort_arity(sort1); i++)
	if ((j = sort_cmp(DAG_sort_sub(sort1)[i], DAG_sort_sub(sort2)[i])) != 0)
	  return j;
    }
  else
    for (i = 0; i < 2; i++)
      if ((j = sort_cmp(DAG_sort_sub(sort1)[i], DAG_sort_sub(sort2)[i])) != 0)
	return j;	
  my_error("sort_cmp: internal error\n");  
  return 0;
}

/*--------------------------------------------------------------*/

static int
symb_cmp(Tsymb symb1, Tsymb symb2)
{
  int i;
  if (symb1 == symb2)
    return 0;
  if (DAG_symb_key(symb1) < DAG_symb_key(symb2))
    return -1;
  if (DAG_symb_key(symb1) > DAG_symb_key(symb2))
    return 1;
  if ((i = strcmp(DAG_symb_name(symb1), DAG_symb_name(symb2))) != 0)
    return i;
  if ((i = sort_cmp(DAG_symb_sort(symb1), DAG_symb_sort(symb2))) != 0)
    return i;
  my_error ("symb_cmp: internal error\n");
  return 0;
}

/*--------------------------------------------------------------*/

int
DAG_cmp(TDAG DAG1, TDAG DAG2)
/* PF ordering function on DAGs: returns -1, 0, 1
   for qsort, one more derefencing needed: see DAG_cmp_q */
{
  unsigned i;
  int j;
  if (DAG1 == DAG2)
    return 0;
  if (DAG_hash(DAG1) < DAG_hash(DAG2))
    return -1;
  if (DAG_hash(DAG1) > DAG_hash(DAG2))
    return 1;
  if ((j = symb_cmp(DAG_symb(DAG1), DAG_symb(DAG2))) != 0)
    return j;
  if (DAG_arity(DAG1) < DAG_arity(DAG2))
    return -1;
  if (DAG_arity(DAG1) > DAG_arity(DAG2))
    return 1;
  for (i = 0; i < DAG_arity(DAG1); i++)
    if ((j = DAG_cmp(DAG_arg(DAG1, i), DAG_arg(DAG2, i))) != 0)
      return j;
  my_error ("DAG_cmp: internal error\n");
  return 0;
}

/*--------------------------------------------------------------*/

int
DAG_cmp_q(TDAG *PDAG1, TDAG *PDAG2)
/* PF ordering function on DAGs: returns -1, 0, 1
   like a compare for qsort */
{
  return DAG_cmp(*PDAG1, *PDAG2);
}

/*--------------------------------------------------------------*/

int
DAG_identity(TDAG DAG1, TDAG DAG2)
{
  /* DD+PF in principle, this function will never be called with dags
     with different top symbols */
  assert(DAG_symb(DAG1) == DAG_symb(DAG2));
  if (DAG_hash(DAG1) != DAG_hash(DAG2) || DAG_arity(DAG1) != DAG_arity(DAG2))
    return 0;
  return memcmp(DAG_args(DAG1), DAG_args(DAG2), DAG_arity(DAG1) * sizeof(TDAG)) == 0;
}

/*--------------------------------------------------------------*/

static TDAG
DAG_gc_inc(TDAG DAG)
{
  assert(DAG_table->data[DAG].gc_count < UINT32_MAX);
  ++DAG_table->data[DAG].gc_count;
  return DAG;
}

/*--------------------------------------------------------------*/

static void
DAG_hook_free(TDAG DAG)
{
  unsigned i;
  for (i = 0; i < stack_hook_free->size; i++)
    stack_hook_free->data[i](DAG);
}

/*--------------------------------------------------------------*/

static TDAG
DAG_gc_dec(TDAG DAG)
{
  unsigned i;
#ifdef DEBUG_DAG
  my_DAG_message("DAG_gc_dec %p %D\n", DAG, DAG);
#endif
  if (DAG_table->data[DAG].gc_count == 0)
    my_error ("DAG_gc_dec: under limit\n");
  if (--DAG_table->data[DAG].gc_count > 0)
    return DAG;
#ifdef DEBUG_DAG
  my_DAG_message("freeing DAG %p: %D\n", DAG, DAG);
#endif
  assert(!DAG_table->data[DAG].misc);
  for (i = 0; i < DAG_arity(DAG); i++)
    {
#ifdef MEM
      if (DAG_SPY(DAG_arg(DAG, i)))
	{
	  my_DAG_message("Released %d from %d\n", DAG_arg(DAG, i), DAG);
	  breakpoint();
	}
#endif
      DAG_gc_dec(DAG_arg(DAG, i));
    }
  hash_remove(DAG_symb_hash(DAG_symb(DAG)), DAG_ptr_of(DAG));
  free(DAG_args(DAG));
#ifdef DAG_CHECK
  memset(&DAG_table->data[DAG], 0, sizeof(struct TSDAG));
#endif
  DAG_table->data[DAG].symb = DAG_SYMB_NULL;
  DAG_table->data[DAG].hash_key = (unsigned) DAG_freed;
  DAG_freed = DAG;
  DAG_hook_free(DAG);
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

static void
DAG_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  unsigned i;
  for (i = 0; i < stack_hook_resize->size; i++)
    stack_hook_resize->data[i](old_alloc, new_alloc);
}

/*--------------------------------------------------------------*/
static Tstack_sort sort_stack = NULL;

TDAG
DAG_new(Tsymb symb, unsigned arity, TDAG * PDAG)
{
  TDAG DAG1, DAG2;
  unsigned i;
  unsigned key;
  int recycled; /* 1 if DAG created from DAG_freed, 0 if fresh memory */
  if (!symb)
    my_error ("DAG_new: null symbol\n");
#ifdef DAG_CHECK
  for (i = 0; i < arity; i++)
    if (!PDAG[i])
      my_error ("DAG_new: unused subdag\n");
#endif
  assert(arity <= UINT_MAX);
  if (DAG_freed != DAG_NULL)
    {
      DAG1 = DAG_freed;
      DAG_freed = (TDAG) DAG_table->data[DAG1].hash_key;
      recycled = 1;
    }
  else
    {
      DAG1 = DAG_table->size;
      stack_inc_hook(DAG_table, DAG_hook_resize);
      recycled = 0;
    }
  DAG_table->data[DAG1].symb = symb;
  stack_inc_n(sort_stack, arity);
  for (i = 0; i < arity; i++)
    sort_stack->data[i] = DAG_sort(PDAG[i]);
  DAG_table->data[DAG1].sort = DAG_symb_check(symb, arity, sort_stack->data);
  stack_reset(sort_stack);
  if (!DAG_table->data[DAG1].sort)
    my_error ("DAG_new: unable to determine sort\n");
  if (symb == PREDICATE_EQ && arity == 2 && !disable_sym_eq &&
      DAG_cmp(PDAG[0],PDAG[1]) > 0)
    {
      TDAG tmp = PDAG[1];
      PDAG[1] = PDAG[0];
      PDAG[0] = tmp;
    }
  if (arity >= 1u << 31)
    my_error("DAG arity too large\n");
  DAG_table->data[DAG1].arity = arity;
  DAG_table->data[DAG1].PDAG = PDAG;
  DAG_table->data[DAG1].gc_count = 0;
  key = hash_one_at_a_time_u_inc(0, DAG_symb_key(symb));
  key = hash_one_at_a_time_u_inc(key, arity);
  for (i = 0; i < arity; i++)
    key = hash_one_at_a_time_u_inc(key, DAG_table->data[PDAG[i]].hash_key);
  DAG_table->data[DAG1].hash_key = hash_one_at_a_time_inc_end(key);
  /*
    key = (int) Psymb;
    key = key << 1 ^ key >> 1 ^ arity;
    for (i = 0; i < arity; i++)
    key = key << 1 ^ key >> 1 ^ DAG_arg(DAG1, i)->hash_key;
  */
  DAG2 = DAG_of_ptr(hash_lookup(DAG_symb_hash(symb), DAG_ptr_of(DAG1)));
  if (DAG2)
    {
      if (recycled)
	{
	  DAG_table->data[DAG1].hash_key = (unsigned) DAG_freed;
	  DAG_table->data[DAG1].symb = DAG_SYMB_NULL;
	  DAG_freed = DAG1;
	}
      else
	stack_dec(DAG_table);
      free(PDAG);
      return DAG2;
    }
  DAG_table->data[DAG1].misc = 0;
  DAG_table->data[DAG1].ground = 0;
  DAG_table->data[DAG1].quant = quantifier(symb);
  for (i = 0; i < DAG_table->data[DAG1].arity; i++) 
  {
    DAG_table->data[DAG1].quant |= DAG_table->data[PDAG[i]].quant;
    DAG_gc_inc(PDAG[i]);
#ifdef MEM
    if (DAG_SPY(PDAG[i]))
      {
	my_DAG_message("Used %d in %d\n", PDAG[i], DAG1);
	breakpoint();
      }
#endif
  }
  hash_insert(DAG_symb_hash(symb), DAG_ptr_of(DAG1));

#ifdef DEBUG_TYPE_VARIABLES
  my_DAG_message ("DAG_new: %D has sort %S.\n", DAG1, DAG_sort(DAG1));
#endif
  return DAG1;
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_args(Tsymb symb, ...)
{
  va_list adpar;
  TDAG DAG;
  unsigned arity = 0;
  TDAG *DAGs = NULL;
  va_start(adpar, symb);
  while ((DAG = va_arg(adpar, TDAG)) != DAG_NULL)
    {
      MY_REALLOC(DAGs, (arity + 1) * sizeof(TDAG));
      DAGs[arity++] = DAG;
    }
  va_end(adpar);
  return DAG_new(symb, arity, DAGs);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_list(Tsymb symb, Tlist list)
{
  TDAG *PDAG = NULL;
  unsigned length, i;
  length = list_length(list);
  if (length)
    {
      MY_MALLOC (PDAG, length * sizeof (TDAG));
    }
  for (i = 0; i < length; i++, list = list_cdr(list))
    PDAG[i] = DAG_of_ptr(list_car(list));
  return DAG_new(symb, length, PDAG);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_stack(Tsymb symb, Tstack_DAG stack_arg)
{
  TDAG *PDAG = NULL;
  if (stack_arg->size)
    {
      MY_MALLOC(PDAG, stack_arg->size * sizeof (TDAG));
      memcpy(PDAG, stack_arg->data, stack_arg->size * sizeof (TDAG));
    }
  return DAG_new(symb, stack_arg->size, PDAG);
}

/*--------------------------------------------------------------*/

#ifdef MEM
static unsigned count = 0;
#endif

TDAG
DAG_dup(TDAG DAG)
{
#ifdef DEBUG_DAG
  my_DAG_message("DAG_dup(%u) %D\n", DAG_table->data[DAG].gc_count, DAG);
#endif
#ifdef MEM
  if (DAG_SPY(DAG))
    {
      my_DAG_message("Count+ %d: %d, %d\n", DAG, ++count, DAG_table->data[DAG].gc_count + 1);
      breakpoint();
    }
#endif
  return DAG_gc_inc(DAG);
}

/*--------------------------------------------------------------*/

void
DAG_free(TDAG DAG)
{
#ifdef DEBUG_DAG
  my_DAG_message("DAG_free (%u) %p:%D\n", DAG_table->data[DAG].gc_count, DAG, DAG);
#endif
#ifdef MEM
  if (DAG_SPY(DAG))
    {
      my_DAG_message("Count- %d: %d, %d\n", DAG, --count, DAG_table->data[DAG].gc_count - 1);
      breakpoint();
    }
#endif
  DAG_gc_dec(DAG);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_integer(long value)
{
  return DAG_new_args(DAG_symb_integer(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_rational(long num, long den)
{
  return DAG_new_args(DAG_symb_rational(num, den), DAG_NULL);
}

      
/*--------------------------------------------------------------*/

TDAG
DAG_new_numeral_str(char * value)
{
  return DAG_new_args(DAG_symb_numeral_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_decimal_str(char * value)
{
  return DAG_new_args(DAG_symb_decimal_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_binary_str(char * value)
{
  return DAG_new_args(DAG_symb_binary_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_hex_str (char * value)
{
  return DAG_new_args(DAG_symb_hex_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

/* PF kept for backward compatibility with SMT-LIB 1.2 */
TDAG
DAG_new_float_str(char * value)
{
  return DAG_new_decimal_str(value);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_rational_str(char * value)
{
  return DAG_new_args(DAG_symb_rational_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_str(char * value)
{
  return DAG_new_args(DAG_symb_str(value), DAG_NULL);
}

/*--------------------------------------------------------------*/

int
DAG_is_rational(TDAG DAG)
{
  return DAG_symb_type(DAG_symb(DAG)) == SYMB_RATIONAL;
}

/*--------------------------------------------------------------*/

int
DAG_is_integer(TDAG DAG)
{
  return DAG_symb_type(DAG_symb(DAG)) == SYMB_INTEGER;
}

/*--------------------------------------------------------------*/

int
DAG_is_number(TDAG DAG)
{
  return DAG_is_integer(DAG) || DAG_is_rational(DAG);
}

/*--------------------------------------------------------------*/

int
DAG_is_atom(TDAG DAG)
{
  return !boolean_connector(DAG_symb(DAG));
}

/*
  --------------------------------------------------------------
  Initialisation and release
  --------------------------------------------------------------
*/

static int DAG_initialised = 0;

void
DAG_init(void)
{
  if (DAG_initialised++)
    my_error ("DAG_init: DAG has been initialised several times\n");

  stack_INIT(DAG_table);
  DAG_freed = DAG_NULL;
  stack_inc0(DAG_table);

  options_new(0, "disable-sym-eq",
	      "Disable symmetry of equality (EXPERIMENTAL - don't use that)",
              &disable_sym_eq);

  stack_INIT(stack_hook_resize);
  stack_INIT(stack_hook_free);

  DAG_sort_init();
  DAG_symb_init();
  DAG_prop_init();
  DAG_flag_init();
  DAG_tmp_init();
  DAG_symb_DAG_init();

  stack_INIT(sort_stack);

  BOOLEAN_TRUE =
    DAG_symb_new(BOOLEAN_TRUE_STR, SYMB_BOOLEAN_CONSTANT, SORT_BOOLEAN);
  BOOLEAN_FALSE =
    DAG_symb_new(BOOLEAN_FALSE_STR, SYMB_BOOLEAN_CONSTANT, SORT_BOOLEAN);

  DAG_symb_set_predefined(BOOLEAN_TRUE);
  DAG_symb_set_predefined(BOOLEAN_FALSE);
  DAG_symb_set_interpreted(BOOLEAN_TRUE);
  DAG_symb_set_interpreted(BOOLEAN_FALSE);

  DAG_TRUE = DAG_dup(DAG_new_args(BOOLEAN_TRUE, DAG_NULL));
  DAG_FALSE = DAG_dup(DAG_new_args(BOOLEAN_FALSE, DAG_NULL));
}

/*--------------------------------------------------------------*/

#ifdef MEM
static int
DAG_dec_size(TDAG * PDAG1, TDAG * PDAG2)
{
  if (DAG_table->data[*PDAG2].misc == DAG_table->data[*PDAG1].misc)
    return DAG_count_nodes(*PDAG2) - DAG_count_nodes(*PDAG1);
  if (DAG_table->data[*PDAG1].misc)
    return 1;
  return -1;
}

static void
mark_indirect_aux(TDAG DAG)
{
  unsigned i;
  DAG_table->data[DAG].misc = 1;
  for (i = 0; i < DAG_arity(DAG); i++)
    mark_indirect_aux(DAG_arg(DAG, i));
}

static void
mark_indirect(TDAG DAG)
{
  unsigned i;
  for (i = 0; i < DAG_arity(DAG); i++)
    mark_indirect_aux(DAG_arg(DAG, i));
}

#endif

void
DAG_done (void)
{
  if (!DAG_initialised--)
    my_error ("DAG_done: DAG has not been initialised several times");
  DAG_free(DAG_TRUE);
  DAG_free(DAG_FALSE);
  DAG_symb_DAG_done();
#ifdef MEM
  {
    unsigned i;
    TDAG DAG;
    Tstack_DAG unfreed;
    stack_INIT(unfreed);
    for (DAG = 0; DAG < DAG_table->size; DAG++)
      if (DAG_table->data[DAG].gc_count)
	stack_push(unfreed, DAG);
    if (unfreed->size)
      {
	for (i = 0; i < unfreed->size; i++)
	  mark_indirect(unfreed->data[i]);
	stack_sort(unfreed, DAG_dec_size);
	my_DAG_message("Largest unfreed DAG %d: %D\n",
		       unfreed->data[0], unfreed->data[0]);
	for (i = 0; i < unfreed->size; i++)
	  {
	    DAG = unfreed->data[i];
	    my_DAG_message("Unfreed DAG %d: %d, %D %s\n", i, DAG, DAG,
			   DAG_table->data[DAG].misc?"(indirect)":"");
	    DAG_table->data[DAG].misc = 0;
	  }
      }
    stack_free(unfreed);
  }
#endif
  stack_free(sort_stack);
  DAG_tmp_done();
  DAG_flag_done();
  DAG_sort_done();
  DAG_symb_done();
  DAG_prop_done();
  DAG_hook_resize(DAG_table->alloc, 0);
  stack_free(DAG_table);
  stack_free(stack_hook_resize);
  stack_free(stack_hook_free);
  attr_max = 0;
}

/*--------------------------------------------------------------*/

void
DAG_set_hook_resize(TDAG_hook_resize hook_resize)
{
  hook_resize(0, DAG_table->alloc);
  stack_push(stack_hook_resize, hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_set_hook_free(TDAG_hook_free hook_free)
{
  stack_push(stack_hook_free, hook_free);
}
