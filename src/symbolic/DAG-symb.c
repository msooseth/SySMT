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
  Symbol stuff
  --------------------------------------------------------------
*/
#include <string.h>

#include "general.h"
#include "stack.h"

#include "DAG-sort-pm.h"
#include "DAG-symb.h"

Tstack_Ssymb DAG_symb_stack;

TSstack(_hook_resize, TDAG_hook_resize);
static Tstack_hook_resize stack_hook_resize;

/* #define SYMB_DAG(symb) (DAG_symb_get_bind_DAG(symb)) */
#define SYMB_SORT(symb) (DAG_symb_sort(symb))
#define SYMB_NAME(symb) (DAG_symb_name(symb))

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
DAG_symb_table_print(void)
{
  unsigned i;
  fprintf(stderr, "%5s %15s %5s\n", "index", "name", "sort");
  for (i = 0; i < stack_size(DAG_symb_stack); ++i)
    fprintf(stderr, "%5i %15s %5i\n", i, SYMB_NAME(i), SYMB_SORT(i));
}
#endif

/*
  --------------------------------------------------------------
  Overloading
  --------------------------------------------------------------
*/

/** \brief Structure to store a set of homonym symbols */
typedef struct Tsymb_homonym
{
  char *name;        /*< the name of the symbols */
  unsigned nb;       /*< the number of homonyms */
  Tstack_symb symbs; /*< homonym symbols */
} Tsymb_homonym;

/** \brief Hash table to store sets of homonyms */
static Thash symb_name_hash;

/*--------------------------------------------------------------*/

/* PF table_lookup usage */
static int
DAG_symb_homonym_cmp(Tsymb_homonym *Psymb_homonym1,
		     Tsymb_homonym *Psymb_homonym2)
{
  return !strcmp(Psymb_homonym1->name, Psymb_homonym2->name);
}

/*--------------------------------------------------------------*/

static unsigned
DAG_symb_homonym_hash_function(Tsymb_homonym *Psymb_homonym)
{
  return hash_one_at_a_time(Psymb_homonym->name);
}

/*--------------------------------------------------------------*/

static void
DAG_symb_homonym_free(Tsymb_homonym *Psymb_homonym)
{
  stack_free(Psymb_homonym->symbs);
  free(Psymb_homonym);
}

/*--------------------------------------------------------------*/

/* PF retrieve homonym structure for name */
static Tsymb_homonym *
homonym_table_lookup(char *name)
{
  Tsymb_homonym tmp;
  tmp.name = name;
  return hash_lookup(symb_name_hash, &tmp);
}

/*--------------------------------------------------------------*/

/* PF insert symb in symb_by_name, symb_table */
static void
homonym_table_insert(Tsymb symb)
{
  Tsymb_homonym *Psymb_homonym;
  Psymb_homonym = homonym_table_lookup(DAG_symb_name(symb));
  if (!Psymb_homonym)
    {
      Tstack_symb symbols;
      stack_INIT(symbols);
      MY_MALLOC(Psymb_homonym, sizeof(Tsymb_homonym));
      Psymb_homonym->name = DAG_symb_name(symb);
      Psymb_homonym->nb = 1;
      stack_push(symbols, symb);
      Psymb_homonym->symbs = symbols;
      hash_insert(symb_name_hash, (void *) Psymb_homonym);
      return;
    }
  Psymb_homonym->nb++;
  stack_push(Psymb_homonym->symbs, symb);
}

/*--------------------------------------------------------------*/

static void
DAG_symb_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  unsigned i;
  for (i = 0; i < stack_hook_resize->size; i++)
    stack_hook_resize->data[i](old_alloc, new_alloc);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_new(const char *name, Tsymb_type type, Tsort sort)
{
  Tsymb symb = DAG_SYMB_NULL;
  Tsymb_homonym *Psymb_homonym;
  Psymb_homonym = homonym_table_lookup((char *) name);
  if (Psymb_homonym)
    {
      unsigned i;
      /* PF Check if other symbols are compatible so that sort of
         every DAG may be deduced by symbol and subDAGs */
      for (i = 0; i < Psymb_homonym->symbs->size; i++)
	if (SYMB_SORT(Psymb_homonym->symbs->data[i]) == sort)
	  return Psymb_homonym->symbs->data[i];
      /*
	PF Since smt-lib2, this is deprecated.
        The same symbol may be overloaded.
        The parser makes sure no ambiguity can occur.
	else if (DAG_sort_conflict(SYMB_SORT((Tsymb) list_car (tmp_list)),
	sort))
	my_error ("Sort for symbol \"%s\" is non resolvable\n", name);
      */
    }
  symb = stack_size(DAG_symb_stack);
  stack_inc_hook(DAG_symb_stack, DAG_symb_hook_resize);
  DAG_symb_stack->data[symb].name = strmake(name);
  DAG_symb_stack->data[symb].type = type;
  DAG_symb_stack->data[symb].sort = sort;
  DAG_symb_stack->data[symb].misc = 0;
  DAG_symb_stack->data[symb].Pflag = NULL;
  DAG_symb_stack->data[symb].key = hash_one_at_a_time_inc(0, SYMB_NAME(symb));
  DAG_symb_stack->data[symb].key =
    hash_one_at_a_time_u_inc(DAG_symb_stack->data[symb].key,
			     Psymb_homonym ? Psymb_homonym->nb : 0);
  DAG_symb_stack->data[symb].key =
    hash_one_at_a_time_inc_end(DAG_symb_stack->data[symb].key);
  DAG_symb_stack->data[symb].dp_mask = 0;
  DAG_symb_stack->data[symb].interpreted = false;
  DAG_symb_stack->data[symb].predefined = false;
  /* TODO later tune the size, for unary symbols,
     for connectors, predefined preds and funcs... */
  DAG_symb_stack->data[symb].hash = 
    hash_new(32, (TFhash) DAG_hash, (TFequal) DAG_identity, NULL);
  homonym_table_insert(symb);
  return symb;
}

/*--------------------------------------------------------------*/

static void
DAG_symb_free(Tsymb symb)
/* PF Free memory of symbol Pvoid */
{
  if (symb == DAG_SYMB_NULL)
    return;
  assert(symb < stack_size(DAG_symb_stack));
#ifdef DAG_STATS
  my_message("Hash statistics for symbol %s\n", symb->name);
  hash_print_stats(DAG_symb_stack->data[symb].hash);
#endif
  hash_free(&DAG_symb_stack->data[symb].hash);
  free(DAG_symb_stack->data[symb].name);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_integer(long value)
{
  char name[255];
  Tsymb symb;
  sprintf(name, "%ld", value);
  symb = DAG_symb_new(name, SYMB_INTEGER, SORT_INTEGER);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_rational(long num, long den)
/* PF the user is responsible for not generating overflows */
/* DC fraction representation of rationals */
{
  char name[255];
  Tsymb symb;
  if (den < 0)
    {
      num *= -1;
      den *= -1;
    }
  assert(l_str_size(num)+l_str_size(den)+2 <= 255);
  sprintf(name, "%ld/%ld", num, den);
  symb = DAG_symb_new(name, SYMB_RATIONAL, SORT_REAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith; /* PF TODO: tidy */
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value textual representation of an integer [\-]?(0|[1-9][0-9]*)
   \return Creates (if new) and returns Tsymb representing integer value.

   The given string is checked for conformance.
*/

Tsymb
DAG_symb_numeral_str(char * value)
{
  size_t i, n, start;
  Tsymb symb;
  n = strlen(value);
  start = (value[0] == '-') ? 1 : 0;
  if (n <= start || (n > 1 && value[start] == '0'))
    my_error("DAG_symb_numeral_str: ill-formed integer\n");
  for (i = start; i < n; i++)
    if (value[i] < '0' || value[i] > '9')
      my_error("DAG_symb_numeral_str: ill-formed integer\n");
  symb = DAG_symb_new(value, SYMB_INTEGER, SORT_NUMERAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value textual representation of a decimal [\-]?(0|[1-9][0-9]*)\.[0-9]+
   \return Creates (if new) and returns Tsymb representing decimal value.

   The given string is checked for conformance.
*/

Tsymb
DAG_symb_decimal_str(char * value)
{
  size_t i, d, n, start;
  Tsymb symb;
  n = strlen(value);
  d = 0;
  for (i = 0; i < n; i++)
    if (value[i] == '.')
      {
        d = i;
        break;
      }
  start = (value[i] == '-') ? 1 : 0;
  if (d == start || d == n - 1 || (d > 1 && value[start] == '0'))
    my_error("DAG_symb_decimal_str: ill-formed decimal\n");
  for (i = start; i < d; i++)
    if (value[i] < '0' || value[i] > '9')
      my_error("DAG_symb_decimal_str: ill-formed decimal\n");
  for (i = d + 1; i < n; i++)
    if (value[i] < '0' || value[i] > '9')
      my_error("DAG_symb_decimal_str: ill-formed decimal\n");
  symb = DAG_symb_new(value, SYMB_RATIONAL, SORT_DECIMAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value textual representation of a binary #b[01]+
   \return Creates (if new) and returns Tsymb representing binary value.

   The given string is checked for conformance.
*/
Tsymb
DAG_symb_binary_str(char * value)
{
  size_t i, n;
  Tsymb symb;
  n = strlen(value);
  if (n < 3 || value[0]!='#' || value[1]!='b')
    my_error("DAG_symb_binary_str: ill-formed binary\n");
  for (i = 2; i < n; i++)
    if (value[i] != '0' && value[i] != '1')
      {
        my_error("DAG_symb_binary_str: ill-formed binary\n");
        return DAG_SYMB_NULL;
      }
  symb = DAG_symb_new(value, SYMB_BINARY, SORT_INTEGER);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value textual representation of an hexadecimal #x[0-9A-Fa-f]+
   \return Creates (if new) and returns Tsymb representing hexadecimal value.

   The given string is checked for conformance.
*/
Tsymb
DAG_symb_hex_str(char * value)
{
  size_t i, n;
  Tsymb symb;
  n = strlen(value);
  if (n < 3 || value[0]!='#' || value[1]!='h')
    my_error("DAG_symb_hex_str: ill-formed hexadecimal\n");
  for (i = 2; i < n; i++)
    if (!((value[i] >= 'A' && value[i] <= 'F') ||
	  (value[i] >= 'a' && value[i] <= 'f') ||
	  (value[i] >= '0' && value[i] <= '9')))
      {
        my_error("DAG_symb_hex_str: ill-formed hexadecimal\n");
        return DAG_SYMB_NULL;
      }
    else if (value[i] >= 'a' && value[i] <= 'f')
      value[i] = value[i] + 'A' - 'a';
  symb = DAG_symb_new(value, SYMB_HEX, SORT_NUMERAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value textual representation of a rational [\-]?[1-9][0-9]* / [0-9]+[1-9] or [\-]?[1-9][0-9]*
   \return Creates (if new) and returns Tsymb representing rational value.
   \remark given string checked for conformance */
Tsymb
DAG_symb_rational_str(char * value)
{
  size_t i, d, n, start;
  Tsymb symb;
  n = strlen(value);
  d = 0;
  for (i = 0; i < n; i++)
    if (value[i] == '/')
      {
        d = i;
        break;
      }
  start = (value[0] == '-') ? 1 : 0;
  if (d == start || d == n - 1 || (d > 1 && value[start] == '0'))
    my_error("DAG_symb_rational_str: ill-formed rational %s\n", value);
  for (i = start; i < d; i++)
    if (value[i] < '0' || value[i] > '9')
      my_error("DAG_symb_rational_str: ill-formed rational %s\n", value);
  for (i = d + 1; i < n; i++)
    if (value[i] < '0' || value[i] > '9')
      my_error("DAG_symb_rational_str: ill-formed rational %s\n", value);
  symb = DAG_symb_new(value, SYMB_RATIONAL, SORT_REAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

/**
   \brief Tsymb constructor
   \param value string
   \return Creates (if new) and returns Tsymb representing string */
Tsymb
DAG_symb_str(char * value)
{
  Tsymb symb;
  symb = DAG_symb_new(value, SYMB_STRING, SORT_REAL);
  DAG_symb_set_predefined(symb);
  DAG_symb_set_interpreted(symb);
  DAG_symb_stack->data[symb].dp_mask = dp_mask_arith;
  return symb;
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_lookup_sort(char *name, Tsort sort)
{
  unsigned i;
  Tsymb found_symb = DAG_SYMB_NULL;
  Tsymb_homonym *homonym = homonym_table_lookup(name);
  if (!homonym)
    return DAG_SYMB_NULL;
  if (sort == DAG_SORT_NULL)
    return DAG_SYMB_NULL;
  for (i = 0; i < homonym->symbs->size; i++)
    {
      if (!DAG_sort_subsumes(DAG_symb_sort(homonym->symbs->data[i]), sort))
	continue;
      /*PF2DD I am a bit puzzled:
	why the order in homonym->symbs should define the behavior here */
      if (found_symb &&
	  !DAG_sort_subsumes(DAG_symb_sort(homonym->symbs->data[i]), 
			     DAG_symb_sort(found_symb)))
	return DAG_SYMB_NULL;
      found_symb = homonym->symbs->data[i];
    }
  return found_symb;
}


/*--------------------------------------------------------------*/

Tsymb
DAG_symb_skolem(Tsort sort)
{
  static unsigned nb = 1;
  char str[16];
  if (nb>99999)
    my_error("too many skolem symbols\n");
  sprintf(str, "veriT__sk_%d",nb++);
  return DAG_symb_new(str, SYMB_SKOLEM, sort);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_const(Tsort sort)
{
  static unsigned nb = 1;
  Tsymb_type type;
  char str[16];
  if (nb>99999)
    my_error("too many constant symbols\n");
  sprintf(str, "veriT__ct_%d",nb++);
  type = (sort == SORT_BOOLEAN) ? SYMB_PREDICATE : SYMB_FUNCTION;
  return DAG_symb_new(str, type, sort);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_variable(Tsort sort)
{
  static unsigned nb = 1;
  char str[16];
  if (nb>9999999)
    my_error("too many variables\n");
  sprintf(str, "?veriT__%d",nb++);
  return DAG_symb_new(str, SYMB_VARIABLE, sort);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_function(Tsort sort)
{
  static unsigned nb = 1;
  char str[16];
  if (nb>99999)
    my_error("too many functions\n");
  sprintf(str, "veriT__fn_%d",nb++);
  return DAG_symb_new(str, SYMB_FUNCTION, sort);
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_predicate(Tsort sort)
{
  static unsigned nb = 1;
  char str[13];
  if (nb>99999)
    my_error("too many predicates\n");
  sprintf(str, "pred_%d",nb++);
  return DAG_symb_new(str, SYMB_PREDICATE, sort);
}

/*--------------------------------------------------------------*/

void
DAG_symb_set_hook_resize(TDAG_symb_hook_resize hook_resize)
{
  hook_resize(0, DAG_table->alloc);
  stack_push(stack_hook_resize, hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_symb_init(void)
{
  stack_INIT(DAG_symb_stack);
  /* Reserve id 0 */
  stack_inc(DAG_symb_stack);
  symb_name_hash = hash_new(1 << 8,
			    (TFhash) DAG_symb_homonym_hash_function,
			    (TFequal) DAG_symb_homonym_cmp,
			    (TFfree) DAG_symb_homonym_free);
  stack_INIT(stack_hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_symb_done(void)
{
  Tsymb symb;
  /*
  for (symb = 1; symb < stack_size(DAG_symb_stack); ++symb)
    if (SYMB_DAG(symb))
      DAG_free(SYMB_DAG(symb));
  */
  for (symb = 1; symb < stack_size(DAG_symb_stack); ++symb)
    DAG_symb_free(symb);
  DAG_symb_hook_resize(DAG_symb_stack->alloc, 0);
  stack_free(DAG_symb_stack);
  hash_free(&symb_name_hash);
  stack_free(stack_hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_symb_set_Pflag(Tsymb symb, void * P)
{
  DAG_symb_stack->data[symb].Pflag = P;
}

/*--------------------------------------------------------------*/

/**
   \brief returns sort of application of symb to arguments of sort
   Psort[0] ...Psort[n-1]
   \param symb the symbol
   \param n the number of arguments
   \param Psort the argument sorts
   \return DAG_SORT_NULL if it cannot be applied 
*/
Tsort
DAG_symb_check(Tsymb symb, unsigned n, Tsort * Psort)
{
  unsigned i;
  Tsort sort;
  /* PF special cases (mainly overloaded symbols) */
  if (n == 0)
    return SYMB_SORT(symb);
  if (symb == PREDICATE_EQ)
    {
      if (n == 2 && DAG_sort_unif_pair(Psort[0], Psort[1])
	  /* && Psort[0] != SORT_BOOLEAN*/ )
        return SORT_BOOLEAN;
      return DAG_SORT_NULL;
    }
  if (symb == PREDICATE_DISTINCT)
    {
      unsigned j;
      for (i = 0; i < n; i++)
        for (j = i + 1; j < n; j++)
          if (!DAG_sort_unif_pair(Psort[0], Psort[1]))
            return DAG_SORT_NULL;
      /* PF TODO Accept boolean sort in distinct */
      return SORT_BOOLEAN;
    }
  if (symb == FUNCTION_ITE)
    {
      if (n == 3 && Psort[0] == SORT_BOOLEAN &&
          Psort[1] != SORT_BOOLEAN && Psort[2] != SORT_BOOLEAN)
        return DAG_sort_unif_pair(Psort[1], Psort[2]);
      return DAG_SORT_NULL;
    }
  if (symb == CONNECTOR_ITE)
    {
      if (n == 3 && Psort[0] == SORT_BOOLEAN &&
          Psort[1] == SORT_BOOLEAN && Psort[2] == SORT_BOOLEAN)
        return SORT_BOOLEAN;
      return DAG_SORT_NULL;
    }
  if (quantifier(symb))
    {
      if (n > 1 && Psort[n - 1] == SORT_BOOLEAN)
        return SORT_BOOLEAN;
      return DAG_SORT_NULL;
    }
  if (symb == LET)
    {
      if (n < 3)
        return DAG_SORT_NULL;
      for (i = 0; i < n - 1; i++, i++)
        if (Psort[i] != Psort[i + 1])
          return DAG_SORT_NULL;
      return Psort[n - 1];
    }
  if (symb == LAMBDA)
    {
      Tsort *sub;
      MY_MALLOC(sub, n * sizeof(Tsort));
      for (i = 0; i < n; i++)
        sub[i] = Psort[i];
      return DAG_sort_new(NULL, n, sub);
    }
  if (symb == APPLY_LAMBDA)
    {
      if (n < 2)
        return DAG_SORT_NULL;
      sort = Psort[0];
      assert(DAG_sort_arity(sort) != DAG_SORT_NARY);
      if (!sort || DAG_sort_arity(sort) != n)
        my_error("Sort error in lambda application.\n");
      return DAG_sort_unif_apply(Psort + 1, DAG_sort_sub(sort), n - 1, 
				 DAG_sort_sub(sort)[n - 1]);
    }
  if (arith_function(symb))
    {
      Tsort sort;
      if ((symb == FUNCTION_SUM && n < 2) ||
          (symb == FUNCTION_PROD && n < 2) ||
          (unary_minus(symb) && n != 1) ||
          (symb == FUNCTION_MINUS && n != 2) ||
          (symb == FUNCTION_DIV && n != 2))
        return DAG_SORT_NULL;
      sort = Psort[0];
      for (i = 1; i < n; i++)
	sort = DAG_sort_combine(sort, Psort[i]);
      if (sort == SORT_INTEGER || sort == SORT_REAL)
        return sort;
      return DAG_SORT_NULL;
    }
  if (arith_comparison(symb))
    {
      Tsort sort;
      if (n != 2) return DAG_SORT_NULL;
      sort = DAG_sort_combine(Psort[0], Psort[1]);
      if (DAG_sort_combine(sort, SORT_INTEGER))
        return SORT_BOOLEAN;
      return DAG_SORT_NULL;
    }
  /* DD when symb is an instance of a polymorphic symbol */
  /* if (symb->origin != NULL) */
  /*   { */
  /*     i = 0; */
  /*     while (i < n && SYMB_SORT(symb)->sub[i] == Psort[i]) ++i; */
  /*     if (i == n) */
  /* 	return SYMB_SORT(symb)->sub[n]; */
  /*     else */
  /* 	return NULL; */
  /*   } */
  /* PF general treatment */
  sort = SYMB_SORT(symb);
  if (!n)
    return sort;
  if (DAG_sort_arity(sort) == DAG_SORT_NARY)
    return DAG_sort_unif_apply_polyadic(Psort, DAG_sort_sub(sort)[0], 
					n, DAG_sort_sub(sort)[1]);
  if (DAG_sort_arity(sort) != n + 1u) /* nary handled just above */
    return DAG_SORT_NULL;
  return DAG_sort_unif_apply(Psort, DAG_sort_sub(sort), n,
			     DAG_sort_sub(sort)[n]);    
}

/*--------------------------------------------------------------*/

Tsymb
DAG_symb_lookup(char *name, unsigned arity, Tsort * Psort, Tsort sort)
{
  unsigned i;
  Tsymb found_symb = DAG_SYMB_NULL;
  Tsymb_homonym *homonym = homonym_table_lookup(name);
  if (!homonym)
    return DAG_SYMB_NULL;
  for (i = 0; i < homonym->symbs->size; i++)
    {
      if (sort && !DAG_sort_combine(sort, SYMB_SORT(homonym->symbs->data[i])))
	continue;
      if (Psort && !DAG_symb_check(homonym->symbs->data[i], arity, Psort))
	continue;
      if (found_symb)
	return DAG_SYMB_NULL;
      found_symb = homonym->symbs->data[i];
    }
  return found_symb;
}
