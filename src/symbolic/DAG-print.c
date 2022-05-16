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
  Module for printing formulas and terms
  --------------------------------------------------------------
*/

#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>

#include "general.h"
#include "DAG.h"
#include "DAG-ptr.h"
#include "DAG-print.h"
#include "DAG-tmp.h"
#include "stack.h"
#include "table.h"
#include "qnt-tidy.h"
#include "recursion.h"

#define symb_misc(s) DAG_symb_misc(s)
#define symb_set_misc(s,v) DAG_symb_set_misc(s,v)
#define symb_sort(s) DAG_symb_sort(s)
#define symb_type(s) DAG_symb_type(s)
#define symb_interpreted(s) DAG_symb_interpreted(s)
#define symb_predefined(s) DAG_symb_predefined(s)

#define sort_name(s) DAG_sort_name(s)
#define sort_arity(s) DAG_sort_arity(s)
#define sort_predefined(s) DAG_sort_predefined(s)
#define sort_sub(s,i) DAG_sort_sub(s)[i]

TDAG_fprint_opt DAG_fprint_opt = {
  /* logic */ "UNKNOWN",
  /* newlines */ 1,
  /* columns */ 120,
  /* column_to_indent */40,
  /* flat */ false,
  /* version */ 2
};

static void DAG_sort_fprint(FILE * file, Tsort sort);
static char * DAG_symb_smt_name(Tsymb symb);

/*
 --------------------------------------------------------------
 helpers
 --------------------------------------------------------------
 */

static Tstack_symb collect_symbols; /**< global list of symbols */

static char * symbol_prefix = NULL;
static char * symbol_prefix_var = NULL;
static char symbol_tmp[256];

/*--------------------------------------------------------------*/

/**
 \param str a symbol name
 
 \note computes a value for symbol_prefix (or symbol_prefix_var if
 str[0] == '?') so that it is not the prefix of str.
 */
static void
check_symbol_prefix(char * str)
{
  if (!strncmp(str, "veriT", 5))
    {
      if (!symbol_prefix)
	symbol_prefix = strmake("veriT.");
      while (!strncmp(str, symbol_prefix, strlen(symbol_prefix)))
	{
	  MY_REALLOC(symbol_prefix,
		     (strlen(symbol_prefix) + 2) * sizeof(char));
	  strcat(symbol_prefix, ".");
	}
    }
  if (!strncmp(str, "?veriT", 6))
    {
      if (!symbol_prefix_var)
	symbol_prefix_var = strmake("?veriT.");
      while (!strncmp(str, symbol_prefix_var, strlen(symbol_prefix_var)))
	{
	  MY_REALLOC(symbol_prefix_var,
		     (strlen(symbol_prefix_var) + 2) * sizeof(char));
	  strcat(symbol_prefix_var, ".");
	}
    }
}

/*--------------------------------------------------------------*/

/**
 \param str the name of a symbol
 
 \note returns the concatenation of symbol_prefix (or symbol_prefix_var
 if str[0] == '?') with str
 
 \note global variable symbol_tmp stores the result, it is limited
 to 255 characters, causing a runtime error (assertion violation)
 when exceeding this limit
 */
static char * rectify_symbol_prefix(char * str)
{
  if (!symbol_prefix)
    return str;
  if (!strncmp(str, "veriT", 5))
  {
    assert(symbol_prefix);
    if (strlen(str) >= 255 - strlen(symbol_prefix))
      my_error("Too long symbol\n");
    strcpy(symbol_tmp, symbol_prefix);
    strcat(symbol_tmp, str);
    return symbol_tmp;
  }
  if (!strncmp(str, "?veriT", 6))
  {
    assert(symbol_prefix_var);
    if (strlen(str) >= 255 - strlen(symbol_prefix_var))
      my_error("Too long symbol\n");
    strcpy(symbol_tmp, symbol_prefix_var);
    strcat(symbol_tmp, str + 1);
    return symbol_tmp;
  }
  return str;
}

/*--------------------------------------------------------------*/

static char * DAG_symb_name_rectify(Tsymb symb)
{
  return rectify_symbol_prefix(DAG_symb_name(symb));
}

/*--------------------------------------------------------------*/

static void
collect_symbols_DAG_node(TDAG src)
{
  Tsymb symb = DAG_symb(src);
  check_symbol_prefix(DAG_symb_name(symb));
  if (symb_type(symb) == SYMB_VARIABLE || 
      symb_misc(symb) || 
      DAG_symb_predefined(symb))
    return;
  stack_push(collect_symbols, symb);
  if (DAG_sort_polymorphic(DAG_symb_sort(symb)))
  {
    int i;
    Tsort * Psort;
    MY_MALLOC(Psort, sizeof(Tsort) * (DAG_arity(src)+1));
    for (i = 0; i < DAG_arity(src); ++i)
      Psort[i] = DAG_sort(DAG_arg(src, i));
    Psort[i] = DAG_sort(src);
    DAG_sort_new(NULL, DAG_arity(src)+1, Psort);
  }
  symb_set_misc(symb, 1);
}

/*--------------------------------------------------------------*/

static void
collect_symbols_DAG(TDAG src)
{
  unsigned i;
  structural_recursion_void(src, collect_symbols_DAG_node);
  for (i = 0; i < collect_symbols->size; i++)
    symb_set_misc(collect_symbols->data[i], 0);
}

/*
 --------------------------------------------------------------
 Printing DAGs : Sorted
 --------------------------------------------------------------
 */

void
DAG_fprint(FILE * file, TDAG DAG)
{
  int i;
  if (SILENT)
    return;
  if (!DAG)
  {
    fprintf(file, "NULL");
    return;
  }
  if (DAG_arity(DAG) == 0)
  {
    fprintf(file, "%s", DAG_symb_name(DAG_symb(DAG)));
    return;
  }
  fprintf(file, "(%s", DAG_symb_name(DAG_symb(DAG)));
  if (quantifier(DAG_symb(DAG)) || DAG_symb(DAG) == LAMBDA)
  {
    fprintf(file, " ");
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
    {
      fprintf(file, " (%s ",
               DAG_symb_name(DAG_symb(DAG_arg(DAG, i))));
      DAG_sort_fprint(file, DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
      fprintf(file, ")");
    }
    fprintf(file, " ");
    DAG_fprint(file, DAG_argn(DAG));
  }
  else if (DAG_symb(DAG) == LET)
  {
    fprintf(file, " (");
    for (i = 0; i < DAG_arity(DAG) - 1; i+=2)
    {
      fprintf(file, "(%s ",
               DAG_symb_name(DAG_symb(DAG_arg(DAG, i))));
      DAG_fprint(file, DAG_arg(DAG, i+1));
      fprintf(file, ")");
    }
    fprintf(file, ") ");
    DAG_fprint(file, DAG_argn(DAG));
  }
  else
  {
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, " ");
      DAG_fprint(file, DAG_arg(DAG, i));
    }
  }
  fprintf(file, ")");
}

/*
 --------------------------------------------------------------
 Printing DAGs : Sorted
 --------------------------------------------------------------
 */

static void
DAG_fprint_sort(FILE * file, TDAG DAG)
{
  int i;
  if (SILENT)
    return;
  if (!DAG)
  {
    fprintf(file, "NULL");
    return;
  }
  if (DAG_arity(DAG) == 0)
  {
    fprintf(file, "[%s : ", DAG_symb_name(DAG_symb(DAG)));
    DAG_sort_fprint(file, symb_sort(DAG_symb(DAG)));
    fprintf(file, "]");
    return;
  }
  fprintf(file, "[([%s", DAG_symb_name(DAG_symb(DAG)));
  fprintf(file, " : ");
  DAG_sort_fprint(file, symb_sort(DAG_symb(DAG)));
  fprintf(file,"]");
  if (quantifier(DAG_symb(DAG)) || DAG_symb(DAG) == LAMBDA)
  {
    fprintf(file, " ");
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
    {
      fprintf(file, " (%s ",
               DAG_symb_name(DAG_symb(DAG_arg(DAG, i))));
      DAG_sort_fprint(file, DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
      fprintf(file, ")");
    }
    fprintf(file, " ");
    DAG_fprint_sort(file, DAG_argn(DAG));
  }
  else if (DAG_symb(DAG) == LET)
  {
    fprintf(file, " (");
    for (i = 0; i < DAG_arity(DAG) - 1; i+=2)
    {
      fprintf(file, "(%s ",
               DAG_symb_name(DAG_symb(DAG_arg(DAG, i))));
      DAG_fprint_sort(file, DAG_arg(DAG, i+1));
      fprintf(file, ")");
    }
    fprintf(file, ") ");
    DAG_fprint_sort(file, DAG_argn(DAG));
  }
  else
  {
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, " ");
      DAG_fprint_sort(file, DAG_arg(DAG, i));
    }
  }
  fprintf(file, ") : ");
  DAG_sort_fprint(file, DAG_sort(DAG));
  fprintf(file, "]");
}

/*--------------------------------------------------------------*/

void
DAG_print(TDAG DAG)
{
  DAG_fprint(stdout, DAG);
}

/*--------------------------------------------------------------*/

void
DAG_print_sort(TDAG DAG)
{
  DAG_fprint_sort(stdout, DAG);
}

/*--------------------------------------------------------------*/

static int sharing_count = 0;

void
DAG_fprint_sharing(FILE * file, TDAG DAG)
{
  int i;
  if (SILENT)
    return;
  if (!DAG)
    {
      fprintf(file, "NULL");
      return;
    }
  if (DAG_arity(DAG) == 0)
    {
      fprintf(file, "%s", DAG_symb_name_rectify(DAG_symb(DAG)));
      return;
    }
  if (DAG_misc(DAG))
    {
      fprintf(file, "#%i", (int) DAG_misc(DAG));
      return;
    }
  if (DAG_symb(DAG) != CONNECTOR_NOT)
    {
      assert(sharing_count < INT_MAX);
      DAG_misc_set(DAG, ++sharing_count);
      fprintf(file, "#%i:", (int) DAG_misc(DAG));
    }
  if (DAG_symb(DAG) == APPLY_LAMBDA)
    {
      fprintf(file, "(");
      DAG_fprint_sharing(file, DAG_arg0(DAG));
      for (i = 1; i < DAG_arity(DAG); i++)
	{
	  fprintf(file, " ");
	  DAG_fprint_sharing(file, DAG_arg(DAG, i));
	}
      fprintf(file, ")");
      return;
    }
  if (quantifier(DAG_symb(DAG)) || DAG_symb(DAG) == LAMBDA)
    {
      fprintf(file, "(%s (", DAG_symb_name_rectify(DAG_symb(DAG)));
      for (i = 0; i < DAG_arity(DAG) - 1; i++)
	{
	  fprintf(file, " (%s ",
		  DAG_symb_smt_name(DAG_symb(DAG_arg(DAG, i))));
	  DAG_sort_fprint(file, DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
	  fprintf(file, ")");
	}
      fprintf(file, " ) ");
      DAG_fprint_sharing(file, DAG_argn(DAG));
      fprintf(file, ")");
      return;
    }
  if (DAG_symb(DAG) == LET)
    {
      fprintf(file, "(let (");
      for (i = 0; i < DAG_arity(DAG) - 1; i++)
	{
	  fprintf(file, " (%s ",
		  DAG_symb_smt_name(DAG_symb(DAG_arg(DAG, i))));
	  i++;
	  DAG_fprint_sharing(file, DAG_arg(DAG, i));
	  fprintf(file, ")");
	}
      fprintf(file, " ) ");
      DAG_fprint_sharing(file, DAG_argn(DAG));
      fprintf(file, ")");
      return;
    }
  fprintf(file, "(%s", DAG_symb_name_rectify(DAG_symb(DAG)));
  for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, " ");
      DAG_fprint_sharing(file, DAG_arg(DAG, i));
    }
  fprintf(file, ")");
}

/*--------------------------------------------------------------*/

void
DAG_fprint_sharing_reset(TDAG DAG)
{
  int i;
  if (DAG_symb(DAG) == CONNECTOR_NOT)
  {
    DAG_fprint_sharing_reset(DAG_arg0(DAG));
    return;
  }
  if (!DAG_misc(DAG))
    return;
  DAG_misc_set(DAG, 0);
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_fprint_sharing_reset(DAG_arg(DAG, i));
}

/*
 --------------------------------------------------------------
 Printing DAGs : Isabelle
 --------------------------------------------------------------
 */

void
DAG_isa_fprint(FILE * file, TDAG DAG)
{
  int i;
  char *str = NULL;
  if (DAG_symb(DAG) == CONNECTOR_AND)
    str = " & ";
  if (DAG_symb(DAG) == CONNECTOR_OR)
    str = " | ";
  if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    str = " --> ";
  if (DAG_symb(DAG) == CONNECTOR_EQUIV || DAG_symb(DAG) == PREDICATE_EQ)
    str = " = ";
  if (DAG_symb(DAG) == CONNECTOR_XOR)
    my_error("DAG_isa_fprint: no XOR\n");
  if (str)
  {
    fprintf(file, "(");
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      if (i != 0)
        fprintf(file, "%s", str);
      DAG_isa_fprint(file, DAG_arg(DAG, i));
    }
    fprintf(file, ")");
    return;
  }
  if (DAG_symb(DAG) == CONNECTOR_NOT)
  {
    fprintf(file, "(~ ");
    DAG_isa_fprint(file, DAG_arg0(DAG));
    fprintf(file, ")");
    return;
  }
  fprintf(file, DAG_arity(DAG) ? "(%s " : "%s",
	   DAG_symb_name_rectify(DAG_symb(DAG)));
  for (i = 0; i < DAG_arity(DAG); i++)
  {
    fprintf(file, i ? " " : "");
    DAG_isa_fprint(file, DAG_arg(DAG, i));
  }
  fprintf(file, DAG_arity(DAG) ? ")" : "");
}

/*
 --------------------------------------------------------------
 Printing DAGs : SMT
 --------------------------------------------------------------
 */

#define DAG_get_num(DAG)			\
  (DAG_misc(DAG) >> 8)
#define DAG_set_num(DAG,n)				\
  if (n > 0xFFFFFF) my_error("too many shared DAGs\n"); \
  DAG_misc(DAG) &= 0x000000FF;				\
  DAG_misc(DAG) |= n << 8;

char * smt_name(char * name)
{
  if (name[0] == '$')
    return name+1;
  else return name;
}

static char * DAG_symb_smt_name(Tsymb symb)
{
  char * name;
  if (symb == CONNECTOR_EQUIV)
    return "iff";
  if (unary_minus(symb))
    return "~";
  if (symb == CONNECTOR_ITE)
    return "if_then_else";
  if (symb == CONNECTOR_IMPLIES)
    return "implies";
  if (symb == FUNCTION_ZERO_VARIABLE)
    return "veriT.zero";
  
  name = DAG_symb_name_rectify(symb);
  if (name[0] == '$')
    return name + 1;
  else return name;
}

/*--------------------------------------------------------------*/

static void
DAG_set_use_aux1(TDAG DAG)
/* PF set flag to the number of parents */
{
  int i;
  assert(DAG_tmp_int[DAG] < INT_MAX);
  if (DAG_tmp_int[DAG]++ > 0)
    return;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_set_use_aux1(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

static void
DAG_set_use_aux2(TDAG DAG, Ttable shared_DAG)
/* PF reset flag,
 assign misc & 0xFFFFFF00 to a counter for shared DAGs,
 add all shared DAGs in shared_DAG */
{
  unsigned i;
  if (!DAG_tmp_int[DAG])
    return;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_set_use_aux2(DAG_arg(DAG, i), shared_DAG);
  if (DAG_ground(DAG) && DAG_tmp_int[DAG] > 1 && DAG_arity(DAG) > 0 &&
      !(DAG_symb(DAG) == CONNECTOR_NOT && DAG_arity(DAG_arg0(DAG)) == 0))
  {
    table_push(shared_DAG, DAG_ptr_of(DAG));
    i = table_length(shared_DAG);
  }
  else
    i = 0;
  DAG_set_num(DAG, i);
  DAG_tmp_int[DAG] = 0;
}

/*--------------------------------------------------------------*/

static void
DAG_set_use(TDAG DAG, Ttable shared_DAG)
/* PF assign misc & 0xFFFFFF00 to a counter for shared DAGs,
 add all shared DAGs in shared_DAG */
{
  DAG_set_use_aux1(DAG);
  DAG_set_use_aux2(DAG, shared_DAG);
}

/*--------------------------------------------------------------*/

static unsigned
DAG_sort_fprint_len(Tsort sort)
{
  int i;
  unsigned tmp;
  if (!sort)
    return 4;
  if (sort_arity(sort) == 0)
    return (unsigned) strlen(sort_name(sort));
  if (sort_arity(sort) == DAG_SORT_NARY)
    return 8 + 2 * DAG_sort_fprint_len(sort_sub(sort, 0)) +
    DAG_sort_fprint_len(sort_sub(sort, 1));
  if (sort_name(sort) != NULL)
    return strlen(sort_name(sort));
  for (i = 0, tmp = 3; i < sort_arity(sort); i++)
    tmp += DAG_sort_fprint_len(sort_sub(sort, i));
  return tmp;
}

/*--------------------------------------------------------------*/

static void
DAG_sort_fprint(FILE * file, Tsort sort)
{
  int i;
  if (!sort)
    {
      fprintf(file, "NULL");
      return;
    }
  if (DAG_sort_parametric(sort))
    {
      fprintf(file, "(%s %d)", sort_name(sort), sort_arity(sort));
      return;
    }
  if (DAG_sort_instance(sort))
    {
      if (sort_name(sort))
	fprintf(file, "%s", sort_name(sort));
      else
	{
	  fprintf(file, "%s", sort_name(sort_sub(sort, 0)));
	  for (i = 1; i < sort_arity(sort); ++i)
	    DAG_sort_fprint(file, sort_sub(sort, i));
	}
      return;
    }
  if (sort_name(sort) != NULL)
    {
      fprintf(file, "%s", sort_name(sort));
      return;
    }
  if (sort_arity(sort) == DAG_SORT_NARY)
    {
      fprintf(file, "(");
      DAG_sort_fprint(file, sort_sub(sort, 0));
      fprintf(file, " ... ");
      DAG_sort_fprint(file, sort_sub(sort, 0));
      fprintf(file, " ");
      DAG_sort_fprint(file, sort_sub(sort, 1));
      fprintf(file, ")");
      return;
    }
  fprintf(file, "(");
  if (sort_name(sort))
    fprintf(file, "%s ", sort_name(sort));
  for (i = 0; i < sort_arity(sort); i++)
    {
      fprintf(file, i ? " " : "");
      DAG_sort_fprint(file, sort_sub(sort, i));
    }
  fprintf(file, ")");
}

/*--------------------------------------------------------------*/

void
DAG_sort_print(Tsort sort)
{
  DAG_sort_fprint(stdout, sort);
}

/*--------------------------------------------------------------*/

void
DAG_sort_fprint_smt_fun(FILE * file, Tsort sort)
{
  int i;
  if (!sort)
    fprintf(file, "NULL");
  else if (sort_arity(sort) == 0)
    fprintf(file, "%s", sort_name(sort));
  else if (sort_arity(sort) == DAG_SORT_NARY)
    {
      DAG_sort_fprint(file, sort_sub(sort, 0));
      fprintf(file, " ... ");
      DAG_sort_fprint(file, sort_sub(sort, 0));
      fprintf(file, " ");
      DAG_sort_fprint(file, sort_sub(sort, 1));
    }
  else if (DAG_sort_instance(sort))
    DAG_sort_fprint(file, sort);
  else						
    {
      for (i = 0; i < sort_arity(sort); i++)
	{
	  fprintf(file, i ? " " : "");
	  DAG_sort_fprint(file, sort_sub(sort, i));
	}
    }
}

/*--------------------------------------------------------------*/

void
DAG_sort_fprint_smt_pred(FILE * file, Tsort sort)
{
  int i;
  if (!sort)
  {
    fprintf(file, "NULL");
    return;
  }
  if (sort_arity(sort) == 0)
  {
    if (sort != SORT_BOOLEAN)
      my_error("DAG_sort_fprint_smt_pred : unexpected sort\n");
    /* DD was
     if (sort == SORT_BOOLEAN)
     fprintf(file, "%s", sort_name(sort));
     else
     my_error("DAG_sort_fprint_smt_pred : unexpected sort\n"); */
    return;
  }
  if (sort_arity(sort) == DAG_SORT_NARY)
  {
    DAG_sort_fprint(file, sort_sub(sort, 0));
    fprintf(file, " ... ");
    DAG_sort_fprint(file, sort_sub(sort, 0));
    if (sort_sub(sort, 1) != SORT_BOOLEAN)
      my_error("DAG_sort_fprint_smt_pred : unexpected sort\n");
    return;
  }
  for (i = 0; i < sort_arity(sort) - 1; i++)
  {
    fprintf(file, i ? " " : "");
    DAG_sort_fprint(file, sort_sub(sort, i));
  }
  if (sort_sub(sort, i) != SORT_BOOLEAN)
    my_error("DAG_sort_fprint_smt_pred : unexpected sort\n");
}

/*--------------------------------------------------------------*/

static unsigned
DAG_fprint_smt_aux2(TDAG DAG)
/* PF set flag to the printed length */
{
  int i;
  if (!DAG)
    return 4;
  if (DAG_tmp_int[DAG])
    return DAG_tmp_int[DAG];
  if (!DAG_arity(DAG))
  {
    char *str = DAG_symb_smt_name(DAG_symb(DAG));
    unsigned len = (unsigned) strlen(str);
    if (str[0] == '-') len += (unsigned) strlen("(~ )"); 
    if (DAG_is_number(DAG) && !DAG_is_integer(DAG))
    {
      char * ptr = str;
      while (*ptr && *ptr != '/')
        ++ptr;
      if (*ptr == '/') 
        len += (unsigned) strlen("(/ )");
    }
    DAG_tmp_int[DAG] = len;
    return len;
  }
  if (DAG_get_num(DAG))
  {
    char str[255];
    if (DAG_sort(DAG) == SORT_BOOLEAN)
      sprintf(str, "$VERIT_%i", (int) DAG_get_num(DAG));
    else
      sprintf(str, "?VERIT_%i", (int) DAG_get_num(DAG));
    DAG_tmp_int[DAG] = strlen(str);
    return DAG_tmp_int[DAG];
  }
  DAG_tmp_int[DAG] = 1 + strlen(DAG_symb_smt_name(DAG_symb(DAG)));
  if (binder(DAG_symb(DAG)))
  {
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
      DAG_tmp_int[DAG] += 3 +
	strlen(DAG_symb_smt_name(DAG_symb(DAG_arg(DAG, i))))
	+ DAG_sort_fprint_len(DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
    DAG_tmp_int[DAG] += 2 + DAG_fprint_smt_aux2(DAG_argn(DAG));
  }
  else				/* APPLY_LAMBDA and other */
    for (i = 0; i < DAG_arity(DAG); i++)
      DAG_tmp_int[DAG] += 1 + DAG_fprint_smt_aux2(DAG_arg(DAG, i));
  DAG_tmp_int[DAG] += 1;
  return DAG_tmp_int[DAG];
}

/*--------------------------------------------------------------*/

static void
DAG_fprint_smt_indent(FILE * file, unsigned n)
/* PF print n spaces */
{
  unsigned i;
  for (i = 0; i < n; i++)
    fprintf(file, " ");
}

/*
 --------------------------------------------------------------
 Printing DAGs : SMT-LIB 2.0 notation
 --------------------------------------------------------------
 */

/*--------------------------------------------------------------*/

static char * DAG_symb_smt2_name(Tsymb symb)
{
  char * name;
  if (symb == CONNECTOR_EQUIV)
    return "=";
  if (unary_minus(symb))
    return "-";
  if (symb == CONNECTOR_ITE)
    return "ite";
  if (symb == CONNECTOR_IMPLIES)
    return "=>";
  
  name = DAG_symb_name_rectify(symb);
  if (name[0] == '$')
    return name + 1;
  else return name;
}

/*--------------------------------------------------------------*/

static void
DAG_fprint_smt2_aux(FILE * file, unsigned n, TDAG DAG)
/* PF print formula, indented at column n */
{
  unsigned i, m;
  if (!DAG)
  {
    fprintf(file, "NULL");
    return;
  }
  if (!DAG_arity(DAG))
  {
    char *str = DAG_symb_smt2_name(DAG_symb(DAG));
    if (DAG_is_integer(DAG) && str[0] == '-')
      fprintf(file, "(- %s)", (str+1));
    else if (DAG_is_rational(DAG))
    {
      char * ptr = str;
      if (str[0] == '-') 
      {
        fprintf(file, "(- ");
        ++ptr;
      }
      while (*ptr && *ptr != '/') ++ptr;
      if (*ptr)
      {
        fprintf(file, "(/ ");
        ptr = str[0] == '-'? str+1 : str;
        while (*ptr != '/')
          fprintf(file, "%c", *ptr++);
        fprintf(file, " ");
        ++ptr;
        while (*ptr)
          fprintf(file, "%c", *ptr++);
        fprintf(file, ")");
      }
      else
        fprintf(file, "%s", str);
      if (str[0] == '-') 
      {
        fprintf(file, ")");
      }
    }
    else
      fprintf(file, "%s", str);
    return;
  }
  if (DAG_get_num(DAG))
  {
    fprintf(file, "?VERIT_%i", (int) DAG_get_num(DAG));
    return;
  }
  fprintf(file, "(%s", DAG_symb_smt2_name(DAG_symb(DAG)));
  m = 1 + n + (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG)));
  if (binder(DAG_symb(DAG)))
  {
    fprintf(file, " (");
    m += 1;
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
    {
      m += (i ? 4 : 3) + (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i)))) +
      DAG_sort_fprint_len(DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
      if (m > DAG_fprint_opt.columns)
      {
        m -=
        (i ? 4 : 3) +
        (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i)))) +
        DAG_sort_fprint_len(DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
        if (m > 1 + n + (int) strlen(DAG_symb_smt2_name(DAG_symb(DAG))) + 2)
        {
          m = 1 + n + (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG))) + 2;
          fprintf(file, "\n");
          DAG_fprint_smt_indent(file, m);
          m += 3 + (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i)))) +
          DAG_sort_fprint_len(DAG_symb_sort
                              (DAG_symb(DAG_arg(DAG, i))));
          fprintf(file, "(%s ",
                   DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i))));
          DAG_sort_fprint(file,
                           DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
          fprintf(file, ")");
        }
        else
        {
          m += (i ? 4 : 3) +
          (unsigned) strlen(DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i)))) +
          DAG_sort_fprint_len(DAG_symb_sort
                              (DAG_symb(DAG_arg(DAG, i))));
          fprintf(file, i ? " (%s " : "(%s ",
                   DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i))));
          DAG_sort_fprint(file,
                           DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
          fprintf(file, ")");
        }
      }
      else
      {
        fprintf(file, i ? " (%s " : "(%s ",
                 DAG_symb_smt2_name(DAG_symb(DAG_arg(DAG, i))));
        DAG_sort_fprint(file, DAG_symb_sort(DAG_symb(DAG_arg(DAG, i))));
        fprintf(file, ")");
      }
    }
    fprintf(file, ") ");
    
    DAG_fprint_smt2_aux(file, m + 2, DAG_argn(DAG));
    fprintf(file, ")");
    return;
  }
  /* APPLY_LAMBDA and other */
  if (m + DAG_tmp_int[DAG] > DAG_fprint_opt.columns && DAG_fprint_opt.newlines)
  {
    if (n + 2 > DAG_fprint_opt.column_to_indent)
      m = 0;
    else
      m = n + 2;
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, "\n");
      DAG_fprint_smt_indent(file, m);
      DAG_fprint_smt2_aux(file, m, DAG_arg(DAG, i));
    }
  }
  else
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, " ");
      DAG_fprint_smt2_aux(file, 0, DAG_arg(DAG, i));
    }
  fprintf(file, ")");
}

/*--------------------------------------------------------------*/

/* TODO handle correctly shared DAGs with bound variables */
void
DAG_fprint_smt2(FILE * file, TDAG DAG)
/* PF print formula, with all the required let */
{
  int i, j;
  char str[255];
  Ttable shared_DAG = NULL;
  shared_DAG = table_new(100, 10);
  DAG_tmp_reserve();
  if (!DAG_fprint_opt.flat)
  {
    qnt_ground(DAG);
    DAG_set_use(DAG, shared_DAG);
  }
  for (i = 0; i < table_length(shared_DAG); i++)
  {
    TDAG DAG = DAG_of_ptr(table_get(shared_DAG, i));
    unsigned n = DAG_get_num(DAG);
    DAG_set_num(DAG, 0);
    if (i && !DAG_fprint_opt.newlines)
      fprintf(file, " ");
    sprintf(str, "(let ((?VERIT_%u ", (unsigned int) n);
    fprintf(file, "%s", str);
    DAG_fprint_smt_aux2(DAG);
    DAG_fprint_smt2_aux(file, (unsigned) strlen(str), DAG);
    DAG_tmp_reset_int(DAG);
    DAG_set_num(DAG, n);
    fprintf(file, "))\n");
  }
  DAG_fprint_smt_aux2(DAG);
  DAG_fprint_smt2_aux(file, 0, DAG);
  DAG_tmp_reset_int(DAG);
  if (!DAG_fprint_opt.flat)
    fprintf(file, "\n");
  for (i = 0, j = 0; i < table_length(shared_DAG); i++, j++)
  {
    TDAG DAG = DAG_of_ptr(table_get(shared_DAG, i));
    if (j == DAG_fprint_opt.columns)
    {
      j = 0;
      fprintf(file, "\n)");
    }
    else
      fprintf(file, ")");
    DAG_set_num(DAG, 0);
  }
  DAG_tmp_release();
  table_free(&shared_DAG);
}

/*--------------------------------------------------------------*/

void
DAG_sort_fprint_smt2(FILE * file, Tsort sort)
{
  int i;
  int arity;
  if (!sort)
  {
    fprintf(file, "NULL");
    return;
  }
  arity = sort_arity(sort);
  if (arity == 0)
  {
    fprintf(file, "%s", sort_name(sort));
    return;
  }
  if (arity == DAG_SORT_NARY)
  {
    fprintf(file, "...");
    return;
  }
  if (DAG_sort_instance(sort))
  {
    fprintf(file, "(%s ", sort_name(sort_sub(sort, 0)));
    for (i = 1; i < arity; ++i)
    {
      if (i != 0) fprintf(file, " ");
      DAG_sort_fprint_smt2(file, sort_sub(sort, i));
    }
    fprintf(file, ")");
  }
  else
  {
    fprintf(file, "(");
    for (i = 0; i < arity - 1; ++i)
    {
      if (i != 0) fprintf(file, " ");
      DAG_sort_fprint_smt2(file, sort_sub(sort, i));
    }
    fprintf(file, ") ");
    DAG_sort_fprint_smt2(file, sort_sub(sort, arity - 1));
  }
}

/*--------------------------------------------------------------*/

void
DAG_fprint_smt2_assert(FILE * file, TDAG DAG)
{
  if (DAG_symb(DAG) == CONNECTOR_AND)
  {
    int i;
    for (i = 0; i < DAG_arity(DAG); ++i)
      DAG_fprint_smt2_assert(file, DAG_arg(DAG, i));
  }
  else
  {
    fprintf(file, "(assert ");
    DAG_fprint_smt2(file, DAG);
    fprintf(file, ")\n");
  }
}

/*--------------------------------------------------------------*/

/* TODO Recognise automagically the logic with symbols that are used? */

/* TODO
 for each polymorphic symbol, find all instances of the symbol,
 and print a "declare-fun" clause for each instance */
void
DAG_fprint_smt2_bench(FILE * file, TDAG DAG, char * status)
{
  unsigned i;
  Tsort sort;
  char * logic = DAG_smtlib_logic();
  if (logic)
    DAG_fprint_opt.logic = logic;
  fprintf(file, "(set-logic %s)\n", logic);
  fprintf(file, "(set-info :source | Benchmark generated by veriT |)\n");
  fprintf(file, "(set-info :smt-lib-version 2.0)\n");
  fprintf(file, "(set-info :status %s)\n", status);
  for (sort = 1; sort < DAG_sort_stack->size; sort++)
    if (!sort_predefined(sort) && sort_name(sort) && !DAG_sort_variable(sort))
      fprintf(file, "(declare-sort %s %d)\n", sort_name(sort),
	      sort_arity(sort));

  stack_INIT(collect_symbols);
  collect_symbols_DAG(DAG);

  for (i = 0; i < collect_symbols->size; i++)
    {
      Tsymb symb = collect_symbols->data[i];
      if (symb_predefined(symb)) continue;
      if (DAG_sort_polymorphic(symb_sort(symb))) 
	fprintf(file, ";;(par ");
      fprintf(file, "(declare-fun %s ", DAG_symb_name_rectify(symb));
      if (sort_arity(symb_sort(symb)) == 0)
	fprintf(file, "() %s", sort_name(symb_sort(symb)));
      else
	DAG_sort_fprint_smt2(file, symb_sort(symb));
      if (DAG_sort_polymorphic(symb_sort(symb))) 
	fprintf(file, ")");
      fprintf(file, ")\n");
    }
  stack_free(collect_symbols);
  
  DAG_fprint_smt2_assert(file, DAG);
  
  fprintf(file, "(check-sat)\n");
  fprintf(file, "(exit)\n");

  if (symbol_prefix)
    {
      free(symbol_prefix);
      symbol_prefix = NULL;
    }
  if (symbol_prefix_var)
    {
      free(symbol_prefix_var);
      symbol_prefix_var = NULL;
    }
}

/*
 --------------------------------------------------------------
 Printing DAGs : B notation
 --------------------------------------------------------------
 */

/*--------------------------------------------------------------*/

/** returns B ASCII identifier for symb */
static char *
DAG_symb_b_name(Tsymb symb)
{
  if (symb == CONNECTOR_AND)
    return "&";
  if (symb == CONNECTOR_IMPLIES)
    return "=>";
  if (symb == CONNECTOR_ITE)
    return "<=>";
  if (symb == PREDICATE_EQ)
    return "=";
  if (symb == PREDICATE_DISTINCT)
    return "/=";
  if (symb == QUANTIFIER_FORALL)
    return "!";
  if (symb == QUANTIFIER_EXISTS)
    return "#";
  if (unary_minus(symb))
    return "-";
  else return DAG_symb_smt_name(symb);
}

/*--------------------------------------------------------------*/

/** returns B ASCII identifier of sort */
static char *
DAG_sort_b_name(Tsort sort)
{
  if (sort == SORT_BOOLEAN)
    return "BOOL";
  if (sort == SORT_INTEGER)
    return "INTEGER";
  return sort_name(sort);
}

/*--------------------------------------------------------------*/

#if 0
static void
DAG_sort_fprint_b(FILE * file, Tsort sort)
{
  int i, arity;
  if (!sort)
  {
    fprintf(file, "NULL");
    return;
  }
  arity = sort_arity(sort);
  if (arity == 0)
  {
    fprintf(file, "%s", DAG_sort_b_name(sort));
    return;
  }
  if (arity == DAG_SORT_NARY)
  {
    fprintf(file, "(");
    DAG_sort_fprint_b(file, sort_sub(sort, 0));
    fprintf(file, " ... ");
    DAG_sort_fprint_b(file, sort_sub(sort, 0));
    fprintf(file, " ");
    DAG_sort_fprint_b(file, sort_sub(sort, 1));
    fprintf(file, ")");
    return;
  }
  for (i = 0; i < arity; i++)
  {
    fprintf(file, (i == arity - 1 ?  " --> " : (i > 0 ? " * " : "")));
    DAG_sort_fprint_b(file, sort_sub(sort, i));
  }
}
#endif

/*--------------------------------------------------------------*/

static void
DAG_fprint_b_aux1(FILE * file, unsigned n, TDAG DAG)
/* PF print formula, indented at column n */
{
  unsigned i, m;
  if (!DAG)
  {
    fprintf(file, "NULL");
    return;
  }
  if (!DAG_arity(DAG))
  {
    char *str = DAG_symb_b_name(DAG_symb(DAG));
    if (DAG_is_integer(DAG) && str[0] == '-')
      fprintf(file, "(- %s)", (str+1));
    else
      fprintf(file, "%s", str);
    return;
  }
  if (DAG_get_num(DAG))
  {
    fprintf(file, "VERIT_%i", (int) DAG_get_num(DAG));
    return;
  }
  if (DAG_symb(DAG) == QUANTIFIER_EXISTS || DAG_symb(DAG) == QUANTIFIER_FORALL)
  {
    fprintf(file, "(");
    fprintf(file, "%s (", DAG_symb_b_name(DAG_symb(DAG)));
    m = 1 + n;
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
    {
      if (i > 0)
        fprintf(file, ", ");
      DAG_fprint_b_aux1(file, m, DAG_arg(DAG, i));
    }
    fprintf(file, ").(");
    for (i = 0; i < DAG_arity(DAG) - 1; i++)
    {
      if (i > 0)
        fprintf(file, " & ");
      DAG_fprint_b_aux1(file, m, DAG_arg(DAG, i));
      fprintf(file, " : %s", DAG_sort_b_name(DAG_sort(DAG_arg(DAG, i))));
    }
    if (DAG_symb(DAG) == QUANTIFIER_EXISTS)
      fprintf(file, " & ");
    else
      fprintf(file, " => ");
    DAG_fprint_b_aux1(file, m, DAG_argn(DAG));
    fprintf(file, "))");
    return;
  }
  if (!symb_interpreted(DAG_symb(DAG)))
  {
    fprintf(file, "%s(", DAG_symb_b_name(DAG_symb(DAG)));
    m = 1 + n;
    for (i = 0; i < DAG_arity(DAG); ++i)
    {
      if (i > 0)
        fprintf(file, ", ");
      DAG_fprint_b_aux1(file, m, DAG_arg(DAG, i));
    }
    fprintf(file, ")");
    return;
  }
  if (DAG_arity(DAG) == 1)
  {
    fprintf(file, "(%s ", DAG_symb_b_name(DAG_symb(DAG)));
    m = n + 1;
    DAG_fprint_b_aux1(file, m, DAG_arg0(DAG));
    fprintf(file, ")");
    return;
  }
  /* APPLY_LAMBDA and other */
  fprintf(file, "(");
  m = 1 + n;
  if (m + DAG_tmp_int[DAG] > DAG_fprint_opt.columns && DAG_fprint_opt.newlines)
  {
    if (n + 2 > DAG_fprint_opt.column_to_indent)
      m = 0;
    else
      m = n + 2;
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      DAG_fprint_smt_indent(file, m);
      if (i > 0)
      {
        fprintf(file, " %s ", DAG_symb_b_name(DAG_symb(DAG)));
        m += (unsigned) strlen(DAG_symb_b_name(DAG_symb(DAG)));
      }
      
      DAG_fprint_b_aux1(file, m, DAG_arg(DAG, i));
    }
  }
  else
    for (i = 0; i < DAG_arity(DAG); i++)
    {
      fprintf(file, " ");
      if (i > 0)
      {
        fprintf(file, " %s ", DAG_symb_b_name(DAG_symb(DAG)));
      }
      DAG_fprint_b_aux1(file, 0, DAG_arg(DAG, i));
    }
  fprintf(file, ")");
}

/*--------------------------------------------------------------*/

static unsigned
DAG_fprint_b_aux2(TDAG DAG)
/* PF set flag to the printed length */
{
  int i;
  if (!DAG)
    return 4;
  if (DAG_tmp_int[DAG])
    return DAG_tmp_int[DAG];
  if (!DAG_arity(DAG))
  {
    char *str = DAG_symb_b_name(DAG_symb(DAG));
    unsigned len = (unsigned) strlen(str);
    if (str[0] == '-') len += (unsigned) strlen("(- )"); 
    DAG_tmp_int[DAG] = len;
    return len;
  }
  if (DAG_get_num(DAG))
  {
    char str[255];
    if (DAG_sort(DAG) == SORT_BOOLEAN)
      sprintf(str, "VERIT_%i", (int) DAG_get_num(DAG));
    DAG_tmp_int[DAG] = strlen(str);
    return DAG_tmp_int[DAG];
  }
  DAG_tmp_int[DAG] = 1 + strlen(DAG_symb_b_name(DAG_symb(DAG)));
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_int[DAG] += 1 + DAG_fprint_b_aux2(DAG_arg(DAG, i));
  DAG_tmp_int[DAG] += 1;
  return DAG_tmp_int[DAG];
}

/*--------------------------------------------------------------*/

void
DAG_fprint_b_aux(FILE * file, TDAG DAG)
/* PF print formula, with all the required let */
{
  DAG_fprint_b_aux2(DAG);
  DAG_fprint_b_aux1(file, 0, DAG);
  DAG_tmp_reset_int(DAG);
  if (!DAG_fprint_opt.flat)
    fprintf(file, "\n");
}

/*--------------------------------------------------------------*/

/* TODO Recognise automagically the logic with symbols that are used? */
/* TODO Recognise automagically the logic with symbols that are used? */
/* TODO handle correctly shared DAGs with bound variables */
void
DAG_fprint_b(FILE * file, TDAG DAG)
{
  unsigned i;
  int first;
  char * logic = DAG_smtlib_logic();
  if (logic)
    DAG_fprint_opt.logic = logic;
  
  fprintf(file, "MACHINE smt \n");
  
  stack_INIT(collect_symbols);
  collect_symbols_DAG(DAG);
  
  if (collect_symbols->size)
  {
    fprintf(file, "  CONSTANTS\n");
    first = 1;
    for (i = 0; i < collect_symbols->size; i++)
      {
	if (!first && DAG_fprint_opt.newlines)
	  fprintf(file, ",\n");
	first = 0;
	fprintf(file, "    %s", DAG_symb_b_name(collect_symbols->data[i]));
      }
    for (i = 0; i < collect_symbols->size; i++)
      {
	if (!first && DAG_fprint_opt.newlines)
	  fprintf(file, ",\n");
	first = 0;
	fprintf(file, "    %s", DAG_symb_b_name(collect_symbols->data[i]));
      }
    fprintf(file, "  PROPERTIES\n");
    first = 1;
    for (i = 0; i < collect_symbols->size; i++)
      {
	if (!first && DAG_fprint_opt.newlines)
	  fprintf(file, " &\n");
	first = 0;
	fprintf(file, "    %s : %s",
		DAG_symb_b_name(collect_symbols->data[i]), 
		DAG_sort_b_name(collect_symbols->data[i]));
      }
    fprintf(file, "\n");
  }

  if (collect_symbols->size)
    fprintf(file, "    &\n");
  DAG_fprint_b_aux(file, DAG);
  
  stack_free(collect_symbols);
  
  fprintf(file, "END\n");
}

/*--------------------------------------------------------------*/

void
DAG_fprint_smt2_set(FILE * file, TDAG * DAG, unsigned n, char * status)
{
  unsigned i, j;
  bool tmp;
  TDAG DAG2, *DAG3;
  MY_MALLOC(DAG3, n * sizeof(TDAG));
  for (i = 0, j = 0; i < n; i++)
    if (DAG_literal(DAG[i]))
      DAG3[j++] = DAG[i];
  DAG2 = DAG_dup(DAG_new(CONNECTOR_AND, j, DAG3));
  tmp = DAG_fprint_opt.flat;
  DAG_fprint_opt.flat = true;
  DAG_fprint_smt2_bench(file, DAG2, status);
  DAG_fprint_opt.flat = tmp;
  DAG_free(DAG2);
}

/*
 --------------------------------------------------------------
 outputting messages with DAGs
 --------------------------------------------------------------
 */

#define MAX_FORMAT 32

/**
 \author Thomas Bouton
 printing function.  Supports all printf-like formats with the exception of :
 - $ directives
 - %n directive
 supports the %D directive to print TDAG trees
 \param file the output file
 \param format the format string
 \param params the parameters (depend on the format string)
 */
static void
my_DAG_aux(FILE *file, char *format, va_list params)
{
  char *f = format;
  char c;
  
  while (1)
  {
    c = *f++;
    if (c == '\0') break;
    if (c == '%')
    {
      char sub_format[MAX_FORMAT];
      int i = 0;
      char ch = *f;
      memset(sub_format, '\0', MAX_FORMAT);
      sub_format[i++] = '%';
      if (ch == '#' || ch == '-' || ch == ' ' /*isspace(ch)*/ || ch == '+')
        sub_format[i++] = *f++;
      while (isdigit(*f))
      {
        sub_format[i++] = *f++;
        if (i >= MAX_FORMAT)
          return;
      }
      if ((*f) == '.')
      {
        sub_format[i++] = *f++;
        while(isdigit(*f))
        {
          sub_format[i++] = *f++;
          if (i >= MAX_FORMAT)
            return;
        }
      }
      switch (ch = *f)
      {
        case 'h':
          sub_format[i++] = ch;
          if ((ch = *f++) == 'h' && i < MAX_FORMAT)
            sub_format[i++] = ch;
          break;
        case 'l':
          sub_format[i++] = ch;
          if ((ch = *f++) == 'l' && i < MAX_FORMAT)
            sub_format[i++] = ch;
          break;
        case 'L':
        case 'q':
        case 'j':
        case 't':
          sub_format[i++] = ch;
          ch = *f++;
      }
      if (i >= MAX_FORMAT)
        return;
      switch(ch = *f++)
      {
        case '%':
          fprintf(file, "%%");
          break;
        case 'D':
          DAG_fprint(file, ((TDAG)va_arg(params, TDAG)));
          break;
        case 'c':
        case 'd':
        case 'i':
          sub_format[i++] = ch;
          fprintf(file, sub_format, ((int)va_arg(params, int)));
          break;
        case 'o':
        case 'u':
        case 'x':
        case 'X':
          sub_format[i++] = ch;
          fprintf(file, sub_format, ((unsigned int)va_arg(params, unsigned int)));
          break;
        case 'f':
        case 'F':
        case 'g':
        case 'G':
        case 'a':
        case 'A':
          sub_format[i++] = ch;
          fprintf(file, sub_format, ((double)va_arg(params, double)));
          break;
        case 's':
          sub_format[i++] = ch;
          fprintf(file, sub_format, va_arg(params, char*));
          break;
        case 'S':
          DAG_sort_fprint(file, (Tsort) va_arg(params, int));
          break;
        case 'p':
          sub_format[i++] = ch;
          fprintf(file, sub_format, va_arg(params, void*));
          break;
        case 'n':
          sub_format[i++] = ch;
          fprintf(file, "<<%%n unsupported>>");
          break;
        default:
          fprintf(file, "<<Error while parsing format - Leaving my_message>>\n");
          return;
      }
    }
    else
    {
      fprintf(file, "%c", c);
    }
  }
}

/*--------------------------------------------------------------*/

void
my_DAG_error(char *format, ...)
{
  va_list params;
  va_start(params, format);
  fprintf(stderr, "error : ");
  my_DAG_aux(stderr, format, params);
  va_end(params);
  exit(1);
}

/*--------------------------------------------------------------*/

void
my_DAG_message(char *format, ...)
{  
  va_list params;
  
  if (SILENT)
    return;
  
  va_start(params, format);
  fprintf(stderr, "MSG : ");
  my_DAG_aux(stderr, format, params);
  va_end(params);
}

/*--------------------------------------------------------------*/

void
my_DAG_warning(char *format, ...)
{  
  va_list params;
  if (DAG_fprint_opt.verbosity == 0) return;
  va_start(params, format);
  fprintf(stderr, "warning : ");
  my_DAG_aux(stderr, format, params);
  va_end(params);
}

