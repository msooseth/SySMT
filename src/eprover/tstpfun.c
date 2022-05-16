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

/* ------------------------------------------------------------------- */

/* ------------------------------------------------------------------- */
/* #define DEBUG_TSTPFUN */
/* #define DEBUG_TSTP_PARSER */

#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "general.h"

#include "DAG.h"
#include "DAG-print.h"
#include "DAG-ptr.h"
#include "DAG-tmp.h"
#include "hash.h"
#include "hashmap.h"
#include "list.h"
#include "polarities.h"
#include "qnt-tidy.h"
#include "set.h"
#include "table.h"

#include "clue.h"

#include "eprover.h"
#include "eprover-int.h"
#include "tstp-parser.h"
#include "tptp-logic.h"

#include "tstpfun.h"

#include "config.h"

/* ------------------------------------------------------------------- */

/** variables refered to by the Bison/Flex generated code */
extern FILE *tstp_in; /** stream it parses from */
extern int tstp_lineno; /** stores the current line number */

#ifdef DEBUG_TSTP_PARSER
int tstp_debug;   /** debugging flag */
#endif
/* ------------------------------------------------------------------- */

/** other global variables accessed by the parser */

const char SZS_STATUS_STR [] = "# SZS status: ";
const int SZS_STATUS_SZ = (sizeof(SZS_STATUS_STR) / sizeof(char)) - 1;

/**
   \note On each line, the free variables need to be recorded so that
   they appear explicitly universally quantified in the DAG
   corresponding to the derived formula.  Free variables are typeset
   in uppercase, just as explicitly quantified variables. To
   distinguish them, the parser flags the explicitly quantified
   variables. When an uppercase variable appears in an expression, and
   it is not flagged, then it is a free variable.
*/

/** the list of free variables found in the current line */
static Tlist tstp_free_vars = NULL;

/** records if the keyword "final" has been parsed in the current line */
static int tstp_final_clause = 0;

/* ------------------------------------------------------------------- */

/**
   \brief initializes variables in the scope of the file
   \note call before parsing a new TSTP file */
static void
tstp_parse_init(void)
{
  tstp_free_vars = NULL;
  tstp_final_clause = 0;
  DAG_tmp_reserve();
}

/* ------------------------------------------------------------------- */

/**
   \brief frees up resources allocated by variables in the file scope */
static void
tstp_parse_done(void)
{
  list_free(&tstp_free_vars);
  DAG_tmp_release();
}

/* ------------------------------------------------------------------- */

/**
   \brief Finds symbol for variable with a given name
   \param name the name of the variable
   \return a variable symbol of sort \c e_sort and name \c name.
   \note Caches previous results.
   \note Destructive for \c name.
 */
static TDAG
tstp_variable(char * name)
{
  TDAG DAG;
  Tsymb symb = DAG_symb_lookup_sort(name, tptp_sort);
  if (symb == DAG_SYMB_NULL)
    symb = DAG_symb_new(name, SYMB_VARIABLE, tptp_sort);
  free(name);
  DAG = DAG_new(symb, 0, NULL);
  return DAG;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_quantified_variable(char * name)
{
  TDAG DAG;
  DAG = tstp_variable(name);
  DAG_tmp_bool[DAG] = 1;
  return DAG;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_expression_variable(char * name)
{
  TDAG DAG;
  DAG = tstp_variable(name);
  if (!DAG_tmp_bool[DAG])
    {
      tstp_free_vars = list_cons(DAG_ptr_of(DAG), tstp_free_vars);
      DAG_tmp_bool[DAG] = 1;
    }
  return DAG;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_quantified_formula(Tsymb quantifier, Tlist * Pvariables, TDAG DAG)
{
  TDAG result;
  assert(*Pvariables);
  list_apply(*Pvariables, (TFapply) & DAG_tmp_reset_bool);
  *Pvariables = list_add(*Pvariables, DAG_ptr_of(DAG));
  result = DAG_new_list(quantifier, *Pvariables);
  list_free(Pvariables);
  return result;
}

/* ------------------------------------------------------------------- */

void
tstp_parse_file(char * filename)
{
#ifdef DEBUG_TSTP_PARSER
  tstp_debug = 1;
#endif
  tstp_lineno = 1;
  tstp_in = fopen(filename, "r");
  if (tstp_in == 0)
    my_error("error: parse_file: cannot open file %s\n", filename);
  tstp_parse_init();
  tstp_parse();
  tstp_parse_done();
  fclose(tstp_in);
}

/* ------------------------------------------------------------------- */

void
tstp_error(char *s)
{
  my_error("%s on line %d\n", s, tstp_lineno);
}

/* ------------------------------------------------------------------- */

TDAG
tstp_equality(TDAG left, TDAG right, int polarity)
{
  TDAG result = DAG_eq(left, right);
  if (polarity == POL_NEG)
    return DAG_not(result);
  else
    return result;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_cnf_formula(Tlist list)
{
  TDAG result = (list_cdr(list) == list)?DAG_of_ptr(list_car(list)):
    DAG_new_list(CONNECTOR_OR, list);
  list_free(&list);
  return result;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_binary_connective(Tbinary_connective connector, TDAG a1, TDAG a2)
{
  switch (connector)
    {
    case EQV:
      return DAG_equiv(a1, a2);
    case LIMPL:
      return DAG_implies(a1, a2);
    case RIMPL:
      return DAG_implies(a2, a1);
    case NEQV:
      return DAG_equiv(a1, a2);
    case NOR:
      return DAG_not(DAG_or2(a1, a2));
    case NAND:
      return DAG_not(DAG_and2(a1, a2));
    default:
      my_error("unknown boolean connector found line %d.\n", tstp_lineno);
      return DAG_equiv(a1, a2);
    }
}

/* ------------------------------------------------------------------- */

TDAG
tstp_or(Tlist list)
{
  TDAG DAG = DAG_new_list(CONNECTOR_OR, list);
  list_free(&list);
  return DAG;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_and(Tlist list)
{
  TDAG DAG = DAG_new_list(CONNECTOR_AND, list);
  list_free(&list);
  return DAG;
}

/* ------------------------------------------------------------------- */

void
tstp_comment(char * comment_str)
{
  if (strncmp(comment_str, SZS_STATUS_STR, SZS_STATUS_SZ) == 0)
    {
      char * value_str = comment_str + SZS_STATUS_SZ;
      if (strcmp(value_str, "ResourceOut") == 0)
	{
	  e_set_status(UNDEF);
	}
      else if (strcmp(value_str, "GaveUp") == 0)
	{
	  e_set_status(UNDEF);
	}
      else if (strcmp(value_str, "InputError") == 0)
	{
	  my_error("error: input error reported by eprover.");
	  e_set_status(UNDEF);
	}
      else if (strcmp(value_str, "Unsatisfiable") == 0)
	{
	  e_set_status(UNSAT);
	}
      else if (strcmp(value_str, "Unknown") == 0)
	{
	  e_set_status(UNDEF);
	}
      else if (strcmp(value_str, "Satisfiable") == 0)
	{
	  e_set_status(SAT);
	}
      else
	{
	  e_set_status(UNDEF);
	}
    }
  free(comment_str);
}

/* ------------------------------------------------------------------- */

char *
tstp_single_quoted(char * quoted)
{
  free(quoted);
  return NULL;
}

/* ------------------------------------------------------------------- */

void 
tstp_inference(const Tpremisse p, const Trole role, TDAG DAG, Tlist premisses)
{
  uintptr_t id;
  Tinference inference;
  assert(premisse_is_internal(p));
  id = premisse_value(p);
  if (tstp_free_vars)
    DAG = tstp_quantified_formula(QUANTIFIER_FORALL, &tstp_free_vars, DAG);
  /* DAG = qnt_tidy(DAG_dup(DAG));
     qnt_ground(DAG); */
  /* DD TODO check if we can apply simplifications or other processing */

  inference = inference_new(DAG, premisses, role, tstp_final_clause);
#ifdef DEBUG_TSTP_PARSER
  inference_fprint(stderr, inference);
#endif
  table_resize(e_derivation->steps, id+1);
  table_set(e_derivation->steps, id, inference);
  if (e_derivation->conflict == 0 && DAG == DAG_FALSE)
    e_derivation->conflict = id;
}

/* ------------------------------------------------------------------- */

TDAG
tstp_function_term(Tsymb symb, Tlist list)
{
  TDAG result = DAG_new_list(symb, list);
  list_free(&list);
  return result;
}
