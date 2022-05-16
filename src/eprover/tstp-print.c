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
  TSTP printer

  Obs. 
  Symbols (resp. DAGs) are printed as 's%x' (resp. 't%x'), where %x 
  is the hexadecimal index of the Tsymb (resp. TDAG) value.
  --------------------------------------------------------------
*/

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "general.h"

#include "DAG.h"
#include "DAG-tmp.h"
#include "DAG-ptr.h"
#include "veriT-DAG.h"
#include "congruence.h"

#include "eprover-int.h"
#include "tstp.h"
#include "tstp-parser.h"


/*--------------------------------------------------------------*/
static void (* print_atom) (FILE *, const TDAG);
static void (* print_deep) (FILE *, const TDAG);
static void (* print_shallow) (FILE *, const TDAG);
static void (* print_root) (FILE *, const TDAG);

static void tstp_formula (FILE *, const TDAG);
static void tstp_quantifier (FILE *, const TDAG);

static void tstp_abstract_pred (FILE *, const TDAG);
static void tstp_abstract_term (FILE *, const TDAG, const TDAG);
static void tstp_merge (FILE *, const TDAG, const TDAG);
static void tstp_abstract_quant (FILE *, const TDAG);

/*--------------------------------------------------------------*/

/**
   \brief symbol for sort function of a given DAG's sort
   \param DAG a DAG
   \pre   The sort of DAG has been bound to a symbol through
   attribute binding.
   \return the bound symbol
*/

static Tsymb
tstp_fun_of_sort(TDAG DAG)
{
  if (DAG_sort(DAG) == SORT_BOOLEAN)
    return DAG_SYMB_NULL;
  assert(DAG_sort_binding(DAG_sort(DAG)));
  return DAG_symb_of_ptr(DAG_sort_binding(DAG_sort(DAG)));
}

/*--------------------------------------------------------------*/

/**
   \brief TSTP symbol for SMT function symbol
   \param symb a function or predicate symbol
   \pre   The TSTP symbol corresponding to \c symb has been 
   set in the attribute \c Pflag.
   \return the bound symbol
*/

static Tsymb
tstp_fun_of_symb(Tsymb symb)
{
  return DAG_symb_of_ptr(DAG_symb_Pflag(symb));
}

/*--------------------------------------------------------------*/

static void
print_root_sort_fun(FILE * file, const TDAG DAG)
{
  if (DAG_symb_is_predicate(DAG_symb(DAG)))
    fprintf(file, "'t%x'", DAG_tmp_DAG[DAG]);
  else
    fprintf(file, "'s%x'('t%x')", tstp_fun_of_sort(DAG), DAG_tmp_DAG[DAG]);
}

/*--------------------------------------------------------------*/

static void
print_deep_sort_fun (FILE * file, const TDAG DAG)
{
  fprintf(file, "'s%x'(", tstp_fun_of_sort(DAG));
  if (DAG_ground(DAG) && !DAG_quant(DAG) && DAG_sort(DAG) != SORT_BOOLEAN)
    fprintf (file, "'t%x'", DAG_tmp_DAG[DAG]);
  else if (DAG_symb_type(DAG_symb(DAG)) == SYMB_VARIABLE)
    fprintf(file, "X%s", 1+DAG_symb_name(DAG_symb(DAG)));
  else
    {
      fprintf(file, "'s%x'", tstp_fun_of_symb(DAG_symb(DAG)));
      if (DAG_arity(DAG) != 0)
	{
	  int i;
	  fputc('(', file);
	  for (i = 0; i < DAG_arity(DAG); ++i)
	    {
	      if (i != 0) fputc(',', file);
	      print_deep_sort_fun(file, DAG_arg(DAG, i));
	    }
	  fputc(')', file);
	}
    }
  fputc(')', file);
}

/*--------------------------------------------------------------*/

static void
print_shallow_sort_fun(FILE * file, const TDAG DAG)
{
  if (!DAG_symb_is_predicate(DAG_symb(DAG)))
    fprintf(file, "'s%x'(", tstp_fun_of_sort(DAG));
  fprintf(file, "'s%x'", DAG_symb_of_ptr(DAG_symb_Pflag(DAG_symb(DAG))));
  if (DAG_arity(DAG) != 0)
    {
      int i;
      fputc('(', file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputc(',', file);
	  print_root_sort_fun(file, DAG_arg(DAG, i));
	}
      fputc(')', file);
    }
  if (!DAG_symb_is_predicate(DAG_symb(DAG)))
    fputc(')', file);
}

/*--------------------------------------------------------------*/

static void
print_atom_sort_fun(FILE * file, const TDAG DAG)
{
  fprintf(file, "'s%x'", tstp_fun_of_symb(DAG_symb(DAG)));
  if (DAG_arity(DAG) != 0)
    {
      int i;
      fputc('(', file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputc(',', file);
	  print_deep(file, DAG_arg(DAG, i));
	}
      fputc(')', file);
    }
}

/*--------------------------------------------------------------*/

static void
print_root_sort_erase(FILE * file, const TDAG DAG)
{
  fprintf(file, "'t%x'", DAG_of_ptr(DAG));
}

/*--------------------------------------------------------------*/

static void
print_deep_sort_erase(FILE * file, const TDAG DAG)
{
  if (DAG_ground(DAG) && !DAG_quant(DAG) && DAG_sort(DAG) != SORT_BOOLEAN)
    fprintf (file, "'t%x'", DAG_of_ptr(DAG));
  else if (DAG_symb_type(DAG_symb(DAG)) == SYMB_VARIABLE)
    fprintf(file, "X%s", 1+DAG_symb_name(DAG_symb(DAG)));
  else
    {
      int i;
      fprintf (file, "'s%x'", DAG_symb(DAG));
      if (DAG_arity(DAG) > 0) {
	fputc('(', file);
	for (i = 0; i < DAG_arity(DAG); ++i)
	  {
	    if (i != 0) fputc(',', file);
	    print_deep_sort_erase(file, DAG_arg(DAG, i));
	  }
	fputc(')', file);
      }
    }
}

/*--------------------------------------------------------------*/

static void
print_shallow_sort_erase(FILE * file, const TDAG DAG)
{
  fprintf(file, "'s%x'", DAG_symb(DAG));
  if (DAG_arity(DAG) != 0)
    {
      int i;
      fputc('(', file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputc(',', file);
	  print_root_sort_erase(file, DAG_arg(DAG, i));
	}
      fputc(')', file);
    }
}

/*--------------------------------------------------------------*/

static void
print_atom_sort_erase(FILE * file, const TDAG DAG)
{
  fprintf(file, "'s%x'", DAG_symb(DAG));
  if (DAG_arity(DAG) != 0)
    {
      int i;
      fputc('(', file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputc(',', file);
	  print_deep(file, DAG_arg(DAG, i));
	}
      fputc(')', file);
    }
}


/*--------------------------------------------------------------*/

static void
tstp_formula(FILE * file, const TDAG DAG)
{
  int    i;
  Tsymb  symb = DAG_symb(DAG);
  
  if (symb == BOOLEAN_TRUE)
    fputs ("$true", file);
  else if (symb == BOOLEAN_FALSE)
    fputs ("$false", file);
  else if (symb == CONNECTOR_NOT)
    {	  
      fputs ("~ ", file);
      tstp_formula(file, DAG_arg0(DAG));
    }
  else if (symb == CONNECTOR_OR)
    {
      fputs ("(", file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputs(" | ", file);
	  tstp_formula(file, DAG_arg(DAG, i));
	}
      fputs (")", file);
    }
  else if (symb == CONNECTOR_AND)
    {
      fputs ("(", file);
      for (i = 0; i < DAG_arity(DAG); ++i)
	{
	  if (i != 0) fputs(" & ", file);
	  tstp_formula(file, DAG_arg(DAG, i));
	}
      fputs (")", file);
    }
  else if (symb == CONNECTOR_IMPLIES)
    {
      assert(DAG_arity(DAG) == 2);
      fputs ("(", file);
      tstp_formula(file, DAG_arg0(DAG));
      fputs(" => ", file);
      tstp_formula(file, DAG_arg(DAG, 1));
      fputs (")", file);
    }
  else if (DAG_sort(DAG_arg0(DAG)) == SORT_BOOLEAN &&
	   (symb == CONNECTOR_EQUIV || symb == PREDICATE_EQ))
    {
      assert(DAG_arity(DAG) == 2);
      fputs ("(", file);
      tstp_formula(file, DAG_arg0(DAG));
      fputs(" <=> ", file);
      tstp_formula(file, DAG_arg(DAG, 1));
      fputs (")", file);
    }
  else if (symb == CONNECTOR_ITE)
    {
      assert(DAG_arity(DAG) == 3);
      fputc('(', file);
      tstp_formula(file, DAG_arg0(DAG));
      fputs(" => ", file);
      tstp_formula(file, DAG_arg(DAG, 1));
      fputs(") & (~(", file);
      tstp_formula(file, DAG_arg0(DAG));
      fputs(") => ", file);
      tstp_formula(file, DAG_arg(DAG, 2));
      fputc(')', file);
    }
  else if (symb == PREDICATE_EQ)
    {
      fputs ("(", file);
      print_deep(file, DAG_arg0(DAG));
      fputs (" = ", file);
      print_deep(file, DAG_arg(DAG, 1));
      fputs (")", file);
    }
  else if (DAG_symb_type(symb) == SYMB_QUANTIFIER)
    {
      fputs ("(", file);
      tstp_quantifier (file, DAG);
      fputs (")", file);
    }
  else /* DAG is an atom */
    {
      print_atom(file, DAG);
    }
}


/*--------------------------------------------------------------*/

static void
tstp_quantifier(FILE * file, const TDAG DAG)
{
  int i;
  assert(DAG_symb_type(DAG_symb(DAG)) == SYMB_QUANTIFIER);
  
  fputc(DAG_symb(DAG) == QUANTIFIER_FORALL ? '!' : '?', file);
  fputc('[', file);
  for (i = 0; i < DAG_arity(DAG) - 1; ++i)
    {
      if (i != 0) fputc(',', file);
      fprintf(file, "X%s", 1+DAG_symb_name(DAG_symb(DAG_arg(DAG, i))));
    }
  fputs("] : ", file);
  tstp_formula(file, DAG_argn(DAG));
}

/*--------------------------------------------------------------*/

static void
tstp_abstract_quant (FILE * file, const TDAG formula)
{
  tstp_quantifier (file, formula);
}

/*--------------------------------------------------------------*/

static void 
tstp_abstract_pred (FILE * file, const TDAG formula)
{
  print_shallow(file, formula);
}

/*--------------------------------------------------------------*/

static void
tstp_abstract_term (FILE * file, const TDAG DAG0, const TDAG DAG1)
{
  if (DAG_symb_is_predicate(DAG_symb(DAG0)))
    tstp_abstract_pred(file, DAG0);
  else
    {
      print_root(file, DAG1);
      fputs(" = ", file);
      print_shallow(file, DAG0);
    }
}

/*--------------------------------------------------------------*/

static void
tstp_merge (FILE * file, const TDAG DAG0, const TDAG DAG1)
{
  print_root(file, DAG0);
  fputs(" = ", file);
  print_root(file, DAG1);
}

/*--------------------------------------------------------------*/

/* this module receives clues that satisfy:
   clue->quantified is set (quantified);
*/

void
tstp_print_clue (FILE * file, Tclue clue, uintptr_t id, int erase_sort)
{
  assert (clue == NULL || clue->type != CLUE_LITERAL);
  fprintf(file, "%s(veriT_clue%lu,plain, ", 
	  clue->type == CLUE_ABSTRACT_QUANT ? "fof" : "cnf", 
	  (unsigned long) id++);
  if (erase_sort)
    {
      print_atom = print_atom_sort_erase;
      print_root = print_root_sort_erase;
      print_deep = print_deep_sort_erase;
      print_shallow = print_shallow_sort_erase;
    }
  else
    {
      print_atom = print_atom_sort_fun;
      print_root = print_root_sort_fun;
      print_deep = print_deep_sort_fun;
      print_shallow = print_shallow_sort_fun;
    }
  if (clue == NULL)
    fprintf(file, "$true");
  else 
    {
      if (!clue->polarity)
	fputs ("~", file);
      if (clue->type == CLUE_ABSTRACT_QUANT)
	tstp_abstract_quant(file, clue->DAG[0]);
      else if (clue->type == CLUE_ABSTRACT_PRED)
	tstp_abstract_pred(file, clue->DAG[0]);
      else if (clue->type == CLUE_ABSTRACT_TERM)
	tstp_abstract_term(file, clue->DAG[0], clue->DAG[1]);
      else if (clue->type == CLUE_MERGE)
	tstp_merge(file, clue->DAG[0], clue->DAG[1]);
      if (!clue->polarity)
	{
	  assert(clue->type != CLUE_ABSTRACT_TERM);
	  fputs("", file);
	}
    }
  fprintf(file, ").\n");
}
