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
  Clue Module
  --------------------------------------------------------------
*/

#ifdef DEBUG
#include <stdio.h>
#endif

#include "config.h"
#include "general.h"
#include "clue.h"
#include "literal.h"

#include "DAG-stat.h"

/* #define DEBUG_CLUE */

#ifdef DEBUG_CLUE
#include "clue-print.h"
#define OUTPUT_CLUE(a) my_message("New clue\n"); clue_print2(a);
#else
#define OUTPUT_CLUE(a)
#endif

static Tclue
clue_new(void)
{
  Tclue clue;
  MY_MALLOC(clue, sizeof(struct TSclue));
  clue->type = CLUE_NONE;
  clue->origin = 0;
  clue->polarity = 0;
  clue->gc_count = 1;
  clue->misc = 0;
#ifdef PROOF
  clue->proof_id = 0;
#endif
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_literal(Tlit lit)
{
  Tclue clue = clue_new();
  TDAG DAG = var_to_DAG(lit_var(lit));
  clue->type = CLUE_LITERAL;
  clue->origin = DP_MAX; /* DD+PF for safety (not really needed) */
  clue->polarity = lit_pol(lit);
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      clue->polarity = 1 - clue->polarity;
      DAG = DAG_arg0(DAG);
    }
  clue->proof.lit = lit;
  if (DAG_symb(DAG) == PREDICATE_EQ)
    {
      clue->DAG[0] = DAG_dup(DAG_arg0(DAG));
      clue->DAG[1] = DAG_dup(DAG_arg1(DAG));
    }
  else
    {
      clue->DAG[0] = DAG_dup(DAG);
      clue->DAG[1] = DAG_NULL;
    }
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_merge(TDAG DAG1, TDAG DAG2, unsigned origin, TUproof proof)
{
  Tclue clue = clue_new();
  clue->type = CLUE_MERGE;
  clue->origin = origin;
  clue->polarity = 1;
  clue->proof = proof;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_congruent(TDAG DAG1, TDAG DAG2)
{
  Tclue clue = clue_new();
  clue->type = CLUE_CONGRUENT;
  clue->origin = 0;
  clue->polarity = 1;
  clue->proof.generic = NULL;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_inequality(TDAG DAG1, TDAG DAG2, unsigned origin, TUproof proof)
{
  Tclue clue = clue_new();
  clue->type = CLUE_INEQUALITY;
  clue->origin = origin;
  clue->polarity = 0;
  clue->proof = proof;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_implied_inequality(Tclue clue)
{
  Tclue clue2 = clue_new();
  assert(clue->type == CLUE_LITERAL &&
	 ((clue->polarity == 0 && DAG_symb(clue->DAG[0]) == PREDICATE_LEQ) ||
	  (clue->polarity == 1 && DAG_symb(clue->DAG[0]) == PREDICATE_LESS)));
  clue2->type = CLUE_IMPLIED_INEQUALITY;
  clue2->origin = 0;
  clue2->polarity = 0;
  clue2->proof.clue = clue;
  clue2->DAG[0] = DAG_dup(DAG_arg0(clue->DAG[0]));
  clue2->DAG[1] = DAG_dup(DAG_arg1(clue->DAG[0]));
  OUTPUT_CLUE(clue2);
  return clue2;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_model_equality(TDAG DAG1, TDAG DAG2, unsigned origin)
{
  Tclue clue = clue_new();
  TDAG DAG;
  clue->type = CLUE_MODEL_EQUALITY;
  clue->origin = origin;
  clue->polarity = 1;
  DAG = DAG_dup(DAG_eq(DAG1, DAG2));
  clue->proof.lit = DAG_to_lit(DAG);
  DAG_free(DAG);
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_abstract(TDAG DAG1, TDAG DAG2)
{
  Tclue clue = clue_new();
  clue->type = CLUE_ABSTRACT_TERM;
  clue->origin = 0;
  clue->polarity = 1;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  clue->proof.generic = NULL;
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_abstract_pred(TDAG DAG1, TDAG DAG2, unsigned polarity, TUproof proof)
{
  Tclue clue = clue_new();
  clue->type = CLUE_ABSTRACT_PRED;
  clue->origin = 0;
  clue->polarity = polarity;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  clue->proof = proof;
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_new_abstract_quant(TDAG DAG1, TDAG DAG2, unsigned polarity, TUproof proof)
{
  Tclue clue = clue_new();
  clue->type = CLUE_ABSTRACT_QUANT;
  clue->origin = 0;
  clue->polarity = polarity;
  clue->DAG[0] = DAG_dup(DAG1);
  clue->DAG[1] = DAG_dup(DAG2);
  clue->proof = proof;
  OUTPUT_CLUE(clue);
  return clue;
}

/*--------------------------------------------------------------*/

Tclue
clue_dup(Tclue clue)
{
  ++clue->gc_count;
  assert(clue->gc_count);
  return clue;
}

/*--------------------------------------------------------------*/

void
clue_free(Tclue clue)
{
  if (!clue)
    return;
  assert(clue->gc_count);
#ifdef DEBUG_CLUE
  if (clue->gc_count == 1)
    {
      my_message("clue_free %p:\n", clue);
      clue_fprint(stderr, clue);
      fprintf(stderr, "\n");
    }
#endif
  if (!--clue->gc_count)
    {
      DAG_free(clue->DAG[0]);
      if (clue->DAG[1]) DAG_free(clue->DAG[1]);
#ifdef DEBUG
      memset(clue, 0xff, sizeof(struct TSclue));
#endif
      free(clue);
    }
}

/*--------------------------------------------------------------*/

Tlit
clue_literal(Tclue clue)
{
  assert(clue->type == CLUE_LITERAL ||
	 clue->type == CLUE_MODEL_EQUALITY ||
	 clue->type == CLUE_IMPLIED_INEQUALITY);
  return clue->proof.lit;
}

/*--------------------------------------------------------------*/

TDAG
clue_DAG(Tclue clue)
{
  TDAG result = DAG_NULL;;
  switch (clue->type) {
  case CLUE_ABSTRACT_QUANT:
  case CLUE_ABSTRACT_PRED:
    result = clue->DAG[0];
    break;
  case CLUE_ABSTRACT_TERM:
    if (clue->DAG[0] != clue->DAG[1])
      result = DAG_eq(clue->DAG[0], clue->DAG[1]);
    else
      result = DAG_TRUE;
    break;
  case CLUE_MERGE:
    assert (clue->DAG[0] != clue->DAG[1]);
    result = DAG_eq(clue->DAG[0], clue->DAG[1]);
    break;
  default:
    my_message("internal error: clue_DAG.\n");  
  }
  if (!clue->polarity)
    result = DAG_not(result);
  return result;
}

/*--------------------------------------------------------------*/

unsigned
clue_DAG_size(Tclue clue)
{
  unsigned result;
  if (clue == NULL) return 0;
  result = 0;
  if (clue->DAG[0]) result += DAG_count_nodes(clue->DAG[0]);
  if (clue->DAG[1]) result += DAG_count_nodes(clue->DAG[1]);
  return result;
}
