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
  Clause Module
  --------------------------------------------------------------
*/

#include "config.h"

#include "general.h"

#include "bool.h"

Tclause
clause_new(unsigned nb_lits)
{
  Tclause clause;
  MY_MALLOC (clause, sizeof (struct TSclause));
  clause->nb_lits = nb_lits;
  clause->nb_pos_lits = 0;
#ifdef PROOF
  clause->proof_id = 0;
#endif
  MY_MALLOC (clause->lits, nb_lits * sizeof (int));
  return clause;
}

/*--------------------------------------------------------------*/

Tclause
clause_dup(Tclause clause)
{
  unsigned i;
  Tclause clause2;
  MY_MALLOC (clause2, sizeof (struct TSclause));
  clause2->nb_lits = clause->nb_lits;
  clause2->nb_pos_lits = 0;
#ifdef PROOF
  clause2->proof_id = clause->proof_id;
#endif
  MY_MALLOC (clause2->lits, clause->nb_lits * sizeof (int));
  for (i = 0; i < clause->nb_lits; i++)
    clause2->lits[i] = clause->lits[i];
  return clause2;
}

/*--------------------------------------------------------------*/

void
clause_set_literal(Tclause clause, unsigned i, Tlit lit)
{
  assert (i < clause->nb_lits);
  clause->lits[i] = lit;
}

/*--------------------------------------------------------------*/

void
clause_add_literal(Tclause clause, Tlit lit)
{
  MY_REALLOC (clause->lits, (clause->nb_lits + 1) * sizeof (int));
  clause->lits[clause->nb_lits++] = lit;
}

/*--------------------------------------------------------------*/

static int compar_literal(const Tlit * lit1, const Tlit * lit2)
{
  return (int) lit_var(*lit1) - (int) lit_var(*lit2);
}

/*--------------------------------------------------------------*/

Tclause
clause_clean(Tclause clause)
     /* PF removes repeated literals
        if valid returns NULL
	The problem is linear (see veriT-sat), but implementation is n ln n */
{
  unsigned i;
  unsigned j;
  /* PF Empty clause */
  if (!clause->nb_lits)
    return clause;
  qsort(clause->lits, clause->nb_lits, sizeof(Tlit), (TFcmp) compar_literal);
  for (i = 0; i < clause->nb_lits - 1; i++)
    if (lit_neg(clause->lits[i]) == clause->lits[i + 1])
      {
	/* PF Valid clause */
	clause_free(clause);
	return NULL;
      }
  for (i = 1, j = 0; i < clause->nb_lits; i++)
    if (clause->lits[i] != clause->lits[j])
      clause->lits[++j] = clause->lits[i];
  clause->nb_lits = j + 1;
  MY_REALLOC(clause->lits, clause->nb_lits * sizeof(int));
  return clause;
}

/*--------------------------------------------------------------*/

Tclause
clause_merge (Tclause clause1, Tclause clause2)
/* PF builds a new clause that is the disjunction of both input
   The problem is linear (see veriT-sat) */
{
  int tmp;
  unsigned i1 = 0, i2 = 0, i = 0;
  Tclause clause;

  if (!clause1 || !clause2)
    return NULL;

  clause = clause_new (clause1->nb_lits + clause2->nb_lits);
  while (i1 < clause1->nb_lits && i2 < clause2->nb_lits)
    {
      tmp = compar_literal(&(clause1->lits[i1]), &(clause2->lits[i2]));
      if (tmp < 0)
	clause->lits[i++] = clause1->lits[i1++];
      else if (tmp > 0)
	clause->lits[i++] = clause2->lits[i2++];
      else
	{
	  if (clause1->lits[i1] != clause2->lits[i2])
	    {
	      /* PF Valid clause */
	      clause_free(clause);
	      return NULL;
	    }
	  clause->lits[i++] = clause1->lits[i1];
	  i1++;
	  i2++;
	}
    }
  while (i1 < clause1->nb_lits)
    clause->lits[i++] = clause1->lits[i1++];
  while (i2 < clause2->nb_lits)
    clause->lits[i++] = clause2->lits[i2++];
  clause->nb_lits = i;
  MY_REALLOC(clause->lits, clause->nb_lits * sizeof(int));
  return clause;
}

/*--------------------------------------------------------------*/

bool
clause_same(Tclause clause1, Tclause clause2)
{
  unsigned i;
  if (clause1->nb_lits != clause2->nb_lits)
    return false;
  for (i = 0; i < clause1->nb_lits; i++)
    if (clause1->lits[i] != clause2->lits[i])
      return false;
  return true;
}

/*--------------------------------------------------------------*/

void
clause_free(Tclause clause)
{
  if (!clause)
    return;
  free (clause->lits);
  free (clause);
}

/*--------------------------------------------------------------*/

void
clause_fprint(FILE * file, Tclause clause)
{
  unsigned i;
  if (!clause)
    fprintf (file, "NULL clause");
  else if (clause->nb_lits == 0)
    fprintf (file, "Empty clause");
  else
    for (i = 0; i < clause->nb_lits; i++)
      fprintf (file, " %d", clause->lits[i]);
  fprintf (file, "\n");
}
