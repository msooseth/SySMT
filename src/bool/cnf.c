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
  Conjunctive normal form
  --------------------------------------------------------------
*/

#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "config.h"
#include "general.h"
#include "list.h"
#include "options.h"
#include "statistics.h"

#include "bool.h"
#include "literal.h"
#include "DAG-print.h"
#include "DAG.h"
#include "cnf.h"
#include "proof.h"

/* #define DEBUG_CNF */
/* #define STATS_CNF */

/* PF clauses are added to the following list
   This is set to null before converting a formula. */
static Tstack_clause *PclausesL;

#ifdef PROOF
#define clause_push_proof(a, b) { a->proof_id = b; stack_push(*PclausesL, a); }
#else
#define clause_push_proof(a, b) stack_push(*PclausesL, a)
#endif

/* PF module option: 1 iff definitional normal (vs. p-definitional) form is used, 0 otherwise */
static bool cnf_definitional = false;

#ifdef STATS_CNF
/* PF module option: 1 iff cnf stats are output */
static bool cnf_stats;
#endif

#if STATS_LEVEL > 1
static unsigned stat_n_binary = 0;
static unsigned stat_n_naive = 0;
static unsigned stat_n_pdef = 0;
#endif

/*--------------------------------------------------------------*/

typedef unsigned char Tpolarity; 

#define POLARITY_NONE ((Tpolarity)0u)
#define POLARITY_POS  ((Tpolarity)1u)
#define POLARITY_NEG  ((Tpolarity)2u)
#define POLARITY_BOTH ((Tpolarity)3u)

#define inverse_polarities(x)						\
  ((Tpolarity)								\
   ((x == POLARITY_BOTH)?POLARITY_BOTH:					\
    ((x == POLARITY_NEG)?POLARITY_POS:					\
     ((x == POLARITY_POS)?POLARITY_NEG:POLARITY_NONE))))

/* PF records the number of literals that have a recorded polarity */
unsigned nb_polarities = 0;
/* PF for every literal, allocates an int to remember which polarities
   have already been produced */
Tpolarity * polarities = NULL;

/*--------------------------------------------------------------*/

/* PF associate a literal with a DAG
   wrapper to add polarities */
static Tlit
cnf_DAG_to_literal(TDAG DAG)
{
  Tlit lit = DAG_to_lit(DAG);
  while (lit_var(lit) >= nb_polarities)
    {
      unsigned i;
      MY_REALLOC(polarities, 2 * nb_polarities * sizeof(Tpolarity));
      for (i = nb_polarities, nb_polarities *= 2; i < nb_polarities; i++)
	polarities[i] = POLARITY_NONE;
    }
  return lit;
}

/*--------------------------------------------------------------*/

static void
cnf_literal_add_polarities(Tlit lit, Tpolarity pols)
{
  polarities[lit_var(lit)] |= lit_pol(lit)?pols:inverse_polarities(pols);
}

/*--------------------------------------------------------------*/

static Tpolarity
cnf_literal_polarities(Tlit lit)
{
  if (lit_pol(lit))
    return polarities[lit_var(lit)];
  return inverse_polarities(polarities[lit_var(lit)]);
}

/*--------------------------------------------------------------*/

/* PF adds clauses C to database, and returns literal such that
   literal correponds to DAG
   if pols is either
     POLARITY_POS if DAG is only used positively
     POLARITY_NEG if DAG is only used negatively
     POLARITY_BOTH if DAG is used with both polarities */
static Tlit
var_cnf(TDAG DAG, Tpolarity polarities)
{
  Tlit lit;
  Tpolarity missing_polarities = polarities;
  assert(polarities);
#ifdef DEBUG_CNF
  fprintf(stderr, "var_cnf (pol %d) : ", polarities);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    return lit_neg(var_cnf(DAG_arg0(DAG), inverse_polarities(polarities)));
  lit = cnf_DAG_to_literal(DAG);
  missing_polarities = polarities & (~cnf_literal_polarities(lit));
  if (!missing_polarities)
    return lit;
  cnf_literal_add_polarities(lit, missing_polarities);

  if (DAG_symb(DAG) == BOOLEAN_TRUE)
    {
      Tclause clause = clause_new(1);
      clause->lits[0] = lit;
      clause_push_proof(clause, proof_true());
      cnf_literal_add_polarities(lit, POLARITY_BOTH);
    }
  else if (DAG_symb(DAG) == BOOLEAN_FALSE)
    {
      Tclause clause = clause_new(1);
      clause->lits[0] = lit_neg(lit);
      clause_push_proof(clause, proof_false());
      cnf_literal_add_polarities(lit, POLARITY_BOTH);
    }
  else if (!boolean_connector(DAG_symb(DAG)))
    {
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND)
    {
      unsigned i;
      Tclause clause;
      if (missing_polarities & POLARITY_POS)
	{
	  for (i = 0; i < DAG_arity(DAG); i++)
	    {
	      clause = clause_new(2);
	      clause->lits[0] = var_cnf(DAG_arg(DAG, i), missing_polarities);
	      clause->lits[1] = lit_neg(lit);
	      clause_push_proof(clause, proof_and_pos(DAG, i));
	    }
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  clause = clause_new(DAG_arity(DAG) + 1);
	  for (i = 0; i < DAG_arity(DAG); i++)
	    clause->lits[i] =
	      lit_neg(var_cnf(DAG_arg(DAG, i), missing_polarities));
	  clause->lits[i] = lit;
	  clause_push_proof(clause, proof_and_neg(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR)
    {
      unsigned i;
      Tclause clause;
      if (missing_polarities & POLARITY_POS)
	{
	  clause = clause_new(DAG_arity(DAG) + 1);
	  for (i = 0; i < DAG_arity(DAG); i++)
	    clause->lits[i] = var_cnf(DAG_arg(DAG, i), missing_polarities);
	  clause->lits[i] = lit_neg(lit);
	  clause_push_proof(clause, proof_or_pos(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  for (i = 0; i < DAG_arity(DAG); i++)
	    {
	      clause = clause_new(2);
	      clause->lits[0] = lit_neg(var_cnf(DAG_arg(DAG, i),
						missing_polarities));
	      clause->lits[1] = lit;
	      clause_push_proof(clause, proof_or_neg(DAG, i));
	    }
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_XOR)
    {
      /* PF we can safely assume arity = 2.
	 Otherwise rewritten as preprocessing */
      assert(DAG_arity(DAG) == 2);
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_xor_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_xor_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_xor_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_xor_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] =
	    lit_neg(var_cnf(DAG_arg0(DAG),
			    inverse_polarities(missing_polarities)));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_implies_pos(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_POS);
	  clause->lits[1] = lit;
	  clause_push_proof(clause, proof_implies_neg1(DAG));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_NEG));
	  clause->lits[1] = lit;
	  clause_push_proof(clause, proof_implies_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_EQUIV)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_equiv_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_equiv_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_equiv_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_equiv_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = var_cnf(DAG_arg(DAG, 2), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_ite_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_ite_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg(DAG, 2), missing_polarities));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_ite_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), missing_polarities));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_ite_neg2(DAG));
	}
    }
#ifdef DEBUG_CNF
  fprintf(stderr, "var_cnf %d for formula : ", lit);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  return lit;
}

/*--------------------------------------------------------------*/

/* PF adds clauses C to database, such that
   (C sat) iff (DAG sat) if pol == POLARITY_POS
   (C sat) iff (not DAG sat) if pol == POLARITY_NEG
   If def is 0, normal form is p-definitional.
   Definitional otherwise */
static void
silent_cnf(TDAG DAG, Tpolarity pol, int def OPTC_PROOF(Tproof_id proof_clause))
{
  Tclause clause;
  assert(polarities);
  assert(pol == POLARITY_POS || pol == POLARITY_NEG);
#ifdef DEBUG_CNF
  fprintf(stderr, "silent_cnf (pol %d, def %d)\n", pol, def);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  if (!boolean_connector(DAG_symb(DAG)))
    {
      clause = clause_new(1);
      if (pol == POLARITY_POS)
	clause->lits[0] = var_cnf(DAG, def ? POLARITY_BOTH : pol);
      else
	clause->lits[0] = lit_neg(var_cnf(DAG, def ? POLARITY_BOTH : pol));
      clause_push_proof(clause, proof_clause);
    }
  else if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      if (pol == POLARITY_POS)
	silent_cnf(DAG_arg0(DAG), POLARITY_NEG, def OPTC_PROOF(proof_clause));
      else
	silent_cnf(DAG_arg0(DAG), POLARITY_POS, def OPTC_PROOF(proof_clause));
#if 0
	silent_cnf(DAG_arg0(DAG), POLARITY_POS, def
		   OPTC_PROOF(proof_not_not(proof_clause)));
#endif
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND && pol == POLARITY_POS)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	silent_cnf(DAG_arg(DAG, i), POLARITY_POS, def
		   OPTC_PROOF(proof_and(proof_clause, i)));
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR && pol == POLARITY_NEG)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	silent_cnf(DAG_arg(DAG, i), POLARITY_NEG, def
		   OPTC_PROOF(proof_not_or(proof_clause, i)));
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND && pol == POLARITY_NEG)
    {
      unsigned i;
      clause = clause_new(DAG_arity(DAG));
      for (i = 0; i < DAG_arity(DAG); i++)
	clause->lits[i] = lit_neg(var_cnf(DAG_arg(DAG, i),
					  def ? POLARITY_BOTH : pol));
      clause_push_proof(clause, proof_not_and(proof_clause));
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR && (pol == POLARITY_POS))
    {
      unsigned i;
      clause = clause_new(DAG_arity(DAG));
      for (i = 0; i < DAG_arity(DAG); i++)
	clause->lits[i] = var_cnf(DAG_arg(DAG, i), def ? POLARITY_BOTH : pol);
      clause_push_proof(clause, proof_or(proof_clause));
    }
  else if (DAG_symb(DAG) == CONNECTOR_XOR)
    {
      /* PF we can safely assume arity = 2.
	 Otherwise rewritten as preprocessing */
      assert(DAG_arity(DAG) == 2);
      if (pol == POLARITY_POS)
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_xor1(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_xor2(proof_clause));
	}
      else
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_not_xor2(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_not_xor1(proof_clause));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      if (pol == POLARITY_POS)
	{
	  clause = clause_new(2);
	  clause->lits[0] =
	    lit_neg(var_cnf(DAG_arg0(DAG), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause->lits[1] =
	    var_cnf(DAG_arg1(DAG), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_implies(proof_clause));
	}
      else
	{
	  silent_cnf(DAG_arg0(DAG), POLARITY_POS, def
		     OPTC_PROOF(proof_not_implies1(proof_clause)));
	  silent_cnf(DAG_arg1(DAG), POLARITY_NEG, def
		     OPTC_PROOF(proof_not_implies2(proof_clause)));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_EQUIV)
    {
      clause = clause_new(2);
      if (pol == POLARITY_POS)
	{
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_equiv1(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_equiv2(proof_clause));
	}
      else
	{
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = var_cnf(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_not_equiv1(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(var_cnf(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_not_equiv2(proof_clause));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      clause = clause_new(2);
      if (pol == POLARITY_POS)
	{
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] =
	    var_cnf(DAG_arg(DAG, 2), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_ite1(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] =
	    var_cnf(DAG_arg1(DAG), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_ite2(proof_clause));
	}
      else
	{
	  clause->lits[0] = var_cnf(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] =
	    lit_neg(var_cnf(DAG_arg(DAG, 2), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause_push_proof(clause, proof_not_ite1(proof_clause));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(var_cnf(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] =
	    lit_neg(var_cnf(DAG_arg1(DAG), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause_push_proof(clause, proof_not_ite2(proof_clause));
	}
    }
}

/*--------------------------------------------------------------*/

#ifdef STATS_CNF
/* PF print some statistics about CNF */
static void
statistics(FILE * file)
{
  unsigned i, j;
  unsigned nb_clauses = stack_size(*PclausesL);
  unsigned nb_lits = 0;
  unsigned pure = 0, unit = 0;
  unsigned *pos, *neg;
  assert(polarities);
  MY_MALLOC(pos, var_max * sizeof(unsigned));
  MY_MALLOC(neg, var_max * sizeof(unsigned));
  /* PF caution: keep those lines, even if duplicate in SAFE_MALLOC mode */
  memset(pos, 0, var_max * sizeof(unsigned));
  memset(neg, 0, var_max * sizeof(unsigned));
  for (i = 0; i < nb_clauses; i++)
    {
      Tclause clause = (Tclause) stack_get(*PclausesL, i);
      if (clause->nb_lits == 1)
	unit++;
      for (j = 0; j < clause->nb_lits; j++)
	if (lit_pol(clause->lits[j]))
	  pos[lit_var(clause->lits[j])]++;
	else
	  neg[lit_var(clause->lits[j])]++;
      nb_lits += clause->nb_lits;
    }
  for (i = 1; i < var_max; i++)
    if (!pos[i] || !neg[i])
      pure++;

  fprintf(file, "Number of variables : %d\n", var_max - 1);
  fprintf(file, "Number of clauses   : %u\n", nb_clauses);
  fprintf(file, "Number of literals  : %u\n", nb_lits);
  fprintf(file, "Aver. nb lit / cl   : %f\n", 1.0 * nb_lits / nb_clauses);
  fprintf(file, "Pure literals       : %u\n", pure);
  fprintf(file, "Unit clauses        : %u\n", unit);

  for (i = 1; i < var_max; i++)
    if (DAG_literal(var_to_DAG(i)))
      fprintf(file, "+Var %4u, pos %5u, neg %5u\n", i, pos[i], neg[i]);
    else
      fprintf(file, " Var %4u, pos %5u, neg %5u\n", i, pos[i], neg[i]);

  free(pos);
  free(neg);
}
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG_CNF
static void
clause_symbolic_fprint(FILE * file, Tclause clause)
{
  int i, prop_literal;
  assert(polarities);
  if (!clause)
    fprintf(file, "NULL clause");
  else if (clause->nb_lits == 0)
    fprintf(file, "Empty clause");
  else
    for (i = 0; i < clause->nb_lits; i++)
      {
	prop_literal = clause->lits[i];
	if (DAG_literal(var_to_DAG(lit_var(prop_literal))))
	  {
	    fprintf(file, lit_pol(prop_literal)? " ": " (not ");
	    DAG_fprint(file, var_to_DAG(lit_var(prop_literal)));
	    fprintf(file, lit_pol(prop_literal)? "" : ") ");
	  }
	else
	  fprintf(file, " %d", clause->lits[i]);
      }
  fprintf(file, "\n");
}
#endif

/*
  --------------------------------------------------------------
  Counting functions
  --------------------------------------------------------------
*/

#if STATS_LEVEL > 1
static int
cnf_binary_count(Tstack_clause clauses)
{
  unsigned i;
  int counter = 0;
  for (i = 0; i < stack_size(clauses); ++i)
    {
      Tclause clause = stack_get(clauses, i);
      if (clause->nb_lits == 2)
	counter++;
    }
  return counter;
}
#endif

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
cnf(TDAG DAG, Tstack_clause * Pclauses OPTC_PROOF(Tproof_id proof_clause))
{
#if STATS_LEVEL > 1
  int cnf_pdef_n;
  int cnf_binary_n;
#endif
#ifdef DEBUG_CNF
  Tlist list;
  unsigned i;
#endif
  assert(polarities);
  PclausesL = Pclauses;
  silent_cnf(DAG, 1, cnf_definitional ? 1 : 0 OPTC_PROOF(proof_clause));

#if STATS_LEVEL > 1
  cnf_pdef_n = stack_size(*Pclauses);
  cnf_binary_n = cnf_binary_count(*Pclauses);
  stats_counter_set(stat_n_pdef, cnf_pdef_n);
  stats_counter_set(stat_n_binary, cnf_binary_n);
#endif

#ifdef DEBUG_CNF
  fprintf(stderr, "CNF RESULT : \n");
  for (i = 0; i < stack_size; ++i)
    clause_symbolic_fprint(stderr, stack_get(*Pclauses, i));
  fprintf(stderr, "END OF CNF\n");
#endif
#ifdef STATS_CNF
  if (cnf_stats)
    statistics(stderr);
#endif
}

/*--------------------------------------------------------------*/

void
cnf_init(void)
{
  assert(!polarities);
  cnf_definitional = false;
  options_new(0, "cnf-definitional",
	      "Conjunctive normal form: "
	      "Use definitional normal form (instead of p-definitional)",
	      &cnf_definitional);
#if STATS_LEVEL > 1
  stat_n_binary =
    stats_counter_new("2cl", "Number of binary clauses in original problem", "%6d");
  stat_n_pdef =
    stats_counter_new("cnf_pdef", "Number of clauses in p-definitional CNF", "%6d");
#endif
#ifdef STATS_CNF
  cnf_stats = false;
  options_new(0, "cnf-stats",
	      "Conjunctive normal form:" " Print statistics", &cnf_stats);
#endif
  nb_polarities = 1;
  MY_MALLOC(polarities, nb_polarities * sizeof(Tpolarity));
}

/*--------------------------------------------------------------*/

void
cnf_done(void)
{
  assert(polarities);
  free(polarities);
  polarities = NULL;
  nb_polarities = 0;
}

/*--------------------------------------------------------------*/

void
cnf_reset(void)
{
  assert(polarities);
  memset(polarities, POLARITY_NONE, nb_polarities * sizeof(Tpolarity));
}
