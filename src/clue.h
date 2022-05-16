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
   \file clue.h
   \author David Deharbe, Pascal Fontaine

   \brief Clue module - Tclue is the data type for sharing information
  between CC and DPs in NO.

  The different kinds of clues are:
  
  - clue_literal

    -# Issued from literals from user space (SAT solver), for CC!
      These are (negated) equalities or (negated) predicates
      origin = DP_MAX
      polarity = 0 if negated, 1 otherwise
      proof.literal is the literal.
      DAG[1] is unused if it is a predicate.  Otherwise, it is a (in)equality
      and both DAG[0-1] are used
      DAGs are fully informative: whole terms matter

    other clues are generated from decision procedures, and are such that
    origin = original decision procedure

  - clue_merge
    informs equality of two "things"
    polarity = 1

    -# Issued within CC, when two terms are found equal (congruence)
      origin = 0
      proof = NULL
      DAGs are terms that should be merged. Both terms should be already 
      known by DP (as they were sent by clue_abstract).
      These should never live outside CC.

    -# Issued by CC to a DP to inform that two classes relevant for DP found equal
      origin = 0
      proof = NULL
      DAGs are not fully informative: they are just identifiers of classes.  
      Both terms should be already known by DP (as they were sent by 
      clue_abstract).

    -# Issued by DP to CC to inform that it found two classes equal
      origin = dp index
      proof is dependent on the DP
      DAGs are not fully informative: they are just identifiers of classes

  - clue_replace
    informs equality of two "things"
    polarity = 1

    -# Issued by CC to a DP to inform that class relevant for DP changed 
    representative
      origin = 0
      proof = NULL
      DAGs are not fully informative: they are just identifiers of
      classes It differs from case merge/2 by the fact that one id is
      unknown to DP
    
  - clue_abstract
    informs a DP of the presence of a relevant term
    only DAG[0] is used.

    only the top most symbol, class identifier for the term, and for
    all direct subterms matter:

    For instance : f(x) - f(y) is understood as
      C(f(x) - f(y)) = C(f(x)) - C(f(y))

    This is not a constraint, but a definition of C(f(x) - f(y)) and a
    notification that this term is relevant for future reasoning (if
    ever it is equal to something else)

    Proofs should be carefully handled when such an equality occurs
    for the proof: Indeed, the proof should include the proofs that
    f(x) - f(y) = C(f(x) - f(y)) (?), f(x) = C(f(x)) and f(y) = C(f(y))

  - clue_abstract_pred.  Constructor: clue_new_abstract_pred
    informs a DP of the presence of a relevant predicate
    only DAG[0] is used.
    only the top most symbol, polarity, and class identifier for all direct subterms
    matter:
    For instance :  NOT(f(x) <= f(y)) is understood as NOT(C(f(x)) <= C(f(y)))
    This is a constraint

    Proofs should be carefully handled when such a constraint occurs
    for the proof: Indeed, the proof should include: the original
    literal, NOT(f(x) <= f(y)), and the proofs that f(x) = C(f(x)) and
    the proofs that f(y) = C(f(y)).

  - clue_abstract_quant
    TODO: describe

  - clue_model_equality
    issued by DP to propagate equalities generated by models.  Behave
    like literal clues

  - clue_implied_inequality
    exactly like clue_literal: a hack within CC to handle < and NOT <=
    as !=

  Clues are freed by the DP/CC that receives it.

  All clues generated during conflict analysis are clues that were
  once sent to DP.

  Clues transferred by CC to DPs are

  - clue_abstract

  - clue_abstract_pred

  - clue_abstract_quant

  - clue_inequality

  - clue_merge

  - clue_replace

  The two last clues (coming from CC) do not matter for the conflict set.

  DP may generate the following clues

  - clue_merge

  - clue_model_equality

  CC also use the following clues for internal purposes

  - clue_new_implied_inequality: used as a hack (a < b introduces a != b)

  - clue_merge: used for congruences

  --------------------------------------------------------------
*/

#ifndef __CLUE_H
#define __CLUE_H

#include "DAG.h"
#include "literal.h"
#include "proof.h"
#include "stack.h"

/** The different forms of proof that can be produced by decision procedures */
union TUproof
{
  /** A single literal */
  Tlit      lit;
  /** A list of clues */  
  Tlist     arith;
  /** A single clue */  
  struct TSclue *clue;
  /** For any use */
  void     *generic;
};
typedef union TUproof TUproof;

/** The different forms of clues that circulate */
enum Tclue_type {
  /** Abstract type, never used */
  CLUE_NONE,
  /** Literal coming directly from the client */
  CLUE_LITERAL,
 /** A = B    assumed by a DP from a guessed model */  
  CLUE_MODEL_EQUALITY,
  /** A = B    deduced by any DP */  
  CLUE_MERGE,
  /** A != B   deduced by any DP */  
  CLUE_INEQUALITY,
  /** f(A)     where f relevant for dest DP */  
  CLUE_ABSTRACT_TERM,
  /** p(A) or NOT p(A) where p relevant for dest DP */  
  CLUE_ABSTRACT_PRED,
  /** TODO: specify */  
  CLUE_ABSTRACT_QUANT,
  /** Used internally by congruence closure */
  CLUE_CONGRUENT,
  CLUE_IMPLIED_INEQUALITY
};
/* The data type for forms of clue */
typedef enum Tclue_type Tclue_type;

/** clues are the bits of informations circulating between CC and the DPs */
struct TSclue
{
  TDAG      DAG[2];        /** if CLUE_ABSTRACT_PRED or CLUE_LITERAL (with a predicate) then only DAG[0] is used, otherwise the clue is an (in)equality and both positions are used */
#ifdef PEDANTIC
  Tclue_type type;
  unsigned  origin;      /** 0 if origin is CC, or index of DP that issued the clue if > 0 */
  unsigned  gc_count;   /** Counts the number of references to the clue */
  unsigned  polarity;    /** Flags the polarity (for abstract pred) */
  unsigned  misc;        /** DD+PF help bit for conflict clause production */
#else
  Tclue_type type:7;
  unsigned  origin:6;      /** 0 if origin is CC, or index of DP that issued the clue if > 0 */
  unsigned  gc_count:17;   /** Counts the number of references to the clue */
  unsigned  polarity:1;    /** Flags the polarity (for abstract pred) */
  unsigned  misc:1;        /** DD+PF help bit for conflict clause production */
#endif
  TUproof   proof;         /** DD+PF abstract pointer to structure saving proof information about the clue */
#ifdef PROOF
  Tproof_id proof_id;
#endif
};

typedef struct TSclue *Tclue;

TSstack(_clue, Tclue);

Tclue     clue_new_literal(Tlit lit);
Tclue     clue_new_merge(TDAG DAG1, TDAG DAG2, unsigned origin, TUproof proof);
Tclue     clue_new_model_equality(TDAG DAG1, TDAG DAG2, unsigned origin);
Tclue     clue_new_abstract(TDAG DAG, TDAG DAG2);
Tclue     clue_new_abstract_pred(TDAG DAG1, TDAG DAG2,
				 unsigned polarity, TUproof proof);
Tclue     clue_new_abstract_quant(TDAG DAG1, TDAG DAG2,
				  unsigned polarity, TUproof proof);
Tclue     clue_new_congruent(TDAG DAG1, TDAG DAG2);
Tclue     clue_new_inequality(TDAG DAG1, TDAG DAG2, unsigned origin,
			      TUproof proof);

Tclue     clue_dup(Tclue clue);
void      clue_free(Tclue clue);

Tlit      clue_literal(Tclue clue);
/**
   \brief returns a DAG that encodes the information stored in clue
   \param clue a clue
   \author David Deharbe
*/
TDAG      clue_DAG (Tclue clue);

/* PF this is a hack for not( <= ) and <, that imply != */
Tclue     clue_new_implied_inequality (Tclue clue);

unsigned clue_DAG_size (Tclue clue);

#ifdef DEBUG
#include "clue-print.h"
#endif

#endif /* __CLUE_H */
