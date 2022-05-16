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
  Module for congruence closure
  --------------------------------------------------------------
*/

#ifndef __CONGRUENCE_H
#define __CONGRUENCE_H

/* PF Decision for (dis)equality and uninterpreted functions.
   Incrementally takes a set of literals.
   Computes if this set is satisfiable with respect to equality only.

   Quantified formulas and lambda terms are treated as constants:
   \forall x (x = a), \not \forall x (x = b), a = b is "satisfiable"
   boolean connectors and ite function are not interpreted here
   (p(a) and not p(b)), a = b is "satisfiable"
   So better only give atoms and quantified formulas */

#include <stdarg.h>

#include "DAG.h"
#include "hashmap.h"
#include "list.h"

#include "clue.h"
#include "config.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "veriT-status.h"

extern int * SAT_hints;
extern int SAT_hint_first;
extern int SAT_hint_last;

typedef enum Tboolean_value {FALSE = 0, TRUE = 1, UNDEFINED} Tboolean_value;

/* PF return status */
Tstatus   CC_status(void);

/* PF add clue in CC.
   Destructive for clue */
void      CC_push(Tclue clue);
/* PF like a push, but only watch the equality or predicate: do not
   assume it has a Boolean value set */
void      CC_watch(Tclue clue);

/* DD+PF get the lists of clues that lead to unsatisfiability
   Should only be called once after conflict detection
   Returned clues live as long as the conflict remains within CC
   (i.e. until backtracking occurs), and should not be freed outside CC */
#ifdef PROOF
Tlist     CC_conflict(Tproof_id * Pproof_id);
#else
Tlist     CC_conflict(void);
#endif
/* DD+PF get the lists of clues that entail the given clue
   Returned clues live as long as the deduction is valid within CC
   (i.e. until backtracking occurs), and should not be freed outside CC */
Tlist     CC_premisses(Tclue clue);
/* DD pushed on table lemmas that have been derived by congruence closure that may be helpful for DPLL solver */
void      CC_lemmas(Tstack_DAG * Plemmas);
/* DD indicates if CC has derived lemmas that may be helpful for DPLL solver */
bool      CC_has_lemma(void);

/* DD+PF buffers of clues for each DP.  Clues should be freed outside CC */
extern Tstack_clue  CC_buffer;
/* DD+PF mask of DPs having pending clues in buffer
   obs. this mask should be a subset of activated DPs */
extern unsigned  CC_clues;
/* DD+PF mask of DPs kept informed of new terms and equalities */
extern unsigned  CC_mask;
/* DD+PF mask of DPs kept informed of quantified formulas */
extern unsigned  CC_mask_quantified;

/* DD+PF abstraction function for NO.  If x and y are equal,
   then they are mapped to the same DAG
   Generated clues should be freed by the module providing the push function */
TDAG      CC_abstract(TDAG DAG);

void      CC_model(void (out) (char *format, ...));

void      CC_init(const unsigned id);
void      CC_done(void);

/**
   \brief returns all signatures for symbol
   \param symb a symbol
   \return the stack of signatures
   \remark if f(a) and f(b) exist, but a = b, then only one is returned */
Tstack_DAG CC_get_sig(Tsymb symb);

/**
   \brief returns all signatures congruent to DAG for symbol
   \param symb a symbol
   \return the stack of signatures
   \remark if f(a) and f(b) exist, but a = b, then only one is returned */
Tstack_DAG CC_get_sig_DAG(Tsymb symb, TDAG DAG);

/**
   \brief returns one element per class that has the sort given in argument
   \param sort the sort
   \return the stack of class representatives */
Tstack_DAG CC_get_sort_classes(Tsort sort);

#endif /* __CONGRUENCE_H */
