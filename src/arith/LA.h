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

#ifndef LA_H
#define LA_H

#include "literal.h"

/**
   \brief initializes the module
   \param[in] id The identification of the module
   \remarks must be called before any other function of the module */
void     LA_init(const unsigned id);

/**
   \brief releases the module */
void     LA_done(void);

/**
   \brief notifies the module that atoms from this DAG may be asserted
   positively or negatively, and equalities between arithmetic-relevant
   terms are to be given
   \param DAG a formula */
void     LA_notify_formula(TDAG DAG);

/**
   \brief asserts a literal
   \param lit a literal */
Tstatus  LA_assert(Tlit lit);

/**
   \brief asserts an equality between two terms
   \param DAG1 a term
   \param DAG2 a term
   \param tag a tag for conflict generation */
Tstatus  LA_assert_eq(TDAG DAG1, TDAG DAG2, unsigned tag);

/**
   \brief check satisfiability of the set of given clues
   \return status of satisfiability after the check */
Tstatus  LA_solve(void);


#ifdef PROOF
/**
   \brief Constructs the list of clues that led to a conflict
   \pre LA_status() yields UNSAT
   \param[out] proof_id The proof of the conflict set
   \return A list of conflicting clues */
Tlist    LA_conflict(Tproof_id * proof_id);
#else
/**
   \brief Returns the set of lits that led to the conflict
   \pre LA_status() yields UNSAT
   \return The stack of conflicting literals */
Tstack_lit LA_conflict(void);
#endif

#if 0

void   LA_flush(void);


/**
   \brief Constructs a list of clues that deduced \p clue.
   \pre clue is an equality deduced by LA and returned by LA_eq_queue_pop()
   \return The list of clues that deduced clue */
Tlist    LA_premisses(const Tclue clue);

/**
   \brief Fills table with lemmas created by the module
   \pre LA_has_lemma() yields \e true
   \param[out] table Returning table with the lemmas */
void     LA_lemmas(Ttable table);

/**
   \brief Verifies if the module has a lemma to produce.
   \return \e true if it has a lemma to return, \e false otherwise. */
bool     LA_has_lemma(void);

/**
   \brief Verifies if the module has an equality to return.
   \return \e true if it has not an equality to return, \e false otherwise. */
bool     LA_eq_queue_empty(void);

/**
   \brief Returns a equality deduced by the module
   \pre LA_eq_queue_empty() yields \e false
   \return An clue of the kind equality produced by the module
   \remarks Each equality is returned only once */
Tclue    LA_eq_queue_pop(void);

/**
   \brief Verifies if the module has an model equality to return
   \return \e true if it has not an model equality to return
   \e false otherwise */
bool     LA_model_eq_queue_empty(void);

/**
   \brief Returns a model equality deduced by the module
   \pre LA_model_eq_queue_empty() yields \e false
   \return An clue of the kind equality produced by the module
   \remarks Each model equality is returned only once */
Tclue    LA_model_eq_queue_pop(void);
#endif

#endif
