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
  \file arith.h

  \author Diego Caminha

  \brief Interface to the arithmetic module.

  This module provides the interface that can be used to have access
  to the arithmetic decision procedures. Currently there are two decision
  procedures: difference logic and linear arithmetic.

  The choice of which decision procedure is accessed is automatically
  determined by the kind of the formula been processed.

  'Arith' is a module seen by veriT as a single decision procedure.

*/

#ifndef __ARITH_H_
#define __ARITH_H_
#include <stdio.h>

#include "config.h"
#include "list.h"
#include "number.h"

#include "clue.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "veriT-status.h"

/**
   \brief initializes the module
   \param[in] id The identification of the module
   \remarks must be called before any other function of the module */
void     arith_init(const unsigned id);

/**
  \brief releases the module.
  \remarks Frees all the memory allocated by module functions. */
void     arith_done(void);

/**
  \brief Adds a clue. */
void     arith_push(Tclue clue);

/**
  \brief Runs the arithmetic solver to verify the satisfiability of the set of given clues.
  \return The status of satisfiability after the check. */
Tstatus  arith_solve(void);

/**
  \brief Looks up for current the satisfiability of the set of given clues.
  \return The current status of satisfiability. */
Tstatus  arith_status(void);

#ifdef PROOF
/**
   \brief Constructs the list of clues that led to a conflict.
   \pre arith_status() yields UNSAT.
   \param[out] proof_id The proof of the conflict set.
   \return A list of conflicting clues. */
Tlist    arith_conflict(Tproof_id * proof_id);
#else
/**
   \brief Constructs a list of clues that led to the conflict.
   \pre arith_status() yields UNSAT.
   \return The list of conflicting clues. */
Tlist    arith_conflict(void);
#endif

/**
   \brief Constructs a list of clues that deduced \p clue.
   \pre clue is an equality deduced by arith and returned by arith_eq_queue_pop().
   \return The list of clues that deduced clue. */
Tlist    arith_premisses(const Tclue clue);

/**
   \brief Fills table with lemmas created by the module.
   \pre arith_has_lemma() yields \e true.
   \param[out] Plemmas storing lemmas in referenced table. */
void     arith_lemmas(Tstack_DAG * Plemmas);

/**
   \brief Verifies if the module has a lemma to produce.
   \return \e true if it has a lemma to return, \e false otherwise. */
bool     arith_has_lemma(void);

/**
  \brief Verifies if the module has an equality to return.
  \return \e true if it has not an equality to return, \e false otherwise. */
bool     arith_eq_queue_empty(void);

/**
  \brief Returns a equality deduced by the module.
  \pre arith_eq_queue_empty() yields \e false.
  \return An clue of the kind equality produced by the module.
  \remarks Each equality is returned only once. */
Tclue    arith_eq_queue_pop(void);

/**
  \brief Verifies if the module has an model equality to return.
  \return \e true if it has not an model equality to return,
  \e false otherwise. */
bool     arith_model_eq_queue_empty(void);

/**
  \brief Returns a model equality deduced by the module.
  \pre arith_model_eq_queue_empty() yields \e false.
  \return An clue of the kind equality produced by the module.
  \remarks Each model equality is returned only once. */
Tclue    arith_model_eq_queue_pop(void);

/**
  \brief Prints some debugging information.
  \param[out] FILE Where the information will be printed. */
void     arith_print(FILE *);

#endif /* __ARITH_H_*/
