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
  \file dl.h

  \author Diego Caminha

  \brief Interface to the difference logic decision procedure.

  Implementation of a difference logic decision procedure based on graphs.

*/

#ifndef __DL_H_
#define __DL_H_
#include <stdio.h>

#include "list.h"

#include "clue.h"
#include "number.h"
#include "veriT-status.h"

/**
   \brief initializes module.
   \param[in] id The identification of the decision procedure.
   \remarks Must be called before any other function of the module. */
void     dl_init(const unsigned id);
/* PF TODO is the above id used somewhere? */

/**
   \brief releases the module */
void     dl_done(void);

/**
   \brief restarts the module. */
void     dl_reset(void);

/**
   \brief adds a clue of the kind inequality.
   \pre \p clue is a disequality. */
/* PF TODO this should not be: only variables id should be exchanged */
void     dl_push_disequality(Tclue clue);

/**
  \brief informs the current problem contains integer variables.
  \remark If current problem contains integer variables,
  models can be generated for completeness of veriT.
  \remark This should be called if problem is mixed integer/real variables. */
/* TODO I do not understand this */
void     dl_set_idl(void);

/**
   \brief Informs the current problem contains only real variables. */
void     dl_set_rdl(void);

/**
   \brief adds a constraint of the kind x <= y + c.
   \param[in] x First variable of the constraint.
   \param[in] y Second variable of the constraint.
   \param[in] c The constant term of the constraint.
   \param[in] clue_list The list of clues that explains why x <= y + c.
   \return The status of satisfiability after the push. */
/* PF TODO here only variable id should go through,
   and constraints ids */
Tstatus  dl_push(TDAG x, TDAG y, Tnumber c, Tlist clue_list);

/**
   \brief removes last added constraint */
void     dl_pop(void);

/**
   \brief Runs the decision procedure to verify the satisfiability
   of the set of given clues.
   \return The status of satisfiability after the check.
   \remarks In the current implementation, the consistency check is done
   incrementally during the pushes, so this function returns
   the current status in constant time. */
Tstatus  dl_solve(void);

/**
   \brief Looks up for current the satisfiability of the set of given clues.
   \return The current status of satisfiability. */
Tstatus  dl_status(void);

/**
   \brief Constructs a list of clues that led to the conflict.
   \pre dl_status() yields UNSAT.
   \return The list of conflicting clues. */
Tlist    dl_conflict(void);

/**
   \brief Constructs a list of clues that deduced clue.
   \pre clue is an equality deduced by the decision procedure
   and returned by dl_eq_queue_pop()
   \return The list of clues that deduced clue. */
Tlist    dl_premisses(const Tclue clue);

/**
   \brief Fills table with lemmas created by the module.
   \pre dl_has_lemma() yields \e true.
   \param[in] table Returning table with the lemmas. */
void     dl_lemmas(Tstack_DAG * Plemmas);

/**
   \brief Verifies if the module has a lemma to produce.
   \return \e true if it has a lemma to return, \e false otherwise. */
bool     dl_has_lemma(void);

/**
   \brief Verifies if the module has an equality to return.
   \return \e true if it has not an equality to return, \e false otherwise. */
bool     dl_eq_queue_empty(void);

/**
  \brief Returns a equality deduced by the module.
  \pre dl_eq_queue_empty() yields \e false.
  \return An clue of the kind equality produced by the module.
  \remarks Each equality is returned only once. */
Tclue    dl_eq_queue_pop(void);

/**
  \brief Verifies if the module has an model equality to return.
  \return \e true if it has not an model equality to return, \e false otherwise.
  \remarks Model equalities can be generated after dl_solve() is called. */
bool     dl_model_eq_queue_empty(void);

/**
  \brief Returns a model equality deduced by the module.
  \pre dl_model_eq_queue_empty() yields \e false.
  \return An clue of the kind equality produced by the module.
  \remarks Each model equality is returned only once. */
Tclue    dl_model_eq_queue_pop(void);

/**
  \brief Prints some debugging information.
  \param[out] FILE Where the information will be printed. */
void     dl_print(FILE *);

#endif /* __DL_H_*/
