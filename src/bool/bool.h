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
  Propositional Abstraction Module
  --------------------------------------------------------------
*/

#ifndef __BOOL_H
#define __BOOL_H

#include "config.h"

#include "stack.h"

#define INSIDE_VERIT
#include "veriT-SAT.h"
#include "DAG.h"
#include "literal.h"
#include "veriT-status.h"

#ifdef PROOF
#include "proof_id.h"
#endif

struct TSclause
{
  unsigned nb_lits;
  unsigned nb_pos_lits;
  Tlit    *lits;
#ifdef PROOF
  Tproof_id proof_id;
#endif
};
typedef struct TSclause * Tclause;
TSstack(_clause, Tclause);

/* DD+PF creates a new clause, with place for nb_lits */
Tclause   clause_new(unsigned nb_lits);
/* PF creates a copy of clause */
Tclause   clause_dup(Tclause clause);
/* DD+PF set the i-th literal to argument */
void      clause_set_literal(Tclause clause, unsigned i, Tlit lit);
/* DD+PF allocate place for one supplementary literals, set it to arg */
void      clause_add_literal(Tclause clause, Tlit lit);
/* EB+PF creates a (cleaned) clause with all lits from the arguments */

/**
   \author Ezequiel Bazan and Pascal Fontaine
   creates a (cleaned) clause with all lits from the arguments
   \param clause1 first clause
   \param clause2 second clause
   \return the merged clause (clause1 OR clause2)
   \remarks Non destructive
   \remarks NULL list is represents TRUE
   \remarks A singleton with an empty clause represents FALSE
*/
Tclause   clause_merge(Tclause clause1, Tclause clause2);
/* PF removes repeated literals and sort; if valid returns NULL */
Tclause   clause_clean(Tclause clause);
/* PF tests if clauses are the same */
bool      clause_same(Tclause clause1, Tclause clause2);
/* DD+PF print clause in file */
void      clause_fprint(FILE * file, Tclause clause);
void      clause_free(Tclause clause);

/** \brief stores (FIFO) the set of literals in the (partial) model */
#define bool_model_Q SAT_literal_stack
/** \brief number of literals in the previous model  */
extern unsigned bool_model_size_old;
/** \brief number of literals in the model */
#define bool_model_size SAT_literal_stack_n
/** \brief number of literals that are the same compared to the
     previous model */
#define bool_model_same SAT_literal_stack_hold
/** \brief number of literals at the beginning of the queue that will
    remain in every (partial) model */
#define bool_model_constant SAT_literal_stack_unit 
/** \brief 1 if the model is total, 0 otherwise */
extern unsigned bool_model_complete;

/**
   \author Pascal Fontaine
   \brief Tune the decision heuristics according to the formula */
void    bool_prepare(void);

/**
   \author David Déharbe and Pascal Fontaine
   \brief Check the set of formulas for a partial model
   \param level stop at decision level (0 if do not stop at level)  
   \param max_dec stop after max_dec decisions
   \return UNSAT, SAT, UNDEF
   \remark updates bool_model_Q, bool_model_size, bool_model_size_old, bool_model_same, bool_model_constant, bool_model_complete
*/
Tstatus  bool_SAT_to_level(unsigned level, int max_dec);

/**
   \author David Déharbe and Pascal Fontaine
   \brief Check the set of formulas for a total model
   \return UNSAT, SAT
   \remark updates bool_model_Q, bool_model_size, bool_model_size_old, bool_model_same, bool_model_constant, bool_model_complete
*/
int      bool_SAT(void);

/**
   \brief stack of literal hints from the SMT reasoner
   \remark this should be allocated, updated, freed in the SMT reasoner
*/
extern  Tlit    *bool_hint;
/**
   \brief index of the first hint
   \remark this may be updated by the SAT solver to assess that literals
   have been taken into consideration */
extern  unsigned bool_hint_first;
/**
   \brief index of the last hint */
extern  unsigned bool_hint_last;

extern void bool_hint_add(Tlit lit);

/**
   \author David Déharbe and Pascal Fontaine
   \brief Add formula to the set of formulas to check for satisfiability
   \param formula the formula to add */
void     bool_add(TDAG formula OPTC_PROOF(Tproof_id proof_clause));
/**
   \author David Déharbe and Pascal Fontaine
   \brief Add clause to the set of formulas to check for satisfiability
   \param clause the clause to add */
void     bool_add_c(Tclause clause);
/**
   \author David Déharbe and Pascal Fontaine
   \brief Add clause as conflict clause to the set of formulas to
   check for satisfiability
   \param clause the clause to add
   \remark the SAT solver may use the fact that clause is conflict clause */
void     bool_add_c_conflict(Tclause clause);

/**
   \author Pascal Fontaine
   \brief output cnf DIMACS of the abstraction of the formula
   \param status status of the set of formulas and clauses
   \param formulas table of formulas in the abstraction
   \param clauses table of clauses to add to the DIMACS file
   \remark use only at the end of normal work
   \remark it resets cnf module */
void     bool_recheck(char * filename, Tstatus status,
		      Tstack_DAG formulas, Tstack_clause clauses);

void     bool_reset(void);

void     bool_init(void);
void     bool_done(void);

/**
   \author Pascal Fontaine
   \brief get the decision level of literal */
unsigned bool_get_declev(Tlit lit);

/**
   \author Pascal Fontaine
   \brief get the current decision level */
unsigned bool_get_current_declev(void);

/** 
 \author Pascal Fontaine
 \brief Computes statistics on the module data
 */
void bool_stats_model(void);

#endif /* __BOOL_H */
