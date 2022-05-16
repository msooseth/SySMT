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

#ifndef SAT_H
#define SAT_H

typedef unsigned SAT_Tvar;    /**< var index into stack_var */
typedef unsigned SAT_Tlit;    /**< lit is var<<1 or var<<+1 according to polarity */ 
typedef unsigned SAT_Tclause; /**< clause index into stack_clause */ 
typedef unsigned SAT_Tlevel;  /**< level type */ 

typedef enum {
  SAT_STATUS_UNSAT = 0,
  SAT_STATUS_SAT = 1,
  SAT_STATUS_UNDEF = 2
} SAT_Tstatus;

#define SAT_VAL_FALSE 0
#define SAT_VAL_TRUE 1
#define SAT_VAL_UNDEF 2

#define SAT_VAR_UNDEF 0
#define SAT_LIT_UNDEF 0
#define SAT_CLAUSE_UNDEF 0

typedef unsigned char SAT_Tvalue;

/**
   \brief array of literals assigned by the SAT solver
   \remark it is the full model if status is SAT
   \remark it is not relevant if status is UNSAT
*/
extern SAT_Tlit *SAT_literal_stack;
/**
   \brief number of literals assigned by the SAT solver
   \remark it should be the number of literals if status is SAT
   \remark it is not relevant if status is UNSAT
*/
extern unsigned  SAT_literal_stack_n;
/**
   \brief number of literals kept unmodified in the stack
   \remark User should set it to SAT_literal_stack_n to reset it
*/
extern unsigned  SAT_literal_stack_hold;

/**
   \brief number of unit literals in the stack
   \remark these literals will be true in all subsequent partial models
*/
extern unsigned  SAT_literal_stack_unit;

/**
   \brief status of the sat solver
*/
extern SAT_Tstatus SAT_status;

/**
   \brief get the decision level of the sat solver (basically, the
   number of decisions done
*/
extern SAT_Tlevel SAT_level;

SAT_Tvar    SAT_var_new(void);
void        SAT_var_new_id(unsigned id);
SAT_Tvalue  SAT_var_value(SAT_Tvar var);
SAT_Tlevel  SAT_var_level(SAT_Tvar var);
void        SAT_var_block_decide(SAT_Tvar var);
void        SAT_var_unblock_decide(SAT_Tvar var);

void        SAT_phase_cache_set(void);

#define SAT_lit(var, pol) ((SAT_Tlit)((var << 1) + pol))
#define SAT_lit_var(lit) ((SAT_Tvar)(lit >> 1))
#define SAT_lit_neg(lit) (lit ^ 1)
#define SAT_lit_pol(lit) ((SAT_Tvalue) (lit & 1))

SAT_Tvalue  SAT_lit_value(SAT_Tlit lit);
SAT_Tlevel  SAT_lit_level(SAT_Tlit lit);

SAT_Tclause SAT_clause_new(unsigned n, SAT_Tlit * lits);
SAT_Tclause SAT_clause_new_conflict(unsigned n, SAT_Tlit * lit);

void        SAT_push(void);
void        SAT_pop(void);

SAT_Tstatus SAT_solve(void);
SAT_Tstatus SAT_solve_2(SAT_Tlevel level, int dec);

/* It is counterproductive to work only on decided literals, since
   propagated literals may also be removed */
#define SAT_MIN_USE_TAUTOLOGIES 1
#define SAT_MIN_SKIP_PROPAGATED 2
void        SAT_minimal_model(SAT_Tlit ** PPlit, unsigned *n, unsigned options);

void        SAT_init(void);
void        SAT_done(void);

#if defined(INSIDE_VERIT)
extern unsigned SAT_proof_stack_n;
extern SAT_Tlit *SAT_proof_stack_lit;
extern SAT_Tclause *SAT_proof_stack_clause;
#endif

#endif
