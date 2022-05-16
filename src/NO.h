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
  Nelson-Oppen Module
  --------------------------------------------------------------
*/

#ifndef __NO_H
#define __NO_H

/* DD+PF
   Normal use of this library is the sequence
   NO_init
   1: NO_push
   goto 1 or
   NO_solve
   if SAT or UNDEF
     NO_quiet
     if 1
       goto 1 or
       3: NO_pop
       goto 3 or
       NO_done
     else // 0
       NO_clauses
       NO_lemmas
       goto 1
   else // UNSAT
     NO_clauses
     NO_lemmas
     2: NO_pop
     goto 2 or
     goto 1
   The abstract state is:
   the status
   the stack of literals
   the set of lemmas
   the set of clauses
*/

#include "table.h"

#include "bool.h"
#include "literal.h"
#include "veriT-status.h"

extern int * SAT_hints;
extern int SAT_hint_first;
extern int SAT_hint_last;

/* DD+PF
   Add literal in the Nelson-Oppen game, in a FIFO style.
   Use of Tliteral is for efficiency reasons. */
Tstatus NO_push(Tlit lit);

/* DD+PF
   Like push, but do not assume literal has a value, just watch
   literal and infer value if can be inferred from pushed literals */
void NO_watch(Tlit lit);

/* DD+PF
   Remove literal from the Nelson-Oppen game, in a FIFO style */
void NO_pop(void);

/* DD+PF
   Check the set of literals for satisfiability.
   May return:
   SAT: the set of literals is satisfiable
   UNSAT: the set of literals is unsatisfiable
   UNDEF: did not get to a conclusion
   In case complete is not set, this will return UNSAT or UNDEF. */
Tstatus NO_solve(void);

/* DD+PF
   Returns 0 if Nelson-Oppen has derived clauses or (general) lemmas,
   otherwise 1. */
int NO_quiet(void);

/* DD+PF
   Returns 1 if Nelson-Oppen will make the SAT solver backtrack,
   otherwise 0. */
int NO_will_backtrack (void);

/* DD+PF
   Returns the table with the clauses derived by Nelson-Oppen.
   (table contents are of type Tclause).
   We use Tclause for efficiency results: not having to build too many DAGs */
void NO_clauses(Tstack_clause * Pclauses);

/* DD+PF
   Returns the table with the lemmas derived by Nelson-Oppen.
   (table contents are of type TDAG). */
void NO_lemmas(Tstack_DAG * Plemmas);

void NO_reset(void);

void NO_init(void);
void NO_logic(char * logic);
void NO_done(void);
void NO_pre(TDAG);

#endif /* __NO_H */
