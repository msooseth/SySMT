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
  E prover interface module

  TODO NOW
  
  test

  TODO LATER

  see which options implemented in veriT-fol need to be ported 
  to veriT.

  theories need to be handled in a different way so that hierarchical
  properties are taken into account.

  see if and how definitions can be used to simplify the clue
  stack

  proof production needs to be designed and implemented

  e_print needs to be implemented

  turn E prover a library with incrementality

  fork on e_solve to allow multiple instances

  --------------------------------------------------------------
*/
#ifndef __EPROVER_H
#define __EPROVER_H
#include <stdio.h>

#include "config.h"
#include "types.h"
#include "list.h"

/* #define DEBUG_E */

#include "clue.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "veriT-status.h"

void     e_init(const unsigned id);
void     e_done(void);
void     e_reset(void);

void     e_push(Tclue clue);
void     e_pop(void);
Tstatus  e_solve(void);
Tstatus  e_status(void);

#ifdef PROOF
Tlist    e_conflict(Tproof_id * Pproof_id);
#else
Tlist    e_conflict(void);
#endif
Tlist    e_premisses(const Tclue clue);
void     e_lemmas(Ttable lemmas);
bool     e_has_lemma(void);
bool     e_eq_queue_empty(void);
Tclue    e_eq_queue_pop(void);
void     e_print(FILE *);

#endif /* __EPROVER_H */
