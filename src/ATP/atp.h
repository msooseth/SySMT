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
  \brief API of the interface with an automated theorem prover.

  The interface is not fully implemented and does not yet provide the
  expected functionalities.
*/
#ifndef __ATP_H
#define __ATP_H
#include <stdio.h>

#include "config.h"
#include "list.h"

#include "clue.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "veriT-status.h"

/**
   \brief Initializes the interface with ATP.  \param id identifies
   the procedure with respect to the Nelson & Oppen combination.
   
   At most one interface may be running at any time. 

   If ATP is not installed (or found) in the shell PATH, a message
   is printed to standard output, but the interface is still live,
   although it won't do anything useful.
 */
void     atp_init (const int id);

/**
   \brief Shuts down the interface with ATP.
 */
void     atp_done (void);

/**
   \brief Reset the interface with ATP.

   As a result, the  clue stack is emptied and the status is OPEN.
*/
void     atp_reset (void);

/**
   \brief Adds a clue.
*/
void     atp_push (Tclue clue);

/**
   \brief Removes a clue.
*/
void     atp_pop (void);

/**
   \brief Applies ATP to the current set of clues.
   \return The satisfiability status reported by ATP.
*/
Tstatus  atp_solve (void);

/**
   \brief Current satisfiability status of the interface.
*/
Tstatus  atp_status (void);

#ifdef PROOF
Tlist    atp_conflict (Tproofid * Pproof_id);
#else
Tlist    atp_conflict (void);
#endif
Tlist    atp_premisses (const Tclue clue);
void     atp_lemmas (Ttable lemmas);
int      atp_has_lemma (void);
int      atp_eq_queue_empty (void);
Tclue    atp_eq_queue_pop (void);
void     atp_print (FILE *);

#endif /* __ATP_H */
