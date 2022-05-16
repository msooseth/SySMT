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
  Module for removing let constructs in formulas
  --------------------------------------------------------------
*/

#ifndef LET_ELIM_H
#define LET_ELIM_H

#include "DAG.h"

void      let_elim_init(void);
void      let_elim_done(void);

/**
   \author Pascal Fontaine
   computes a let-free equivalent term (or formula)
   \param DAG the term (or formula) with let
   \return The let-free equivalent term (or formula)
   \remarks Non destructive
   \remarks tree-linear (DAG-exponential)
   \remarks this high complexity is acceptable because this is applied on the
   input formula before let expansion (i.e, before the tree explodes)
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks the formula should have been pre-processed by binder_rename
   to avoid capture
   \pre requires the term not to have a binder on a variable in the
   scope of another binder on that variable
   \remarks for instance it breaks on
   forall y . .... let x=phi(y) .... forall y ... x...
   \post returns a let-free term
   \remarks breaks the post-condition of binder-rename
 */
TDAG      let_elim(TDAG DAG);

/**
   \brief array version of the let_elim function
   \remark Destructive
   \seealso let_elim
*/
void    let_elim_array(unsigned n, TDAG * Psrc);

#endif
