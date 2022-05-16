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
  Simplex
  --------------------------------------------------------------
*/

#ifndef __SIMPLEX_H
#define __SIMPLEX_H

#include "literal.h"

#include "numbers.h"

/**
   \author Pascal Fontaine
   \typdef TLAvar
   \brief Linear Arithmetic variable
   \remark variables are unsigned
   \remark variable 0 is used for the independant term, i.e. v_0 = 1 */
typedef unsigned TLAvar;

/**
   \author Pascal Fontaine
   \brief create a new variable
   \return the new variable
   \remark all created variables are non-basic */
TLAvar LAvar_new(void);

Tstatus simplex_assert_upper_bound(TLAvar i, TLAdelta delta, Tlit lit);
Tstatus simplex_assert_lower_bound(TLAvar i, TLAdelta delta, Tlit lit);
Tstatus simplex_solve(void);
Tstack_lit simplex_conflict(void);

void simplex_constraint_push(unsigned n, unsigned *vars, TLAsigned *coefs);

void simplex_init(void);
void simplex_done(void);

#endif
