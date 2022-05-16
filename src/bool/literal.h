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
  Literal management Module
  --------------------------------------------------------------
*/

#ifndef __LITERAL_H
#define __LITERAL_H

#include "stack.h"

#include "DAG.h"

#define INSIDE_VERIT
#include "veriT-SAT.h"

typedef SAT_Tvar Tvar;
typedef SAT_Tlit Tlit;

#define LIT_UNDEF 0

TSstack(_lit, Tlit);

extern Tvar var_max;

/* DD+PF Get the literal associated to DAG */
Tlit DAG_to_lit(TDAG DAG);
/* DD+PF Same as above, but returns 0 if no literal associated to DAG
   Does not set a boolean variable */
Tlit DAG_is_lit(TDAG DAG);
/* DD+PF Get the literal bounded to DAG (lit should be positive) */
TDAG lit_to_DAG(Tlit lit);
/* DD+PF Get var bounded to DAG */
TDAG DAG_to_var(Tvar var);
/* DD+PF Get DAG bounded to var */
TDAG var_to_DAG(Tvar var);

#define lit_make SAT_lit
#define lit_var  SAT_lit_var
#define lit_neg  SAT_lit_neg
#define lit_pol  SAT_lit_pol

void literal_init(void);
void literal_reset(void);
void literal_done(void);

#endif /* __LITERAL_H */
