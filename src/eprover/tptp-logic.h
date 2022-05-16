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
   --------------------------------------------------------------

   \file tptp-logic.h

   --------------------------------------------------------------
*/
#ifndef __TPTP_LOGIC_H
#define __TPTP_LOGIC_H

#include "DAG.h"

/*--------------------------------------------------------------*/

/** \brief The sort of terms built by the E prover */
extern Tsort    tptp_sort;

/** \brief Value for attribute misc of Skolem symbols */
extern int   TPTP_SYMB_SORT;
/** \brief Value for attribute misc of Skolem symbols */
extern int   TPTP_SYMB_SKOLEM;
/** \brief Value for attribute misc of E-defined predicate symbols */
extern int   TPTP_SYMB_PREDICATE;

/*--------------------------------------------------------------*/

extern void  tptp_logic_init(void);
extern void  tptp_logic_quit(void);
extern void  tptp_logic_set_sort(Tsort sort);
extern Tsymb tptp_logic_epred(int count, int arity);
extern Tsymb tptp_logic_skolem(int count, int arity);
extern Tsymb tptp_logic_function(char * name, int arity);
extern Tsymb tptp_logic_predicate(char * name, int arity);
extern Tsymb tptp_logic_const(void);

/*--------------------------------------------------------------*/

extern void tptp_mark_symbols(void);
extern void tptp_unmark_symbols(void);

/*--------------------------------------------------------------*/

extern Tsort tptp_sort;

#endif /* __TPTP_LOGIC_H */
