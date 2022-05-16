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

changecom(`////')dnl
define(`BEGIN',`EXTENSION(#EXT')dnl
define(`END',`)#EXT')dnl
define(`EXTENSION',ifdef(`SMTEXT',`$1',`'))dnl
changequote(`#EXT',`#EXT')dnl
#EXT
/* Warning: edits should be performed on file 'smttypes.h.m4'. */
#ifndef SMTTYPES_H
#define SMTTYPES_H

#include "DAG.h"
#include "list.h"
#include "stack.h"

typedef struct TSbind
{
  Tsymb symb;
  TDAG DAG;
} * Tbind;

#define T_BIND Tbind
#define T_BIND_LIST Tlist
#define T_FUNCTION_ID Tsymb
#define T_NUMERAL_LIST Tlist
#define T_SORT Tsort
#define T_SORT_LIST Tlist
#define T_VAR Tsymb
#define T_STACK_VAR Tstack_symb
#define T_SYMBOL_LIST Tlist
#define T_TERM TDAG
#define T_TERM_LIST Tlist
#define T_ATTR Tassoc
#define T_ATTR_LIST Tlist
#
#EXTBEGIN
#define T_MACRO struct Tbind *
#EXTEND

#endif
#EXT
