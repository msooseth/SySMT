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
  In quantified formulas, moves triggers from matrix to top
  level.
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>

#include "general.h"

#include "DAG.h"
#include "DAG-prop.h"
#include "fix-trigger.h"
#include "recursion.h"

/*--------------------------------------------------------------*/

static TDAG
fix_trigger_rec(TDAG src)
{
  if (quantifier(DAG_symb(src)) && !quantifier(DAG_symb(DAG_argn(src))))
    {
      Tstack_DAGstack *Pannot2 = DAG_prop_get(DAG_argn(src), DAG_PROP_TRIGGER);
      if (Pannot2)
	{
	  Tstack_DAGstack *Pannot1 = DAG_prop_get(src, DAG_PROP_TRIGGER);
	  if (Pannot1)
	    {
	      unsigned i;
	      for (i = 0; stack_size(*Pannot2) != 0; ++i)
		stack_push(*Pannot1, stack_pop(*Pannot2));
	      stack_free(*Pannot2);
	    }
	  else
	    DAG_prop_set(src, DAG_PROP_TRIGGER, Pannot2);
	  DAG_prop_remove(DAG_argn(src), DAG_PROP_TRIGGER);
	}
    }
  return src;
}

/*--------------------------------------------------------------*/

TDAG
fix_trigger(TDAG src)
{
  TDAG dest;
  if (DAG_quant(src))
    dest = structural_recursion(src, fix_trigger_rec);
  else
    dest = DAG_dup(src);
  return dest;
}

/*--------------------------------------------------------------*/

void
fix_trigger_array(unsigned n, TDAG * Psrc)
{
  structural_recursion_array(n, Psrc, fix_trigger_rec);
}
