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

/* ------------------------------------------------------------
 *  dbg-trigger.c
 *  
 *
 *  Debugging resources for triggers.
 *
   ------------------------------------------------------------ */

#include "stack.h"

#include "veriT-DAG.h"
#include "DAG-print.h"
#include "DAG-prop.h"

#include "dbg-trigger.h"

/*--------------------------------------------------------------*/
/*--------------------------------------------------------------*/
/*--------------------------------------------------------------*/

static void
trigger_print (Tstack_DAG trigger)
{
  unsigned i;
  for (i = 0; i < stack_size(trigger); ++i)
    my_DAG_message("\t%02u:\t%D\n", i + 1, stack_get(trigger, i));
}

/*--------------------------------------------------------------*/

static void
trigger_list_print (Tstack_DAGstack triggers)
{
  unsigned i;
  for (i = 0; i < stack_size(triggers); ++i) 
    {
      trigger_print(stack_get(triggers, i));
      my_DAG_message ("\n");
    }
}

/*--------------------------------------------------------------*/
/*--------------------------------------------------------------*/
/*--------------------------------------------------------------*/

void dbg_trigger_print (TDAG DAG)
{
  Tstack_DAGstack * Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
  my_DAG_message("triggers for:\n%D\n", DAG);
  if (Ptriggers)
    trigger_list_print(*Ptriggers);
  else
    my_DAG_message("\tnone\n");
}

