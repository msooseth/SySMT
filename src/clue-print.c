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
  Clue Display Module
  --------------------------------------------------------------
*/

#include "config.h"
#include "general.h"

#include "clue-print.h"
#include "DAG-print.h"

void clue_fprint (FILE * file, Tclue clue)
{
  if (!clue) 
    {
      fprintf(file, "NULL");
      return;
    }
  if (!clue->polarity) fputc('~', file);
  if (clue->type == CLUE_ABSTRACT_TERM ||
      clue->type == CLUE_ABSTRACT_PRED ||
      clue->type == CLUE_ABSTRACT_QUANT)
    {
      DAG_fprint(file, clue->DAG[0]);
      fprintf(file, " { = ");
      DAG_fprint(file, clue->DAG[1]);
      fprintf(file, "}");
    }
  else if (clue->DAG[1])
    {
      DAG_fprint(file, clue->DAG[0]);
      fprintf(file, " = ");
      DAG_fprint(file, clue->DAG[1]);
    }
  else
    DAG_fprint(file, clue->DAG[0]);
}

/*--------------------------------------------------------------*/

void
clue_print2 (Tclue clue)
{
  if (clue == NULL) 
    {
      my_message ("Clue NULL\n");
      return;
    }
  my_message("Clue %x\n",clue);
  my_DAG_message("  DAG[0] :%D\n  DAG[1] :%D\n", clue->DAG[0], clue->DAG[1]);
  switch (clue->type)
    {
    case CLUE_LITERAL:
      my_message("  type    : literal\n");
      break;
    case CLUE_CONGRUENT:
      my_message("  type    : congruent\n");
      break;
    case CLUE_MODEL_EQUALITY:
      my_message("  type    : model equality\n");
      break;
    case CLUE_MERGE:
      my_message("  type    : merge\n");
      break;
    case CLUE_INEQUALITY:
      my_message("  type    : inequality\n");
      break;
    case CLUE_ABSTRACT_TERM:
      my_message("  type    : term\n");
      break;
    case CLUE_ABSTRACT_PRED:
      my_message("  type    : pred\n");
      break;
    case CLUE_ABSTRACT_QUANT:
      my_message("  type    : quant\n");
      break;
    case CLUE_IMPLIED_INEQUALITY:
      my_message("  type    : implied inequality\n");
      break;
    default:
      my_message("  type    : unknown\n");
    }
  my_message("  gc_count  : %d\n", clue->gc_count);
  my_message("  polarity  : %d\n", clue->polarity);
  my_message("  misc      : %d\n", clue->misc);
#ifdef PROOF
  my_message("  proof_id  : %d\n", clue->proof_id);
#endif
}

/*--------------------------------------------------------------*/

void
list_clue_fprint (FILE * file, Tlist list)
{
  if (list)
    {
      Tlist ptr = list;
      do
	{
	  clue_fprint (file, (Tclue) list_car (ptr));
	  fprintf (file, "\n");
	  ptr = list_cdr (ptr);
	}
      while (ptr != list);
    }
  else
    {
      fprintf (file, "empty\n");
    }
}
