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

#ifdef DEBUG_E
#include <stdio.h>
#endif

#include "eprover-int.h"
#include "general.h"

Tderivation
derivation_new (void)
{
  Tderivation result;
  MY_MALLOC (result, sizeof (struct TSinference));
  result->steps = table_new (20, 20);
  table_push (result->steps, inference_new (DAG_TRUE, NULL, AXIOM, 0));
  result->nb_axioms = 0;
  result->conflict = 0;
  return result;
}

void
derivation_reset (Tderivation derivation)
{
  table_apply(derivation->steps, (TFapply) & inference_free);
  table_erase(derivation->steps);
  table_push (derivation->steps, inference_new (DAG_TRUE, NULL, AXIOM, 0));
  derivation->nb_axioms = 0;
  derivation->conflict = 0;
}

void
derivation_free (Tderivation * Pderivation)
{
  table_apply((*Pderivation)->steps, (TFapply) & inference_free);
  table_erase((*Pderivation)->steps);
  table_free (&(* Pderivation)->steps);
  free (* Pderivation);
  *Pderivation = NULL;
}

#ifdef DEBUG_E
void 
derivation_fprint (FILE * file, Tderivation derivation)
{
  int i = 0;
  for (i = 1; i < table_length (derivation->steps); ++i)
    {
      fprintf (file, "%i: ", i);
      if (i == derivation->conflict)
	fprintf(file, "*** CONFLICT ***");
      inference_fprint (file, (Tinference) table_get (derivation->steps, i));
    }
}

void 
derivation_print (Tderivation derivation)
{
  derivation_fprint(stdout, derivation);
}
#endif
