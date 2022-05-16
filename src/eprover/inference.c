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
#include "DAG-print.h"
#endif

#include "eprover-int.h"
#include "general.h"

Tinference
inference_new (TDAG DAG, Tlist premisses, Trole role, int final)
{
  Tinference inf;
  MY_MALLOC(inf, sizeof (struct TSinference));
  inf->DAG = DAG_dup (DAG);
  inf->premisses = premisses;
  inf->role = role;
  inf->flag = 0;
  inf->final = final;
  return inf;
}

void
inference_free (Tinference inf)
{
  DAG_free(inf->DAG);
  list_free(&inf->premisses);
  free(inf);
}

void
inference_reset_flag (Tinference inf)
{
  inf->flag = 0;
}

#ifdef DEBUG_E
void
inference_fprint (FILE * file, Tinference inf)
{
  switch (inf->role) {
  case AXIOM: 
    fprintf(file, "axiom "); 
    break;
  case HYPOTHESIS: 
    fprintf(file, "hypothesis "); 
    break;
  case DEFINITION: 
    fprintf(file, "definition "); 
    break;
  case LEMMA: 
    fprintf(file, "lemma "); 
    break;
  case THEOREM: 
    fprintf(file, "theorem "); 
    break;
  case CONJECTURE: 
    fprintf(file, "conjecture "); 
    break;
  case LEMMA_CONJECTURE: 
    fprintf(file, "lemma_conjecture "); 
    break;
  case NEGATED_CONJECTURE: 
    fprintf(file, "negated_conjecture "); 
    break;
  case PLAIN: 
    fprintf(file, "plain "); 
    break;
  case UNKNOWN: 
    fprintf(file, "unknown "); 
    break;
  }
  DAG_fprint (file, inf->DAG);
  {
    Tlist list = inf->premisses;
    LIST_LOOP_BEGIN(list, Tpremisse, p);
    fprintf(file, " %s[%lu]", 
	    premisse_is_external(p) ? "clue" : "inf",
	    (long unsigned) premisse_value(p));
    LIST_LOOP_END(list);
  }
  if (inf->final) fprintf(file, " [final]");
  fprintf(file, "\n");
}
#endif
