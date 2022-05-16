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

#include "config.h"

#include "DAG.h"
#include "general.h"
#include "stack.h"

#include "literal.h"

Tvar var_max = 0;
Tvar var_available = 0;
static unsigned var_alloc = 0;
static TDAG *var2DAG = NULL;
static Tvar *DAG2var = NULL;

/* #define DEBUG_BOOL */

/*--------------------------------------------------------------*/

static void
literal_DAG_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  unsigned i;
  MY_REALLOC(DAG2var, new_alloc * sizeof(Tvar));
  for (i = old_alloc; i < new_alloc; i++)
    DAG2var[i] = 0;
}

/*--------------------------------------------------------------*/

Tlit
DAG_is_lit(TDAG DAG)
{
  return DAG2var[DAG] << 1;
}

/*--------------------------------------------------------------*/

Tlit
DAG_to_lit(TDAG DAG)
{
  unsigned positive = 1;
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      DAG = DAG_arg0(DAG);
      positive = !positive;
    }
  if (!DAG2var[DAG])
    {
      var_max++;
      if (var_alloc == var_max)
	{
	  unsigned i;
	  var_alloc *= 2;
	  MY_REALLOC(var2DAG, var_alloc * sizeof(TDAG));
	  for (i = var_max; i < var_alloc; i++)
	    var2DAG[i] = 0;
	}
      DAG2var[DAG] = var_max;
      var2DAG[var_max] = DAG_dup(DAG);
#ifdef DEBUG_BOOL
      my_DAG_message("DAG variable: %D, %d\n", DAG, var_max);
#endif
    }
  return lit_make(DAG2var[DAG], positive);
}

/*--------------------------------------------------------------*/

TDAG
lit_to_DAG(Tlit lit)
{
  return var2DAG[lit_var(lit)];
}

/*--------------------------------------------------------------*/

TDAG
DAG_to_var(TDAG DAG)
{
  return DAG2var[DAG];
}

/*--------------------------------------------------------------*/

TDAG
var_to_DAG(Tvar var)
{
  return var2DAG[var];
}

/*--------------------------------------------------------------*/

void
literal_init(void)
{
  assert(!var2DAG);
  assert(!DAG2var);
  var_alloc = 64;
  MY_MALLOC(var2DAG, var_alloc * sizeof(TDAG));
  var2DAG[0] = DAG_NULL;
  var_max = 0;
  DAG_set_hook_resize(literal_DAG_hook_resize);
}

/*--------------------------------------------------------------*/

void
literal_reset(void)
{
  unsigned i;
  assert(var2DAG);
  for (i = 1; i <= var_max; i++)
    {
      DAG2var[var2DAG[i]] = 0;
      DAG_free(var2DAG[i]);
      var2DAG[i] = 0;
    }
  var_max = 0;
}

/*--------------------------------------------------------------*/

void
literal_done(void)
{
  unsigned i;
  assert(var2DAG);
  for (i = 1; i <= var_max; i++)
    DAG_free(var2DAG[i]);
  free(var2DAG);
}
