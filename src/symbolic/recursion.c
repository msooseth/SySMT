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
  Module for doing structural recursion on DAGs
  --------------------------------------------------------------
*/

#include "general.h"

#include "DAG.h"
#include "DAG-tmp.h"
#include "recursion.h"

/*
  --------------------------------------------------------------
  Structural recursion - function
  --------------------------------------------------------------
*/

static void
structural_rec_aux(TDAG src, TDAG (*structural_rec_func) (TDAG))
{
  unsigned i;
  TDAG *PDAG, dest, tmp;
  if (DAG_tmp_DAG[src])
    return;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    {
      /* PF TODO maybe here we can improve by only rebuilding if
	 some change occurred */
      structural_rec_aux(DAG_arg(src, i), structural_rec_func);
      PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
    }
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  tmp = DAG_dup(structural_rec_func(dest));
  DAG_tmp_DAG[src] = tmp;
  DAG_free(dest);
}

/*--------------------------------------------------------------*/

TDAG
structural_recursion(TDAG src, TDAG (*f) (TDAG))
{
  TDAG dest;
  DAG_tmp_reserve();
  structural_rec_aux(src, f);
  dest = DAG_dup(DAG_tmp_DAG[src]);
  DAG_tmp_free_DAG(src);
  DAG_tmp_release();
  return dest;
}

/*--------------------------------------------------------------*/

static void
structural_rec_aux2(TDAG src, TDAG (*structural_rec_func) (TDAG))
{
  unsigned i;
  TDAG *PDAG, dest, tmp;
  if (DAG_tmp_DAG[src])
    return;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    {
      /* PF TODO maybe here we can improve by only rebuilding if
	 some change occurred */
      structural_rec_aux2(DAG_arg(src, i), structural_rec_func);
      PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
    }
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  tmp = structural_rec_func(dest);
  DAG_tmp_DAG[src] = tmp;
}

/*--------------------------------------------------------------*/

TDAG
structural_recursion2(TDAG src, TDAG (*f) (TDAG))
{
  TDAG dest;
  DAG_tmp_reserve();
  structural_rec_aux2(src, f);
  dest = DAG_dup(DAG_tmp_DAG[src]);
  DAG_tmp_free_DAG(src);
  DAG_tmp_release();
  return dest;
}

/*--------------------------------------------------------------*/

void
structural_recursion_array(unsigned n, TDAG * Psrc, TDAG (*f) (TDAG))
{
  unsigned i;
  TDAG * dest;
  DAG_tmp_reserve();
  MY_MALLOC(dest, n * sizeof(TDAG));
  for (i = 0; i < n; i++)
    {
      structural_rec_aux(Psrc[i], f);
      dest[i] = DAG_dup(DAG_tmp_DAG[Psrc[i]]);
    }
  for (i = 0; i < n; i++)
    {
      DAG_tmp_free_DAG(Psrc[i]);
      DAG_free(Psrc[i]);
      Psrc[i] = dest[i];
    }
  free(dest);
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Structural recursion - predicate
  --------------------------------------------------------------
*/

static int (*structural_rec_pred) (TDAG);

static int
structural_rec_pred_aux(TDAG src)
{
  unsigned i;
  if (DAG_tmp_bool[src])
    return 1;
  DAG_tmp_bool[src] = 1;
  if (!structural_rec_pred(src))
    return 0;
  for (i = 0; i < DAG_arity(src); i++)
    if (!structural_rec_pred_aux(DAG_arg(src, i)))
      return 0;
  return 1;
}

/*--------------------------------------------------------------*/

int
structural_recursion_pred(TDAG src, int (*f) (TDAG))
{
  int res;
  DAG_tmp_reserve();
  structural_rec_pred = f;
  res = structural_rec_pred_aux(src);
  DAG_tmp_reset_bool(src);
  DAG_tmp_release();
  return res;
}

/*
  --------------------------------------------------------------
  Structural recursion - void
  --------------------------------------------------------------
*/

static void (*structural_rec_void) (TDAG);

static void
structural_rec_void_aux(TDAG src)
{
  unsigned i;
  if (DAG_tmp_bool[src])
    return;
  DAG_tmp_bool[src] = 1;
  structural_rec_void(src);
  for (i = 0; i < DAG_arity(src); i++)
    structural_rec_void_aux(DAG_arg(src, i));
}

/*--------------------------------------------------------------*/

void
structural_recursion_void(TDAG src, void (*f) (TDAG))
{
  DAG_tmp_reserve();
  structural_rec_void = f;
  structural_rec_void_aux(src);
  DAG_tmp_reset_bool(src);
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Conditional structural recursion - function
  --------------------------------------------------------------
*/
static int (*cond_structural_rec_halt) (TDAG);
static TDAG (*cond_structural_rec_func) (TDAG);

/*--------------------------------------------------------------*/


static void
cond_structural_rec_aux(TDAG src)
{
  unsigned i;
  TDAG *PDAG, dest, tmp;
  if (DAG_tmp_DAG[src])
    return;
  if (cond_structural_rec_halt(src))
    {
      DAG_tmp_DAG[src] = DAG_dup(src);
      return;
    }
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    {
      cond_structural_rec_aux(DAG_arg(src, i));
      PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
    }
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  tmp = DAG_dup(cond_structural_rec_func(dest));
  DAG_tmp_DAG[src] = tmp;
  DAG_free(dest);
}

/*--------------------------------------------------------------*/

TDAG
cond_structural_recursion(TDAG src, TDAG (*f) (TDAG), int (*halt) (TDAG))
{
  TDAG dest;
  DAG_tmp_reserve();
  cond_structural_rec_func = f;
  cond_structural_rec_halt = halt;
  cond_structural_rec_aux(src);
  dest = DAG_dup(DAG_tmp_DAG[src]);
  DAG_tmp_free_DAG(src);
  DAG_tmp_release();
  return dest;
}
