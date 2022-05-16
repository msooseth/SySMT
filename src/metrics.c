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
 * =====================================================================================
 *
 *       Filename:  metrics.c
 *
 *    Description:  Count metrics
 *
 *         Author:  YOUR NAME (), 
 *        Company:  
 *
 * =====================================================================================
 */

#include "recursion.h"
#include "veriT-DAG.h"
#include "DAG-prop.h"

#include "metrics.h"

/*
  ---------------------------------------------------------------
  Generic counting routine
  ---------------------------------------------------------------
*/

static unsigned
metrics_count(TDAG DAG, unsigned * counter, void (*count) (TDAG))
{
  *counter = 0;
  structural_recursion_void(DAG, count);
  return *counter;
}

/*
  ---------------------------------------------------------------
  Counting quantifiers in a DAG
  ---------------------------------------------------------------
*/

static unsigned metrics_quantifier_counter = 0;

static void
metrics_quantifier_count_node(TDAG DAG)
{
  if (DAG_symb_type(DAG_symb(DAG)) == SYMB_QUANTIFIER)
    metrics_quantifier_counter += 1;
}

/*---------------------------------------------------------------*/

unsigned
metrics_quantifier_count(TDAG DAG)
{
  return metrics_count(DAG, &metrics_quantifier_counter, 
		       metrics_quantifier_count_node);
}

/*
  ---------------------------------------------------------------
  Counting quantified variables in a DAG
  ---------------------------------------------------------------
*/

static unsigned metrics_quantified_variables_counter = 0;

static void
metrics_quantified_variables_count_node(TDAG DAG)
{
  if (DAG_symb_type(DAG_symb(DAG)) == SYMB_QUANTIFIER)
    metrics_quantified_variables_counter += DAG_arity(DAG) - 1u;
}

/*---------------------------------------------------------------*/

unsigned
metrics_quantified_variable_count(TDAG DAG)
{
  return metrics_count(DAG, & metrics_quantified_variables_counter, 
		       metrics_quantified_variables_count_node);
}

/*
  ---------------------------------------------------------------
  Counting triggers in a DAG
  ---------------------------------------------------------------
*/

static unsigned metrics_trigger_counter = 0;

static void
metrics_trigger_count_node(TDAG DAG)
{
  if (DAG_prop_get(DAG, DAG_PROP_TRIGGER))
    metrics_trigger_counter += 1;
}

/*---------------------------------------------------------------*/

unsigned
metrics_trigger_count(TDAG DAG)
{
  return metrics_count(DAG, & metrics_trigger_counter,
		       metrics_trigger_count_node);
}
