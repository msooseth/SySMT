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
  Sort utilities
  --------------------------------------------------------------
*/
#include <string.h>

#include "general.h"

#include "assoc.h"

#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "DAG-print.h"
#include "DAG-sort.h"

Tstack_Ssort DAG_sort_stack;

/*
  --------------------------------------------------------------
  Debugging routines
  --------------------------------------------------------------
*/

#ifdef DEBUG
void
DAG_sort_table_print(void)
{
  unsigned i, j;
  fprintf(stderr, "%5s %15s %5s %4s %4s %4s %4s %4s\n", 
          "index", "name", "arity", "para", "poly", "inst", "vari", "sub");
  for (i = 1; i < DAG_sort_stack->size; ++i)
    {
      fprintf(stderr, "%5i %15s %5i %4i %4i %4i %4i ",
	      i, DAG_sort_name(i) ? DAG_sort_name(i) : "" , DAG_sort_arity(i), 
	      DAG_sort_parametric(i), DAG_sort_polymorphic(i),
	      DAG_sort_instance(i), DAG_sort_variable(i));
      if (DAG_sort_arity(i) == DAG_SORT_NARY)
	fprintf(stderr, "{%i+ %i", DAG_sort_sub(i)[0], DAG_sort_sub(i)[1]);
      else if (DAG_sort_arity(i) == 0 || DAG_sort_parametric(i))
	fprintf(stderr, "{");
      else
	for (j = 0; j < DAG_sort_arity(i); ++j)
	  fprintf(stderr, "%c%i", j == 0 ? '{' : ' ', DAG_sort_sub(i)[j]);
      fprintf(stderr, "}\n");
    }
}
#endif

/*
  --------------------------------------------------------------
  Attributes
  --------------------------------------------------------------
*/

void
DAG_sort_bind(Tsort sort, void * P)
{
  assert(DAG_sort_binding(sort) == NULL);
  DAG_sort_stack->data[sort].binding = P;
}

/*--------------------------------------------------------------*/

void
DAG_sort_unbind(Tsort sort)
{
  DAG_sort_stack->data[sort].binding = NULL;
}

/*--------------------------------------------------------------*/

void
DAG_sort_mark(Tsort sort)
{
  DAG_sort_stack->data[sort].mark = 1;
}

/*--------------------------------------------------------------*/

void
DAG_sort_unmark(Tsort sort)
{
  DAG_sort_stack->data[sort].mark = 0;
}

/*--------------------------------------------------------------*/

int
DAG_sort_is_marked(Tsort sort)
{
  return (int) DAG_sort_stack->data[sort].mark;
}

/*--------------------------------------------------------------*/

int
DAG_sort_variable_fn(Tsort sort)
{
  return (int) DAG_sort_variable(sort);
}

/*
  --------------------------------------------------------------
  Invariant checking (only in DEBUG mode)
  --------------------------------------------------------------
*/

#ifdef DEBUG
/**
   \brief Invariant check for Tsort values

   \param sort a sort

   \return 1 if sort satisfies invariant properties, 0 otherwise.

   \note a value of type Tsort is either:

   - a variable sort: it is then polymorphic, has null arity and 
   no sub-sort, is neither an instance or parametric.

   - an instance of a parametric sort: it has positive arity and
   sub-sorts; it is not a sort variable; its first sub-sort is a
   parametric sort constructor and the arity is one plus the arity of
   the constructor.

   - a parametric sort constructor has positive arity and the
   array of sub-sorts is NULL; it is not a sort variable.
   
   - a sort that is polymorphic is not a parametric sort constructor.
   
   - a sort of arity zero is polymorphic it is a sort variable.

   - a sort of positive arity is polymorphic if at least one sub-sort is
   polymorphic */
int
DAG_sort_invariant(Tsort sort)
{
  if (DAG_sort_parametric(sort) &&
      (DAG_sort_variable(sort) || DAG_sort_instance(sort)))
    return 0;
  if (DAG_sort_instance(sort) &&
      (DAG_sort_variable(sort) || DAG_sort_parametric(sort)))
    return 0;
  if (DAG_sort_variable(sort) &&
      (DAG_sort_instance(sort) || DAG_sort_parametric(sort)))
    return 0;
  if (DAG_sort_polymorphic(sort))
    {
      if (DAG_sort_arity(sort) == 0) 
	{
	  if (!DAG_sort_variable(sort)) return 0;
	}
      else 
	{
	  unsigned i;
	  for (i = 1; i < DAG_sort_arity(sort); ++i)
	    if (DAG_sort_polymorphic(DAG_sort_sub(sort)[i]))
	      break;
	  if (i == DAG_sort_arity(sort))
	    return 0;
	}
    }
  if (DAG_sort_parametric(sort))
    return DAG_sort_arity(sort) > 0 && DAG_sort_stack->data[sort].sub != NULL;
  if (DAG_sort_instance(sort))
    return DAG_sort_arity(sort) > 0 &&
      DAG_sort_stack->data[sort].sub != NULL  &&
      DAG_sort_parametric(DAG_sort_sub(sort)[0]) && 
      DAG_sort_arity(sort) == DAG_sort_arity(DAG_sort_sub(sort)[0])+1;
  if (DAG_sort_variable(sort))
    return DAG_sort_polymorphic(sort) && DAG_sort_arity(sort) == 0 && 
      DAG_sort_stack->data[sort].sub == NULL;
  return 1;
}
#endif

/*
  --------------------------------------------------------------
  Constructors, destructors, basic setters and getters
  --------------------------------------------------------------
*/

Tsort
DAG_sort_new(const char *name, unsigned arity, Tsort * sub)
{
  Tsort tmp = DAG_SORT_NULL;
  if (arity == 1)
    my_error("Sort %s has only one component\n", name);
  /* Check if sort with same name already defined */
  if (name)
    tmp = DAG_sort_lookup(name);
  if (tmp != DAG_SORT_NULL)
    {
      if (DAG_sort_parametric(tmp))
        my_error("Sort %s defined as parametric and non-parametric", name);
      if (arity != DAG_sort_arity(tmp))
        my_error("Sort %s defined twice with different arities\n", name);
      if (arity == DAG_SORT_NARY) 
	{
	  if (sub[0] != DAG_sort_sub(tmp)[0] || sub[1] != DAG_sort_sub(tmp)[1])
	    my_error("Sort %s defined twice with different component sorts\n",
		     name);
	}
      else
	{
	  unsigned i;
	  for (i = 0; i < arity; i++)
	    if (sub[i] != DAG_sort_sub(tmp)[i])
	      my_error("Sort %s defined twice with different component sorts\n",
		       name);
	}
      free(sub);
      return tmp;
    }
  /* Check if there exists a similar sort */
  if (arity != 0)
    for (tmp = 1; tmp < DAG_sort_stack->size; tmp++)
      {
        if (DAG_sort_parametric(tmp) || DAG_sort_arity(tmp) != arity)
          continue;
	if (arity == DAG_SORT_NARY)
	  {
	    if (sub[0] != DAG_sort_sub(tmp)[0] ||
		sub[1] != DAG_sort_sub(tmp)[1])
	      continue;
	  }
	else
	  {
	    unsigned j;
	    for (j = 0; j < arity && sub[j] == DAG_sort_sub(tmp)[j]; j++);
	    if (j < arity)
	      continue;
	    /* PF sorts are the same, merge if possible */
	    if (name && DAG_sort_name(tmp))
	      my_error("Compound sort defined twice (%s, %s)"
		       " with different names\n", name, DAG_sort_name(tmp));
          }
        free(sub);
        return tmp;
      }
  /* Create new sort */
  tmp = DAG_sort_stack->size;
  stack_inc(DAG_sort_stack);
  DAG_sort_stack->data[tmp].name = strmake(name);
  DAG_sort_stack->data[tmp].arity = arity;
  DAG_sort_stack->data[tmp].sub = sub;
  DAG_sort_stack->data[tmp].mark = 0;
  DAG_sort_stack->data[tmp].variables = table_new(0, 10);
  DAG_sort_stack->data[tmp].nbvariables = 0;
  DAG_sort_stack->data[tmp].binding = NULL;
  DAG_sort_stack->data[tmp].variable = 0;
  DAG_sort_stack->data[tmp].instance =
    (arity > 0 && DAG_sort_parametric(sub[0]));
  DAG_sort_stack->data[tmp].parametric = 0;
  if (arity != DAG_SORT_NARY)
    {
      unsigned i;
      unsigned polymorphic = 0;
      for (i = 0; i < arity && !polymorphic; ++i)
        polymorphic |= DAG_sort_polymorphic(sub[i]);
      DAG_sort_stack->data[tmp].polymorphic = polymorphic;
    }
  else
    DAG_sort_stack->data[tmp].polymorphic = 
      DAG_sort_polymorphic(sub[0]) || DAG_sort_polymorphic(sub[1]);
  DAG_sort_stack->data[tmp].predefined = 0;
  return tmp;
}

/*--------------------------------------------------------------*/

Tsort
DAG_sort_new_args(const char *name, unsigned arity, ...)
{
  va_list adpar;
  Tsort sort;
  unsigned arity2 = 0;
  Tsort *subs = NULL;
  va_start(adpar, arity);
  while ((sort = va_arg(adpar, Tsort)) != DAG_SORT_NULL)
    {
      MY_REALLOC(subs, (arity2 + 1) * sizeof(Tsort));
      subs[arity2++] = sort;
    }
  if ((arity == DAG_SORT_NARY ? 2 : arity) != arity2)
    my_error("DAG_sort_new_args: incompatible number of arguments\n");
  va_end(adpar);
  return DAG_sort_new(name, arity, subs);
}

/*--------------------------------------------------------------*/

Tsort     
DAG_sort_new_var(char * name)
{
  static unsigned long counter = 0;
  Tsort tmp = DAG_SORT_NULL;
  if (name == NULL)
    {
      char * name2;
      unsigned size = ul_str_size(counter);
      MY_MALLOC(name2, sizeof(char) * (size + 3));
      sprintf(name2, "'_%lu", counter);
      counter += 1;
      tmp = DAG_sort_new(name2, 0, NULL);
      free(name2);
    }
  else
    tmp = DAG_sort_new(name, 0, NULL);
  DAG_sort_stack->data[tmp].variable = 1;
  DAG_sort_stack->data[tmp].instance = 0;
  DAG_sort_stack->data[tmp].parametric = 0;
  DAG_sort_stack->data[tmp].polymorphic = 1;
  return tmp;
}

/*--------------------------------------------------------------*/

Tsort
DAG_sort_new_param(char *name, unsigned arity)
{
  Tsort tmp = DAG_SORT_NULL;
  if (arity == 0 || arity == DAG_SORT_NARY)
    my_error("Parametric sort must have positive arity.");
  if (name == NULL)
    my_error("Parametric sort must be named.");

  tmp = DAG_sort_lookup(name);
  if (tmp)
    {
      if (!DAG_sort_parametric(tmp))
        my_error("Sort %s defined as parametric and non-parametric", name);
      if (arity != DAG_sort_arity(tmp))
        my_error("Sort %s defined twice with different arities\n", name);
      return tmp;
    }
  tmp = DAG_sort_stack->size;
  stack_inc(DAG_sort_stack);
  DAG_sort_stack->data[tmp].name = strmake(name);
  DAG_sort_stack->data[tmp].arity = arity;
  DAG_sort_stack->data[tmp].sub = NULL;
  DAG_sort_stack->data[tmp].mark = 0;
  DAG_sort_stack->data[tmp].variables = table_new(0, 10);
  DAG_sort_stack->data[tmp].nbvariables = 0;
  DAG_sort_stack->data[tmp].binding = NULL;
  DAG_sort_stack->data[tmp].polymorphic = 0;
  DAG_sort_stack->data[tmp].instance = 0;
  DAG_sort_stack->data[tmp].variable = 0;
  DAG_sort_stack->data[tmp].parametric = 1;
  DAG_sort_stack->data[tmp].predefined = 0;
  return tmp;
}

/*--------------------------------------------------------------*/

Tsort
DAG_sort_new_inst(char * name, Tsort sort, unsigned arity, Tsort * sub)
{
  unsigned i, j;
  Tsort tmp, *sub2;
  bool same, polymorphic;
  assert(DAG_sort_parametric(sort));
  assert(DAG_sort_arity(sort) == arity);
  assert(arity > 0);
  for (i = 1; i < DAG_sort_stack->size; ++i)
    {
      tmp = i;
      if (!DAG_sort_instance(tmp))
        continue;
      if (DAG_sort_arity(tmp) != DAG_sort_arity(sort) + 1)
	continue;
      if (DAG_sort_sub(tmp)[0] != sort)
        continue;
      for (j = 1, same = true; j <= arity && same; ++j)
        same = sub[j-1] == DAG_sort_sub(tmp)[j];
      if (!same)
        continue;
      if (name && DAG_sort_name(tmp) && strcmp(name, DAG_sort_name(tmp)) == 0)
        my_error("Duplicate sort definitions (%s, %s).", name,
		 DAG_sort_name(tmp));
      if (!DAG_sort_name(tmp) && name)
        DAG_sort_name(tmp) = strmake(name);
      free(sub);
      return tmp;
    }
  tmp = DAG_sort_stack->size;
  stack_inc(DAG_sort_stack);
  DAG_sort_stack->data[tmp].name = strmake(name);
  DAG_sort_stack->data[tmp].arity = arity + 1;
  MY_MALLOC(sub2, (arity + 1) * sizeof(Tsort));
  sub2[0] = sort;
  memcpy(sub2+1, sub, arity * sizeof(Tsort));
  DAG_sort_stack->data[tmp].sub = sub2;
  DAG_sort_stack->data[tmp].mark = 0;
  DAG_sort_stack->data[tmp].variables = table_new(0, 10);
  DAG_sort_stack->data[tmp].nbvariables = 0;
  DAG_sort_stack->data[tmp].binding = NULL;
  DAG_sort_stack->data[tmp].parametric = 0;
  DAG_sort_stack->data[tmp].variable = 0;
  DAG_sort_stack->data[tmp].instance = 1;
  for (i = 0, polymorphic = 0; i < arity && !polymorphic; ++i)
    polymorphic |= DAG_sort_polymorphic(sub[i]);
  DAG_sort_stack->data[tmp].polymorphic = polymorphic;
  DAG_sort_stack->data[tmp].predefined = false;

  free(sub);
  return tmp;
}

/*--------------------------------------------------------------*/

Tsort
DAG_sort_lookup(const char *name)
{
  Tsort sort;
  for (sort = 1; sort < DAG_sort_stack->size; ++sort)
    if (DAG_sort_name(sort) && !DAG_sort_instance(sort) &&
	strcmp(DAG_sort_name(sort), name) == 0)
      return sort;
  return DAG_SORT_NULL;
}

/*--------------------------------------------------------------*/

void
DAG_sort_unbind_rec(Tsort sort)
{
  if (sort == DAG_SORT_NULL) return;
  if (DAG_sort_binding(sort))
    {
      unsigned i;
      DAG_sort_unbind(sort);
      if (DAG_sort_parametric(sort))
	return;
      if (DAG_sort_arity(sort) == DAG_SORT_NARY)
	for (i = 0; i < 2; ++i)
	  DAG_sort_unbind_rec(DAG_sort_sub(sort)[i]);
      else
	for (i = 0; i < DAG_sort_arity(sort); ++i)
	  DAG_sort_unbind_rec(DAG_sort_sub(sort)[i]);
    }
}

/*
  --------------------------------------------------------------
  Module initialization and release
  --------------------------------------------------------------
*/

void
DAG_sort_init(void)
{
  stack_INIT(DAG_sort_stack);
  /* Reserve ((Tsort) 0) */
  stack_inc(DAG_sort_stack);
  SORT_BOOLEAN = DAG_sort_new(SORT_BOOLEAN_STR, 0, NULL);
  DAG_sort_set_predefined(SORT_BOOLEAN);
}

/*--------------------------------------------------------------*/

void
DAG_sort_done(void)
{
  Tsort tmp;
  for (tmp = 1; tmp < DAG_sort_stack->size; ++tmp)
    {
      unsigned i;
      Ttable variables = DAG_sort_stack->data[tmp].variables;
      free(DAG_sort_stack->data[tmp].name);
      free(DAG_sort_stack->data[tmp].sub);
      for (i = 0; i < table_length(variables); i++)
	DAG_free(DAG_of_ptr(table_get(variables, i)));
      table_free(&variables);
    }
  stack_free(DAG_sort_stack);
}

/*--------------------------------------------------------------*/

Tsort
DAG_sort_combine(Tsort sort1, Tsort sort2)
{
  if (sort1 == sort2) 
    return sort1;
  if ((sort1 == SORT_INTEGER && sort2 == SORT_REAL) ||
      (sort2 == SORT_INTEGER && sort1 == SORT_REAL))
    return SORT_REAL;
  return DAG_SORT_NULL;
}
