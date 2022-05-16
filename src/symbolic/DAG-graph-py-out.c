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


#include "DAG.h"
#include "DAG-tmp.h"

#include "DAG-graph-py-out.h"

#define DAG_symb_sym(a)				\
  (DAG_symb(a) == CONNECTOR_AND ||		\
   DAG_symb(a) == CONNECTOR_OR ||		\
   DAG_symb(a) == CONNECTOR_EQUIV ||		\
   DAG_symb(a) == PREDICATE_EQ ||		\
   DAG_symb(a) == FUNCTION_SUM ||		\
   DAG_symb(a) == FUNCTION_PROD)

/*--------------------------------------------------------------*/

/**
   \brief store node associated with symbol */
Tstack_unsigned symbs;

/**
   \brief node data structure */
typedef struct Tnode
{
  unsigned type;
  unsigned symb;
} Tnode;

TSstack(_node, Tnode);

static Tstack_node nodes;

typedef struct Tedge
{
  unsigned src;
  unsigned dest;
} Tedge;

TSstack(_edge, Tedge);

static Tstack_edge edges;

static unsigned nb_colors = 0;

#define COLOR_ARGPOS 0

#define NODES_FOR_SYMB
/* #define DIRECTLY_LINK_FIRST_ARGUMENT */
#define INTRODUCE_BOTH_POL

/*--------------------------------------------------------------*/

static void
DAG_graph_python_aux(TDAG DAG)
{
  unsigned i;
  Tnode *Pnode;
  Tedge *Pedge;
  if (DAG_tmp_unsigned[DAG])
    return;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_graph_python_aux(DAG_arg(DAG, i));
  stack_inc(nodes);
  Pnode = &stack_top(nodes);
#ifndef NODES_FOR_SYMB
  Pnode->symb = DAG_symb(DAG);
#else
  Pnode->symb = 0;
#endif
  DAG_tmp_unsigned[DAG] = stack_size(nodes);
  /*
  if (stack_size(nodes) == 134 ||
      stack_size(nodes) == 181)
    my_DAG_message("%d : %D\n", stack_size(nodes) - 1, DAG);
  */
#ifdef NODES_FOR_SYMB
  Pnode->type = DAG_sort(DAG);
  if (!DAG_arity(DAG))
    {
      assert(!stack_get(symbs, DAG_symb(DAG)));
      stack_set(symbs, DAG_symb(DAG), stack_size(nodes));
      Pnode->type = DAG_symb_interpreted(DAG_symb(DAG))?nb_colors++:
	DAG_symb_sort(DAG_symb(DAG));
      Pnode->symb = DAG_symb(DAG);
      return;
    }
  if (!stack_get(symbs, DAG_symb(DAG)))
    {
      /* Create node for the symbol */
      stack_inc(nodes);
      Pnode = &stack_top(nodes);
      Pnode->type = DAG_symb_interpreted(DAG_symb(DAG))?nb_colors++:
	DAG_symb_sort(DAG_symb(DAG));
      Pnode->symb = DAG_symb(DAG);
      stack_set(symbs, DAG_symb(DAG), stack_size(nodes));
    }
  /* Add an edge to the symbol */
  stack_inc(edges);
  Pedge = &stack_top(edges);
  Pedge->src = DAG_tmp_unsigned[DAG];
  Pedge->dest = stack_get(symbs, DAG_symb(DAG));
#else
  Pnode->type = DAG_symb(DAG) + 2;
#endif
  /* Add an edge for every subterm */
  if (DAG_symb_sym(DAG) || quantifier(DAG_symb(DAG)))
    {
      /* For symmetric symbols, order does not matter */
      for (i = 0; i < DAG_arity(DAG); i++)
	{
	  stack_inc(edges);
	  Pedge = &stack_top(edges);
	  Pedge->src = DAG_tmp_unsigned[DAG];
	  Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, i)];
	}
      return;
    }
  /* For non symmetric symbols path length increases with arg position */
#ifdef DIRECTLY_LINK_FIRST_ARGUMENT
  stack_inc(edges);
  Pedge = &stack_top(edges);
  Pedge->src = DAG_tmp_unsigned[DAG];
  Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, 0)];
  for (i = 1; i < DAG_arity(DAG); i++)
    {
      stack_inc(edges);
      Pedge = &stack_top(edges);
      stack_inc(nodes);
      Pnode = &stack_top(nodes);
      Pnode->type = COLOR_ARGPOS;
      Pnode->symb = 0;
      Pedge->src = (i == 1)?DAG_tmp_unsigned[DAG]:(stack_size(nodes) - 1);
      Pedge->dest = stack_size(nodes);
      stack_inc(edges);
      Pedge = &stack_top(edges);
      Pedge->src = stack_size(nodes);
      Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, i)];
    }
#else
  for (i = 0; i < DAG_arity(DAG); i++)
    {
      stack_inc(edges);
      Pedge = &stack_top(edges);
      stack_inc(nodes);
      Pnode = &stack_top(nodes);
      Pnode->type = COLOR_ARGPOS;
      Pnode->symb = 0;
      Pedge->src = (!i)?DAG_tmp_unsigned[DAG]:(stack_size(nodes) - 1);
      Pedge->dest = stack_size(nodes);
      stack_inc(edges);
      Pedge = &stack_top(edges);
      Pedge->src = stack_size(nodes);
      Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, i)];
    }
#endif
}

/*--------------------------------------------------------------*/

void
DAG_graph_python_out(FILE * file, TDAG DAG)
{
  unsigned i, l;
  stack_INIT(nodes);
  stack_INIT(edges);
  stack_INIT(symbs);
  stack_resize(symbs, stack_size(DAG_symb_stack));
  DAG_tmp_reserve();
  if (DAG_symb(DAG) == CONNECTOR_AND && DAG_arity(DAG) == 1)
    DAG = DAG_arg0(DAG);
  nb_colors = stack_size(DAG_sort_stack);
  DAG_graph_python_aux(DAG);
  DAG_tmp_reset_unsigned(DAG);
  DAG_tmp_release();
  fprintf(file, "symbols = [");
  for (i = 0, l = 0; i < stack_size(symbs); i++)
    if (stack_get(symbs, i))
      {
	unsigned j, k;
	char * symb = DAG_symb_name(i);
	char * symb_esc = NULL;
	MY_MALLOC(symb_esc, strlen(symb) * 2 + 1);
	for (j = 0, k = 0; symb[j]; j++, k++)
	  {
	    if (symb[j] == '\'')
	      symb_esc[k++] = '\\';
	    symb_esc[k] = symb[j];
	  }
	symb_esc[k] = 0;
	printf("%s(%d, '%s')",l++?", ":"", stack_get(symbs, i), symb_esc);
	free(symb_esc);
      }
  fprintf(file, "]\n");
  fprintf(file, "nodes = [");
  for (i = 0; i < stack_size(nodes); i++)
    {
      Tnode *Pnode = &stack_get(nodes, i);
      char * symb_esc;
      if (Pnode->symb)
	{
	  unsigned j, k;
	  char * symb = DAG_symb_name(Pnode->symb);
	  MY_MALLOC(symb_esc, strlen(symb) * 2 + 1);
	  for (j = 0, k = 0; symb[j]; j++, k++)
	    {
	      if (symb[j] == '\'')
		symb_esc[k++] = '\\';
	      symb_esc[k] = symb[j];
	    }
	  symb_esc[k] = 0;
	}
      else
	symb_esc = strmake("");
      printf("%s(%d, '%s', %d)",i?", ":"", Pnode->type, symb_esc, i + 1);
      free(symb_esc);
    }
  fprintf(file, "]\n");
  fprintf(file, "edges = [");
  for (i = 0; i < stack_size(edges); i++)
    {
      Tedge *Pedge = &stack_get(edges, i);
      printf("%s(%d, %d)",i?", ":"", Pedge->src, Pedge->dest);
    }
  fprintf(file, "]\n");
  /*
  for (i = 0; i < stack_size(nodes); i++)
    {
      Tnode *Pnode = &stack_get(nodes, i);
      if (!Pnode->symb || DAG_symb_misc(Pnode->symb))
	continue;
      DAG_symb_misc(Pnode->symb) = 1;
      printf("# %d : %s\n", Pnode->symb, DAG_symb_name(Pnode->symb));
    }
  */
  stack_free(symbs);
  stack_free(nodes);
  stack_free(edges);
}
