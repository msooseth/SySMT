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
  Module for simplifying formulas by eliminating uninterpreted
  constants.
  --------------------------------------------------------------
*/

/** \todo Enrich comments */

#include <stdlib.h>
#include <strings.h>

#include "general.h"
#include "statistics.h"

#include "bitset.h"

#include "DAG-print.h"
#include "DAG.h"
#include "DAG-subst.h"
#include "DAG-stat.h"
#include "polarities.h"
#include "simplify.h"
#include "simp-formula-sat.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"

/* #define DEBUG_SIMP_FORMULA_SAT */
/* #define SIMP_STAT */

#ifdef SIMP_STAT

#define STAT_NEW(A, B) stat_ ## A = stats_counter_new(#A, B, "%4d")
#define STAT_INC(A) stats_counter_inc(stat_ ## A )
#else
#define STAT_NEW(A,B) ;
#define STAT_INC(A) ;
#endif

#define INT_OF_PTR(p) ((int) (intptr_t) p)
#define PTR_OF_INT(i) ((void *) (intptr_t) i)

/*--------------------------------------------------------------*/
/* x = a and phi(x) --> phi(a)                                  */
/*--------------------------------------------------------------*/

/* x = t and phi(x) --> phi(t), if x \notin t */
/* p EQV G and H(p) --> H(G), if p \notin G */

/* 
   rewrite as follows
   x = t and phi(x) --> phi(t), if x \notin t
   p EQV G and H(p) --> H(G), if p \notin G

   Applying such rewrite rule one at a time is sub-optimal. It is
   effectively a source of ineficiency on some benchmarks, where it
   causes the pre-processing time to grow exceedingly compared to
   other tools.

  In the following we describe an approach to apply several
  substitutions at once, taking care of possible mutual dependencies.

  A set of candidate substitutions S = {(xi, ti)| 1 <= i <= n} is 
  collected.

  Let G = (X, E) be the directed graph, where X = {x1 ... xn} and
  (xi, xj) \in E iff xj is a subterm of ti.

  Let S = be the strongly connected components of G.  Let S' \subseteq
  S = {s \in S | \card s > 1} and S'' = S - S'. Each s \in S' is a
  graph (Xs, Es) that has at least one cycle. Let prune(s) = (Xs, Es')
  be an acyclic sub-graph of s, and prune(S') = {prune(s) | s \in S'}.

  G' = S'' \cup prune(S') is acyclic. Let xs1 ... xsn be a topological
  sort of G'. 

  The substitution to apply to the original formula is 
  ts1' := ts1
  xs1 := ts1'
  ts2' := ts2(xs1 := ts1)
  xs2 := ts2'
  ts3' := ts3(xs2 := ts2')(xs1 := ts1)
  xs3 := ts3'
  ...
  tsn' := tsn(xsn-1 := tsn-1')...(xs1 := ts1')
  xsn := tsn'

*/

/*--------------------------------------------------------------*/

static void
collect_rewrite1(TDAG target, TDAG source, Tstack_DAG *Plhs, Tstack_DAG *Prhs)
{
  unsigned index;
  if (DAG_contain(source, target) || DAG_quant(source))
    return;
  index = (unsigned) DAG_misc(target);
  if (index == 0)
    {
      DAG_misc_set(target, (int) stack_size(*Plhs));
      stack_push(*Plhs, target);
      stack_push(*Prhs, source);
    }
  else
    {
      TDAG source2 = stack_get(*Prhs, index);
      if (DAG_count_nodes(source2) < DAG_count_nodes(source))
	stack_set(*Prhs, index, source2);
    }
}

/*--------------------------------------------------------------*/

static void
simplify_collect_rewrite2(TDAG src, int pol, Tstack_DAG *Plhs, Tstack_DAG *Prhs)
/* PF returns 1 if there is something that defines a symbol in
   src taken with pol(arity).
   Sets target and source to what is defined and to what. */
{
  unsigned i;
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      simplify_collect_rewrite2(DAG_arg0(src), INV_POL(pol), Plhs, Prhs);
      return;
    }
  if ((pol == POL_POS && DAG_symb(src) == CONNECTOR_AND) ||
      (pol == POL_NEG && DAG_symb(src) == CONNECTOR_OR))
    {
      for (i = 0; i < DAG_arity(src); i++)
	simplify_collect_rewrite2(DAG_arg(src, i), pol, Plhs, Prhs);
    }
  else if (pol == POL_NEG && DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      simplify_collect_rewrite2(DAG_arg0(src), POL_POS, Plhs, Prhs);
      simplify_collect_rewrite2(DAG_arg1(src), POL_NEG, Plhs, Prhs);
    }
  else if (pol == POL_POS && DAG_symb(src) == PREDICATE_EQ)
    {
      if (!DAG_arity(DAG_arg0(src))
	  && !DAG_symb_interpreted(DAG_symb(DAG_arg0(src))))
	collect_rewrite1(DAG_arg0(src), DAG_arg1(src), Plhs, Prhs);
      else if (!DAG_arity(DAG_arg1(src)) &&
	       !DAG_symb_interpreted (DAG_symb(DAG_arg1(src))))
	collect_rewrite1(DAG_arg1(src), DAG_arg0(src), Plhs, Prhs);
    }
  else if (pol == POL_POS && DAG_symb(src) == CONNECTOR_EQUIV)
    {
      /* PF Boolean proposition equivalent to something */
      if (!DAG_arity(DAG_arg0(src)) &&
	  !DAG_symb_interpreted(DAG_symb(DAG_arg0(src))))
	collect_rewrite1(DAG_arg0(src), DAG_arg1(src), Plhs, Prhs);
      else if (!DAG_arity(DAG_arg1(src)) &&
	       !DAG_symb_interpreted(DAG_symb(DAG_arg1(src))))
	collect_rewrite1(DAG_arg1(src), DAG_arg0(src), Plhs, Prhs);
    }
  else if (!DAG_arity(src) && !DAG_symb_interpreted(DAG_symb(src)))
    /* PF Boolean proposition */
    collect_rewrite1(src, pol == POL_POS ? DAG_TRUE : DAG_FALSE, Plhs, Prhs);
#if 0
  else if (pol == POL_POS && DAG_symb(src) == QUANTIFIER_FORALL)
    collect_rewrite_quant(src, Plhs, Prhs);
#endif
  return;
}

/*--------------------------------------------------------------*/

static void
collect_edges_rec(TDAG DAG, Tlist * Plist)
{
  unsigned i;
  if (DAG_flag(DAG))
    return;
  DAG_flag_set(DAG, 1);
  if (DAG_misc(DAG))
    *Plist = list_add(*Plist, DAG_ptr_of(DAG));
  for (i = 0; i < DAG_arity(DAG); ++i)
    collect_edges_rec(DAG_arg(DAG, i), Plist);
}

/*--------------------------------------------------------------*/
static void
collect_edges(TDAG *Plhs, TDAG *Prhs)
{
  assert(!DAG_Pflag(*Plhs));
  DAG_Pflag_set(*Plhs, NULL);
  collect_edges_rec(*Prhs, (Tlist *) &DAG_Pflag(*Plhs));
  DAG_reset_flag(*Prhs);
}

/*--------------------------------------------------------------*/

static unsigned
DAG_index(void * ptr)
{
  TDAG DAG = DAG_of_ptr(ptr);
  assert(DAG_misc(DAG) > 0);
  return DAG_misc(DAG) - 1u;
}

/*--------------------------------------------------------------*/

typedef struct TShypernode {
  Tbs   nodes;     /**< elements of the hyper-node */
  Tlist adjacency; /**< list of neighbor hyper-nodes */
  Tlist super;     /**< list of containing hyper-nodes */
  int   visited;   /**< graph traversal attribute */
} * Thypernode;

/*--------------------------------------------------------------*/
#ifdef DEBUG_SIMP_FORMULA_SAT
static void
hypernode_fprint(FILE * file, Tbs_mgr mgr, Thypernode h)
{
  Tlist list;
  fprintf(file, "< ");
  bitset_fprint(file, mgr, h->nodes);
  list = h->adjacency;
  LIST_LOOP_BEGIN(list, Thypernode, h2);
  {
    fprintf(file, "\n\t=>");
    bitset_fprint(file, mgr, h2->nodes);
  }
  LIST_LOOP_END(list);
  list = h->super;
  LIST_LOOP_BEGIN(list, Thypernode, h2);
  {
    fprintf(file, "\n\t<:");
    bitset_fprint(file, mgr, h2->nodes);
  }
  LIST_LOOP_END(list);
  fprintf(file, ">");
}
#endif

/*--------------------------------------------------------------*/

/*
  Source: wikipedia

  algorithm tarjan is
  input: graph G = (V, E)
  output: set of strongly connected components (sets of vertices)

  index := 0
  S := empty
  for each v in V do
    if (v.index is undefined)
      strongconnect(v)
    end if
  repeat

  function strongconnect(v)
    // Set the depth index for v to the smallest unused index
    v.index := index
    v.lowlink := index
    index := index + 1
    S.push(v)

    // Consider successors of v
    for each (v, w) in E do
      if (w.index is undefined) then
        // Successor w has not yet been visited; recurse on it
        strongconnect(w)
        v.lowlink := min(v.lowlink, w.lowlink)
      else if (w is in S) then
        // Successor w is in stack S and hence in the current SCC
        v.lowlink := min(v.lowlink, w.index)
      end if
    end for

    // If v is a root node, pop the stack and generate an SCC
    if (v.lowlink = v.index) then
      start a new strongly connected component
      repeat
        w := S.pop()
        add w to current strongly connected component
      until (w = v)
      output the current strongly connected component
    end if
  end function
 */
static void
tarjan_scc_rec(TDAG DAG, int *table_index, int *table_lowlink,
	       Tstack_DAG *Pstack, int *Pindex, Tlist * Plist)
{
  Tlist tmp;
  Tlist edges = DAG_Pflag(DAG);
  table_index[DAG_misc(DAG)] = *Pindex;
  table_lowlink[DAG_misc(DAG)] = *Pindex;
  *Pindex += 1;
  stack_push(*Pstack, DAG);
  tmp = edges;
  if (tmp)
    do
      {
	TDAG DAG2 = DAG_of_ptr(list_car(tmp));
	if (table_index[DAG_misc(DAG2)] == 0)
	  {
	    tarjan_scc_rec(DAG2, table_index, table_lowlink,
			   Pstack, Pindex, Plist);
	    table_lowlink[DAG_misc(DAG)] = MIN(table_lowlink[DAG_misc(DAG)],
					       table_lowlink[DAG_misc(DAG2)]);
	  }
	else
	  {
	    unsigned i;
	    for (i = 0; i < stack_size(*Pstack); ++i)
	      if (stack_get(*Pstack, i) == DAG2)
		break;
	    if (i != stack_size(*Pstack))
	      table_lowlink[DAG_misc(DAG)] = MIN(table_lowlink[DAG_misc(DAG)],
						 table_index[DAG_misc(DAG2)]);
	  }
	tmp = list_cdr(tmp);
      }
    while (tmp != edges);
  if (table_lowlink[DAG_misc(DAG)] == table_index[DAG_misc(DAG)])
    {
      TDAG DAG2;
      Tstack_DAG scc = NULL;
      unsigned i = stack_size(*Pstack) - 1u;
      while (stack_get(*Pstack, i) != DAG)
	{
	  assert(i);
	  i--;
	}
      stack_INIT(scc);
      do
	{
	  DAG2 = stack_pop(*Pstack);
	  stack_push(scc, DAG2);
	}
      while (DAG2 != DAG);
      *Plist = list_add(*Plist, scc);
    }
}

/*--------------------------------------------------------------*/

static Tlist
tarjan_scc(Tstack_DAG vertices)
{
  unsigned size = stack_size(vertices);
  int    *table_index, *table_lowlink;
  Tstack_DAG stack = NULL;
  unsigned capacity = (unsigned) (size * sizeof(int));
  int    index;
  unsigned i;
  Tlist  result;
  MY_MALLOC(table_index, capacity);
  bzero(table_index, capacity);
  MY_MALLOC(table_lowlink, capacity);
  bzero(table_lowlink, capacity);
  index = 0;
  stack_INIT(stack);
  result = NULL;
  for (i = 1; i < size; ++i)
    {
      TDAG vertex = stack_get(vertices, i);
      if (table_index[DAG_misc(vertex)]== 0)
	tarjan_scc_rec(vertex, table_index, table_lowlink, &stack,
		       &index, &result);
    }
  free(table_index);
  free(table_lowlink);
  stack_free(stack);
  return result;
}

/*--------------------------------------------------------------*/

static void
topological_sort_rec(TDAG DAG, Tstack_DAG *Porder)
{
  Tlist edges, tmp;
  if (DAG_flag(DAG)) return;
  DAG_flag_set(DAG, 1);
  edges = DAG_Pflag(DAG);
  tmp = edges;
  if (tmp)
    do
      {
	TDAG DAG2 = DAG_of_ptr(list_car(tmp));
	topological_sort_rec(DAG2, Porder);
	tmp = list_cdr(tmp);
      }
    while (tmp != edges);
  stack_push(*Porder, DAG);
}

/*--------------------------------------------------------------*/

static void
topological_sort_reset_flag(TDAG DAG)
{
  Tlist edges, tmp;
  if (DAG_flag(DAG) == 0) return;
  DAG_flag_set(DAG, 0);
  edges = DAG_Pflag(DAG);
  tmp = edges;
  if (tmp)
    do
      {
	TDAG DAG2 = DAG_of_ptr(list_car(tmp));
	topological_sort_reset_flag(DAG2);
	tmp = list_cdr(tmp);
      }
    while (tmp != edges);
}

/*--------------------------------------------------------------*/

static void
topological_sort(Tstack_DAG vertices, Tstack_DAG *Porder)
{
  unsigned i;
  for (i = 1; i < stack_size(vertices); ++i)
    topological_sort_rec(stack_get(vertices, i), Porder);
  for (i = 1; i < stack_size(vertices); ++i)
    topological_sort_reset_flag(stack_get(vertices, i));
}

/*--------------------------------------------------------------*/

#ifdef DEBUG_SIMP_FORMULA_SAT
static void 
hypergraph_print(Ttable out, Ttable super, Ttable visited, Ttable removed)
{
  int i;
  fprintf(stderr, "out = [\n");
  for (i = 0; i < table_length(out); ++i)
    {
      Tlist list = table_get(out, i);
      fprintf(stderr, "\t%i: {", i);
      LIST_LOOP_BEGIN(list, intptr_t, j);
      fprintf(stderr, "%i ", (int) j);
      LIST_LOOP_END(list);
      fprintf(stderr, "\t}\n");
    }
  fprintf(stderr, "]\n");
  fprintf(stderr, "super = [\n");
  for (i = 0; i < table_length(super); ++i)
    {
      Tlist list = table_get(super, i);
      fprintf(stderr, "\t%i: {", i);
      LIST_LOOP_BEGIN(list, intptr_t, j);
      fprintf(stderr, "%i ", (int) j);
      LIST_LOOP_END(list);
      fprintf(stderr, "\t}\n");
    }
  fprintf(stderr, "]\n");
  fprintf(stderr, "visited = [");
  for (i = 0; i < table_length(visited); ++i)
    {
      void * val = table_get(visited, i);
      if (val) fprintf(stderr, "%i ", (intptr_t) val);
    }
  fprintf(stderr, "]\n");
  fprintf(stderr, "removed = [");
  for (i = 0; i < table_length(removed); ++i)
    {
      void * val = table_get(removed, i);
      if (val) fprintf(stderr, "%i ", (intptr_t) val);
    }
  fprintf(stderr, "]\n");
}
#endif

/*--------------------------------------------------------------*/

static unsigned 
hypernode_add(Tbs_mgr mgr, Tbs hnode, Ttable table_nodes)
{
  unsigned i, length;
  length = table_length(table_nodes);
  for (i = 0; i < length; ++i)
    {
      Tbs hnode2 = (Tbs) table_get(table_nodes, i);
      if (bitset_equal(mgr, hnode2, hnode))
	{
	  bitset_free(mgr, hnode);
	  return i;
	}
    }
  table_push(table_nodes, hnode);
  return length;
}

/*--------------------------------------------------------------*/

static int
get_stack_pos(int n, Ttable stack, Ttable super)
{
  unsigned i;
  Tlist list;
  list = table_get(super, n);
  for (i = table_length(stack); i-- > 0; )
    {
      int m = INT_OF_PTR(table_get(stack, i));
      if (m == n) return i;
      LIST_LOOP_BEGIN(list, void *, tmp);
      {
	if (INT_OF_PTR(tmp) == m)
	  return i;
      }
      LIST_LOOP_END(list);
    }
  return -1;
}

/*--------------------------------------------------------------*/

/**
   \brief returns the hyper-edge index that links n1 to n2
   \param n1 an hyper-node index
   \param n2 another hyper-node index
   \param out table of outgoing edges indices
   \param removed table of deleted edges
   \return if there is an outgoing edge from n1 that has
   n2 as a destination, returns its index; otherwise, returns -1 */
static int
get_edge(unsigned n1, int n2, Ttable out,  Ttable removed)
{
  Tlist list;
  assert(n1 < table_length(out));
  list = table_get(out, n1);
  LIST_LOOP_BEGIN(list, void *, e);
  {
    int edge = INT_OF_PTR(e);
    if (edge == n2 && !table_get(removed, edge))
      return edge;
  }
  LIST_LOOP_END(list);
  return -1;
}

/*--------------------------------------------------------------*/

/**
   \brief marks as removed an hyper-edge in cycle
   \param cycle a table storing a cyclic sequence of hyper-edges
   \param removed a table indexed by edges that indicate those
   removed 
   \note currently, the last edge added to cycle is removed; a
   sophisticated heuristics is most probably preferable */
static void
break_cycle(Ttable cycle, Ttable removed)
{
  int e; /** index of the edge to be removed */
  e = INT_OF_PTR(table_top(cycle));
  assert(e < table_length(removed));
  table_set(removed, e, PTR_OF_INT(1));
}

/*--------------------------------------------------------------*/

/**
   \brief builds a cyclic sequence of edges in the given stack
   \param ptr the position where the cycle starts in the stack
   \param stack the stack of currently visited hyper-nodes
   \param out the table storing the outgoing hyper-edges of each 
   hyper-node.
   \param removed the table recording the deleted hyper-edges */
static void
remove_cycles_one(unsigned pos, Ttable stack, Ttable out, Ttable removed)
{
  Ttable cycle;
  int    ptr, prev, curr;
  ptr = table_length(stack) - 1;
  cycle = table_new(table_length(stack), 1);
  prev = INT_OF_PTR(table_get(stack, ptr--));
  while (1)
    {
      int e;
      curr = INT_OF_PTR(table_get(stack, ptr--));
      e = get_edge(curr, prev, out, removed);
      if (e != -1)
	table_push(cycle, PTR_OF_INT(e));
      if (ptr == pos)
	break;
      prev = curr;
    }
  break_cycle(cycle, removed);
  table_free(&cycle);
}

/*--------------------------------------------------------------*/

/**
   \brief removes cycles reachable from hyper-node n
   \param n the index of a hyper-node
   \param stack the stack of hyper-nodes being visited
   \param out table mapping hyper-nodes to the list of outgoing edges 
   \param super table mapping hyper-nodes to the list of containing
   hyper-nodes
   \param visited table registering visited hyper-nodes
   \param removed table registering removed hyper-edges
*/
static int
remove_cycles_rec(int n, Ttable stack,
		  Ttable out, Ttable super, Ttable visited, Ttable removed)
{
  int pos;
  Tlist list;
  pos = get_stack_pos(n, stack, super);
  table_push(stack, PTR_OF_INT(n));
  if (pos != -1)
    {
      remove_cycles_one(pos, stack, out, removed);
      table_pop(stack);
      return 1;
    }
  list = table_get(super, n);
  LIST_LOOP_BEGIN(list, void *, tmp);
  {
    int p = INT_OF_PTR(tmp);
    if (!table_get(visited, p))
      if (remove_cycles_rec(p, stack, 
			    out, super, visited, removed))
	{
	  table_pop(stack);
	  return 1;
	}
  }
  LIST_LOOP_END(list);
  list = table_get(out, n);
  LIST_LOOP_BEGIN(list, void *, e);
  {
    int edge = INT_OF_PTR(e);
    if (!table_get(removed, edge) && !table_get(visited, edge))
      if (remove_cycles_rec(edge, stack, out, super, visited, removed))
	{
	  table_pop(stack);
	  return 1;
	}
  }
  LIST_LOOP_END(list);
  table_set(visited, n, PTR_OF_INT(n));
  table_pop(stack);
  return 0;
}

/*--------------------------------------------------------------*/

/**
   \brief removes cycles in hyper-graph
   \param out table mapping hyper-nodes to the list of outgoing edges 
   \param super table mapping hyper-nodes to the list of containing
   hyper-nodes
   \param visited table registering visited hyper-nodes
   \param removed table registering removed hyper-edges
   \return the interesting information is registered in parameter
   <b>removed</b> */
static void
remove_cycles_aux(Ttable out, Ttable super, Ttable visited, Ttable removed)
{
  Ttable stack;
  unsigned i;
  stack = table_new(table_length(out), 1);
  for (i = 0; i < table_length(visited); ++i)
    {
      if (!table_get(visited, i))
	do 
	  {
	    if (!remove_cycles_rec(i, stack, out, super, visited, removed))
	      break;
	  }
	while(1);
    }
  table_free(&stack);
}

/*--------------------------------------------------------------*/

/*
  nodes contains the vertices of a strongly connected component
  in the dependency graph.

  The result shall be cycle-free. Edges represent an
  equality/equivalence in the original formula. Such definitions
  may be represented by several edges. If one edge of a definition
  is a removed, all need to be removed. The original dependency
  graph is therefore not suitable.

  Instead we build a second graph where each node represent a set of
  variables; those nodes are called h-nodes. There is two kinds of
  edges between h-nodes: super-edges and out-edges.  There is a
  super-edge from h1 to h2 if h2 is a superset of h1.  There is an
  out-edge from h1 to h2 if there is a definition where the defined
  constant is in h1, and h2 is the set of variables in the definition of
  that constant.
  
  The code below builds that graph and removes the cycles found in the
  graph. Note that in any cycle there is at least one out-edge.

  The cycle detection and removal is sub-optimal. It is a DFS looking
  for a cycle. When one such cycle has been found, one out-edge is
  marked as removed. The process is repeated until all h-nodes have
  been visited and all cycles have been removed.
*/
static void
remove_cycles(Tstack_DAG nodes)
{
  unsigned size = stack_size(nodes);
  unsigned i, j;
  Ttable  table_hnodes;  /* hyper-node: set of hyper-nodes */
  Ttable  table_out;     /* hyper-node: list of outgoing edges */
  Ttable  table_super;   /* hyper-node: list of containing hyper-nodes */
  Ttable  table_visited; /* hyper-node: has been visited */
  Ttable  table_removed; /* hyper-edge: has been removed */
  Tbs_mgr mgr;
  int *   Pmisc;

#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("remove_cycles\n");
  for (i = 0; i < size; ++i)
    {
      TDAG DAG = stack_get(nodes, i);
      Tlist list;
      my_DAG_message("\t%D\n", DAG);
      list = (Tlist) DAG_Pflag(DAG);
      LIST_LOOP_BEGIN(list, void *, P);
      {
        TDAG DAG2 = DAG_ptr_of(P);
        my_DAG_message("\t\t=>%D\n", DAG2);
      }
      LIST_LOOP_END(list);
    }
#endif
  MY_MALLOC(Pmisc, size * sizeof(int));
  for (i = 0; i < size; ++i)
    {
      TDAG node = stack_get(nodes, i);
      Pmisc[i] = DAG_misc(node);
      DAG_misc_set(node, (int)(i + 1));
      assert(DAG_flag(node) == 0);
      DAG_flag_set(node, 1);
    }
  table_hnodes = table_new(2 * size, 1);
  table_out = table_new(2 * size, 1);
  table_super = table_new(2 * size, 1);
  table_visited = table_new(2 * size, 1);
  table_removed = table_new(size, 1);

  mgr  = bitset_new_manager(size, DAG_index);
  for (i = 0; i < stack_size(nodes); ++i)
    {
      Tbs s = bitset_new(mgr);
      bitset_insert(mgr, s, DAG_ptr_of(stack_get(nodes, i)));
      table_push(table_hnodes, s);
      table_push(table_out, NULL);
      table_push(table_removed, NULL);
    }
  for (i = 0; i < stack_size(nodes); ++i)
    {
      Tbs s;
      Tlist list;
      unsigned src;
      s = bitset_new(mgr);
      list = DAG_Pflag(stack_get(nodes, i));
      if (list)
	{
	  LIST_LOOP_BEGIN(list, void *, P);
          {
            TDAG DAG = DAG_of_ptr(P);
	    if (DAG_flag(DAG))
	      bitset_insert(mgr, s, DAG_ptr_of(DAG));
          }
	  LIST_LOOP_END(list);
	  src = hypernode_add(mgr, s, table_hnodes);
	  if (src < table_length(table_out))
	    table_set(table_out, src, (void *)
		      list_add(table_get(table_out, src), PTR_OF_INT(i)));
	  else
	    table_push(table_out, list_cons(PTR_OF_INT(i), NULL));
	}
      assert(table_length(table_out) == table_length(table_hnodes));
    }
  for (i = 0; i < size; ++i)
    DAG_flag_set(stack_get(nodes, i), 0);
  for (i = 0; i < table_length(table_hnodes); ++i)
    {
      table_push(table_super, NULL);
      for (j = i + 1; j < table_length(table_hnodes); ++j)
	{
	  Tbs si, sj;
	  si = table_get(table_hnodes, i);
	  sj = table_get(table_hnodes, j);
	  if (bitset_subseteq(mgr, si, sj))
	    table_set(table_super, i,
		      list_add(table_get(table_super, i), 
			       (void *) (intptr_t) j));
	  else if (bitset_subseteq(mgr, sj, si))
	    table_set(table_super, j,
		      list_add(table_get(table_super, j), 
			       (void *) (intptr_t) i));
	}
    }
  for (i = 0; i < table_length(table_hnodes); ++i)
    table_push(table_visited, NULL);

  for (i = 0; i < table_length(table_hnodes); ++i)
    bitset_free(mgr, (Tbs) table_get(table_hnodes, i));
  table_free(&table_hnodes);
  bitset_free_manager(&mgr);

  remove_cycles_aux(table_out, table_super, table_visited, table_removed);

  for (i = 0; i < table_length(table_removed); ++i)
    if (table_get(table_removed, i))
      list_free((Tlist*)&DAG_Pflag(stack_get(nodes, i)));

  for (i = 0; i < table_length(table_out); ++i)
    {
      Tlist list = (Tlist) table_get(table_out, i);
      list_free(&list);
    }
  table_free(&table_out);
  for (i = 0; i < table_length(table_super); ++i)
    {
      Tlist list = (Tlist) table_get(table_super, i);
      list_free(&list);
    }
  table_free(&table_super);
  table_free(&table_visited);
  table_free(&table_removed);

  for (i = 0; i < size; ++i)
    {
      TDAG node = stack_get(nodes, i);
      assert(DAG_misc(node) == (int)(i + 1));
      DAG_misc_set(node, Pmisc[i]);
    }
  free(Pmisc);
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

TDAG
simplify_formula_sat(TDAG src)
{
  Tstack_DAG table_lhs = NULL;
  Tstack_DAG table_rhs = NULL;
  TDAG   dest;
  Tstack_DAG order = NULL;
  unsigned i, nb, nb_substs;
  Tlist list_SCC;
  TDAG  *origin, *subst;
#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("simplify_formula_sat input: %D\n", src);
#endif
  stack_INIT(table_lhs);
  stack_INIT(table_rhs);
  stack_push(table_lhs, DAG_NULL);
  stack_push(table_rhs, DAG_NULL);
  /* for each def (xi, ti), stores xi in table_lhs ti in table_rhs */
  /* assign xi's misc to a unique id consecutively numbered from 1 */
  /* DAG_misc(xi) == i iff table_lhs(i) == xi */
  simplify_collect_rewrite2(src, 1, &table_lhs, &table_rhs);
  if (stack_size(table_lhs) == 1)
    {
      stack_free(table_lhs);
      stack_free(table_rhs);
#ifdef DEBUG_SIMP_FORMULA_SAT
      my_DAG_message("simplify_formula_sat output: %D\n", src);
#endif
      return src;
    }
  /* gets all candidate substitutions */
  nb = stack_size(table_lhs) - 1;
  nb_substs = 0;
  MY_MALLOC(origin, nb * sizeof(TDAG));
  MY_MALLOC(subst, nb * sizeof(TDAG));

#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("Defs:\n");
  for (i = 1; i <= nb; ++i)
    my_DAG_message("\t%D = %D\n", stack_get(table_lhs, i),
		   stack_get(table_rhs, i));
#endif

  /* for each (xi, ti), set xi's Pflag to the list of xij in ti */
  for (i = 1; i <= nb; ++i)
    {
      TDAG lhs = stack_get(table_lhs, i);
      TDAG rhs = stack_get(table_rhs, i);
      collect_edges(&lhs, &rhs);
      if (DAG_Pflag(lhs))
	continue;
      origin[nb_substs] = lhs;
      subst[nb_substs] = DAG_dup(rhs);
      ++nb_substs;
    }

#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("Edges:\n");
  for (i = 1; i <= nb; ++i)
    {
      TDAG DAG = stack_get(table_lhs, i);
      Tlist edges = DAG_Pflag(DAG);
      my_DAG_message("%D\n", DAG);
      LIST_LOOP_BEGIN(edges, void *, P);
      {
	TDAG DAG2 = DAG_of_ptr(P);
	my_DAG_message("\t=>\t%D\n", DAG2);
      }
      LIST_LOOP_END(edges);
    }
#endif

  /* build list of strongly connected component in the dependency 
     graph */
  list_SCC = tarjan_scc(table_lhs);

#ifdef DEBUG_SIMP_FORMULA_SAT
  LIST_LOOP_BEGIN(list_SCC, Tstack_DAG, SCC);
  {
    int j;
    my_DAG_message("SCC: \n");
    for (j = 0; j < stack_size(SCC); ++j)
      my_DAG_message("\t%D\n", stack_get(SCC, j));
    my_DAG_message("\n");
  }
  LIST_LOOP_END(list_SCC);
#endif

  LIST_LOOP_BEGIN(list_SCC, Tstack_DAG, SCC);
  if (stack_size(SCC) > 1)
    remove_cycles(SCC);
  stack_free(SCC);
  LIST_LOOP_END(list_SCC);
  list_free(&list_SCC);

  stack_INIT(order);
  topological_sort(table_lhs, &order);

#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("Order:\n");
  for (i = 0; i < stack_size(order); ++i)
    my_DAG_message("\t%D = %D\n", stack_get(order, i),
		   stack_get(table_rhs, DAG_misc(DAG1)));
#endif


#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("Edges:\n");
  for (i = 1; i <= nb; ++i)
    {
      TDAG DAG = stack_get(table_lhs, i);
      Tlist edges = DAG_Pflag(DAG);
      my_DAG_message("%D\n", DAG);
      LIST_LOOP_BEGIN(edges, void *, P);
      {
	TDAG DAG2 = DAG_of_ptr(P);
	my_DAG_message("\t=>\t%D\n", DAG2);
      }
      LIST_LOOP_END(edges);
    }
#endif

  /* perform substitutions in correct order */
  for (i = 0; i < stack_size(order); ++i)
    if (DAG_Pflag(stack_get(order, i)))
      {
	TDAG target = stack_get(order, i);
	TDAG source = stack_get(table_rhs, DAG_misc(target));
	list_free((Tlist *) &DAG_Pflag(target));
	origin[nb_substs] = target;
	subst[nb_substs] = 
	  DAG_dup(DAG_subst_multiple(source, nb_substs, origin, subst));
	++nb_substs;
      }
  STAT_INC(subst);
#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("Subst:\n");
  for (i = 0; i < nb_substs; ++i)
    {
      my_DAG_message("\t%D := %D\n", origin[i], subst[i]);
    }
#endif

  dest = DAG_dup(DAG_subst_multiple(src, nb_substs, origin, subst));
  for (i = 0; i < nb_substs; ++i)
    DAG_free(subst[i]);
  free(origin);
  free(subst);

  for (i = 1; i < stack_size(table_lhs); ++i)
    {
      TDAG vertex = stack_get(table_lhs, i);
      DAG_misc_set(vertex, 0);
      list_free((Tlist *) &DAG_Pflag(vertex));
    }
  stack_free(order);
  DAG_free(src);
  stack_free(table_lhs);
  stack_free(table_rhs);
#ifdef DEBUG_SIMP_FORMULA_SAT
  my_DAG_message("simplify_formula_sat output: %D\n", dest);
#endif
  return dest;
}

