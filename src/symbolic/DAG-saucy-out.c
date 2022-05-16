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


#include "statistics.h"

#include "DAG.h"
#include "DAG-tmp.h"

#include "DAG-saucy-out.h"
#include "saucy.h"
#include "amorph.h"

/* #define DEBUG_SAUCY */
#define COMPLETE_SYM

#ifdef DEBUG_SAUCY
#include "DAG-print.h"
#endif

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
static Tstack_unsigned symbs;

/**
   \brief store symbol associated to node */
static Tstack_symb node_to_symb;

/**
   \brief node data structure */
typedef struct Tnode
{
  unsigned type;
  unsigned symb;
#ifdef COMPLETE_SYM
  TDAG DAG;
#endif
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

/* Stats are global so we can print them from the signal handler */
static struct saucy_stats stats;
#if 0
static char *marks;    /* "Bit" vector for printing */
#endif

#define COLOR_ARGPOS 0

/* #define DIRECTLY_LINK_FIRST_ARGUMENT */
#define INTRODUCE_BOTH_POL

static unsigned sym_time, sym_gen, sym_size, sym_exp, sym_nosymb;

/*--------------------------------------------------------------*/

static void
DAG_to_graph_aux(TDAG DAG)
{
  unsigned i;
  Tnode *Pnode;
  Tedge *Pedge;
  if (DAG_tmp_unsigned[DAG])
    return;
  for (i = 0; i < DAG_arity(DAG); i++)
   DAG_to_graph_aux(DAG_arg(DAG, i));
  stack_inc(nodes);
  Pnode = &stack_top(nodes);
  Pnode->symb = 0;
  Pnode->type = DAG_sort(DAG);
#ifdef COMPLETE_SYM
  Pnode->DAG = DAG;
#endif
  DAG_tmp_unsigned[DAG] = stack_size(nodes);
#ifdef DEBUG_SAUCY
  my_DAG_message("Assign %d to %D\n", DAG_tmp_unsigned[DAG], DAG);
#endif
  /*
  if (stack_size(nodes) == 134 ||
      stack_size(nodes) == 181)
    my_DAG_message("%d : %D\n", stack_size(nodes) - 1, DAG);
  */
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
#ifdef COMPLETE_SYM
      Pnode->DAG = DAG_NULL;
#endif
      stack_set(symbs, DAG_symb(DAG), stack_size(nodes));
    }
  /* Add an edge to the symbol */
  stack_inc(edges);
  Pedge = &stack_top(edges);
  Pedge->src = DAG_tmp_unsigned[DAG];
  Pedge->dest = stack_get(symbs, DAG_symb(DAG));
#ifdef DEBUG_SAUCY
  my_DAG_message("(%d %d) symbol\n", Pedge->src, Pedge->dest);
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
#ifdef DEBUG_SAUCY
          my_DAG_message("(%d %d) arity %d\n", Pedge->src, Pedge->dest, i);
#endif
	}
      return;
    }
  /* For non symmetric symbols path length increases with arg position */
#ifdef DIRECTLY_LINK_FIRST_ARGUMENT
  stack_inc(edges);
  Pedge = &stack_top(edges);
  Pedge->src = DAG_tmp_unsigned[DAG];
  Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, 0)];
#ifdef DEBUG_SAUCY
  my_DAG_message("(%d %d) directly link first argument\n", Pedge->src, Pedge->dest);
#endif
  for (i = 1; i < DAG_arity(DAG); i++)
    {
      stack_inc(edges);
      Pedge = &stack_top(edges);
      stack_inc(nodes);
      Pnode = &stack_top(nodes);
      Pnode->type = COLOR_ARGPOS;
      Pnode->symb = 0;
#ifdef COMPLETE_SYM
      Pnode->DAG = DAG_NULL;
#endif
      Pedge->src = (i == 1)?DAG_tmp_unsigned[DAG]:(stack_size(nodes) - 1);
      Pedge->dest = stack_size(nodes);
#ifdef DEBUG_SAUCY
      my_DAG_message("(%d %d)\n", Pedge->src, Pedge->dest);
#endif
      stack_inc(edges);
      Pedge = &stack_top(edges);
      Pedge->src = stack_size(nodes);
      Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, i)];
#ifdef DEBUG_SAUCY
      my_DAG_message("(%d %d)\n", Pedge->src, Pedge->dest);
#endif
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
#ifdef COMPLETE_SYM
      Pnode->DAG = DAG_NULL;
#endif
      Pedge->src = (!i)?DAG_tmp_unsigned[DAG]:(stack_size(nodes) - 1);
      Pedge->dest = stack_size(nodes);
      stack_inc(edges);
#ifdef DEBUG_SAUCY
       my_DAG_message("(%d %d) arity %d (linking node)\n", Pedge->src, Pedge->dest, i);
#endif
      Pedge = &stack_top(edges);
      Pedge->src = stack_size(nodes);
      Pedge->dest = DAG_tmp_unsigned[DAG_arg(DAG, i)];
#ifdef DEBUG_SAUCY
      my_DAG_message("(%d %d) arity %d\n", Pedge->src, Pedge->dest, i);
#endif
    }
#endif
}

/*--------------------------------------------------------------*/

static void
DAG_to_graph(TDAG DAG)
{
  DAG_tmp_reserve();
  if (DAG_symb(DAG) == CONNECTOR_AND && DAG_arity(DAG) == 1)
    DAG = DAG_arg0(DAG);
  nb_colors = stack_size(DAG_sort_stack);
  DAG_to_graph_aux(DAG);
  DAG_tmp_reset_unsigned(DAG);
  DAG_tmp_release();
}

/*--------------------------------------------------------------*/

static int
edge_compare(Tedge * Pedge1, Tedge * Pedge2)
{
  return (Pedge1->src == Pedge2->src)?
    ((int)Pedge1->dest-(int)Pedge2->dest):
    ((int)Pedge1->src-(int)Pedge2->src);
}

/*--------------------------------------------------------------*/

static void
eliminate_duplicate_edges(void)
{
  unsigned i, j;
  qsort(edges->data, edges->size, sizeof(Tedge), (TFcmp) edge_compare);
  for (i = 1, j = 0; i < edges->size; i++)
    if (edges->data[j].src != edges->data[i].src ||
	edges->data[j].dest != edges->data[i].dest)
      edges->data[++j] = edges->data[i];
  edges->size = j;
}

/*--------------------------------------------------------------*/

static void
print_automorphism(int n, const int *gamma, int nsupp, const int *support,
		   struct amorph_graph *g, char *marks)
{
  int i, j, k;
  /* We presume support is already sorted */
  for (i = 0; i < nsupp; ++i)
    {
      k = support[i];
      /* Skip elements already seen */
      if (marks[k]) continue;
      /* Start an orbit */
      marks[k] = 1;
      printf("(%d", k);
      /* Mark and notify elements in this orbit */
      for (j = gamma[k]; j != k; j = gamma[j])
	{
	  marks[j] = 1;
	  printf(" %d", j);
	}
      /* Finish off the orbit */
      putchar(')');
    }
  putchar('\n');
  /* Clean up after ourselves */
  for (i = 0; i < nsupp; ++i)
    marks[support[i]] = 0;
}

/*--------------------------------------------------------------*/

static void
amorph_graph_free(struct amorph_graph *g)
{
  free(g->sg.adj);
  free(g->sg.edg);
  free(g->colors);
  free(g);
}

/*--------------------------------------------------------------*/

/*
static int
integer_compare(const void *a, const void *b)
{
  return *(int *)a - *(int *)b;
}
*/

typedef Tstack_symb Tsymmetry;

TSstack(_symmetry, Tsymmetry);

Tstack_symmetry generators = NULL;

/*--------------------------------------------------------------*/

static int
on_automorphism(int n, const int *gamma, int k, int *support, void *arg)
{
  unsigned i;
  Tsymmetry symmetry;
#ifdef PEDANTIC
  printf("%d, %p\n", n, arg);
#endif
  stack_INIT(symmetry);
  for (i = 0; i < (unsigned) k; i++)
    if (stack_get(node_to_symb, support[i]))
      {
	stack_push(symmetry, stack_get(node_to_symb, support[i]));
	stack_push(symmetry, stack_get(node_to_symb, gamma[support[i]]));
      }
  if (stack_size(symmetry))
    stack_push(generators, symmetry);
  else
    {
      stats_counter_inc(sym_nosymb);
      stack_free(symmetry);
    }
  /* struct amorph_graph *g = arg; */
  /* qsort(support, k, sizeof(int), integer_compare); */
#ifdef DEBUG_SAUCY
  printf("symmetry found:\n");
  for (i = 0; i < (unsigned) k; i++)
    if (stack_get(node_to_symb, support[i]))
      printf("  %s -> %s\n",
             DAG_symb_name(stack_get(node_to_symb, support[i])),
             DAG_symb_name(stack_get(node_to_symb, gamma[support[i]])));
#ifdef COMPLETE_SYM
    else if (stack_get(nodes, support[i] - 1).DAG)
      {
	printf("  ");
	DAG_print(stack_get(nodes, support[i] - 1).DAG);
	printf(" -> ");
	DAG_print(stack_get(nodes, gamma[support[i]] - 1).DAG);
	printf("\n");
      } 
#endif
#endif
  /*  g->consumer(n, gamma, k, support, g, marks); */
  return 1;
}

/*--------------------------------------------------------------*/

static struct amorph_graph *
create_saucy_graph(int directed)
{
  struct amorph_graph *g = NULL;
  unsigned i, n, m, e;
  int  val, *adjo, *adji, *edg, *colors;
  Tstack_unsigned color_tsl;
  /* Set to NULL to simplify freeing in error path */
  adjo = edg = colors = NULL;;
  /* Allocate amorph struct */
  MY_MALLOC(g, sizeof(struct amorph_graph));
  /* Allocate nodes */
  n = stack_size(nodes) + 1;
  m = (n + 1) * (directed? 2 : 1);
  MY_MALLOC(adjo, m * sizeof(int));
  /* Initialize for nodes in no edge, in particular 0
     and position n, kept for sum of edges */
  memset(adjo, 0, m * sizeof(int));
  adji = adjo + (directed ? n + 1 : 0);
  /* Allocate edges */
  e = stack_size(edges);
  MY_MALLOC(edg, 2 * e * sizeof(int));
  /* Allocate colors */
  MY_MALLOC(colors, n * sizeof(int));
  memset(colors, 0, n * sizeof(int));
  if (!g || !adjo || !edg || !colors)
    {
      free(g);
      free(colors);
      free(adjo);
      free(edg);
      return NULL;
    }
  /* Count edges per node */
  for (i = 0; i < e; i++)
    {
      /* Edge a --> b should add a to input of b, so adji[b]++, and adjo[a]++ */
      ++adjo[stack_get(edges, i).src];
      ++adji[stack_get(edges, i).dest];
    }
#ifdef DEBUG_SAUCY
  for (i = 0; i < m; i++)
    printf("%s%d", i?", ":"[", adjo[i]);
  printf("]\n");
#endif
  assert(adji[n] == 0);
  assert(adjo[n] == 0);
  /* Translate adj values to real locations */
  for (val = 0, i = 0; i < m; i++)
    {
      int tmp = adjo[i];
      adjo[i] = val;
      val += tmp;
      assert(!i || adjo[i - 1] <= adjo[i]);
    }
  assert(adji[n] == 2 * (int) e);
  assert(adjo[n] == directed?e:2*e);
  assert(!directed || adji[0] == (int)e);
  /* Store edges in edg */
  for (i = 0; i < e; i++)
    {
      edg[adji[stack_get(edges, i).dest]++] = (int) stack_get(edges, i).src;
      edg[adjo[stack_get(edges, i).src]++] = (int) stack_get(edges, i).dest;
    }
#ifdef DEBUG_SAUCY
  for (i = 0; i < m; i++)
    printf("%s%d", i?", ":"[", adjo[i]);
  printf("]\n");
#endif
  /* Translate again-broken sizes to adj values */
  assert(adjo[n] == adjo[n - 1]);
  assert(adji[n] == adji[n - 1]);
  for (val = 0, i = 0; i < m; i++)
    SWAP(int, val, adjo[i]);
  if (directed)
    for (i = 0; i < n + 1; i++)
      adji[i] -= (int) e;
#ifdef DEBUG_SAUCY
  for (i = 0; i < m; i++)
    printf("%s%d", i?", ":"[", adjo[i]);
  printf("]\n");
#endif
  /* Store colors */
  stack_INIT_s(color_tsl, nb_colors);
  stack_resize(color_tsl, nb_colors);
  nb_colors = 0;
  for (i = 1; i < n; i++)
    {
      Tnode *Pnode = &stack_get(nodes, i - 1);
      assert(Pnode->type < stack_size(color_tsl));
      if (Pnode->type && !color_tsl->data[Pnode->type])
	color_tsl->data[Pnode->type] = ++nb_colors;
      colors[i] = (int) color_tsl->data[Pnode->type];
    }
  stack_free(color_tsl);
  /* Graph data */
  g->sg.n = (int) n;
  g->sg.e = (int) e;
  g->sg.adj = adjo;
  g->sg.edg = edg;
  g->colors = colors;
#ifdef DEBUG_SAUCY
  for (i = 0; i < n; i++)
    {
      int j;
      for (j = adjo[i]; j < adjo[i + 1]; j++)
        printf("%d %d\n", i, edg[j]);
    }
  for (i = 0; i < n; i++)
    printf("%s%d", i?", ":"", colors[i]);
  printf("\n");
#endif
  /* Amorph functions */
  g->consumer = print_automorphism;
  g->free = amorph_graph_free;
  g->stats = NULL;
  /* g->data = info; */
  return g;
}

/*--------------------------------------------------------------*/

static void
print_generators(Tstack_symmetry * Pgenerators)
{
  unsigned i, j;
  Tstack_bool(mark);
  Tstack_symb(image);
  stack_INIT(mark);
  stack_INIT(image);
  stack_resize(mark, stack_size(DAG_symb_stack));
  stack_resize(image, stack_size(DAG_symb_stack));
  for (i = 0; i < stack_size(*Pgenerators); i++)
    {
      Tsymmetry * Psymmetry = &stack_get(*Pgenerators, i);
      for (j = 0; j < stack_size(*Psymmetry); j += 2)
	stack_set(image, stack_get(*Psymmetry, j),
		  stack_get(*Psymmetry, j + 1));
      for (j = 0; j < stack_size(*Psymmetry); j += 2)
	if (!stack_get(mark, stack_get(*Psymmetry, j)))
	  {
	    Tsymb tmp, symb = stack_get(*Psymmetry, j);
	    printf("(%s", DAG_symb_name(symb));
	    tmp = symb;
	    while ((tmp = stack_get(image, tmp)) != symb)
	      {
		stack_set(mark, tmp, true);
		printf(" %s", DAG_symb_name(tmp));
	      }
	    printf(")");
	  }
      for (j = 0; j < stack_size(*Psymmetry); j++, j++)
	stack_set(mark, stack_get(*Psymmetry, j), false);
      printf("\n");
    }
  stack_free(image);
  stack_free(mark);
}

/*--------------------------------------------------------------*/

void
DAG_search_automorphisms(TDAG DAG)
{
  Tsymb i;
  struct saucy *s;
  struct amorph_graph *g = NULL;
  int digraph_mode = 1;
  /* Create graph from DAG representation */
  stats_timer_start(sym_time);
  stack_INIT(nodes);
  stack_INIT(edges);
  stack_INIT(symbs);
  stack_INIT(generators);
  stack_resize(symbs, stack_size(DAG_symb_stack));
  DAG_to_graph(DAG);
  stack_INIT(node_to_symb);
  stack_resize(node_to_symb, stack_size(nodes) + 1);
  for (i = 0; i < stack_size(symbs); i++)
    if (stack_get(symbs, i))
      stack_set(node_to_symb, stack_get(symbs, i), i);
  eliminate_duplicate_edges();
  /* safeguard for corner cases */
  if (stack_size(nodes) <= 2 || stack_size(edges) < 2)
    return;
  /* Create saucy graph */
  g = create_saucy_graph(digraph_mode);
  /* Allocate saucy space */
  if (!(s = saucy_alloc(g->sg.n)))
    my_error("saucy initialization failed");
  /* /\* Set up the alarm for timeouts *\/ */
  /* if (timeout > 0) { */
  /*   platform_set_timer(timeout, timeout_handler); */
  /* } */

  /* Print statistics when signaled */
  /* platform_set_user_signal(stats_handler); */

  /* Start timing */
  /* cpu_time = platform_clock(); */

  /* Run the search */
  saucy_search(s, &g->sg, digraph_mode, g->colors,
	       on_automorphism, NULL, &stats);
  /* Finish timing */
  /* cpu_time = platform_clock() - cpu_time; */

  /* if (gap_mode && !quiet_mode) printf("\n]\n"); */

  /* /\* Warn if timeout *\/ */
  /* if (timeout_flag) warn("search timed out"); */

  /* /\* Print out stats if requested *\/ */
  /* if (stats_mode) { */
  /*   fflush(stdout); */
  /*   f = quiet_mode ? stdout : stderr; */
  /*   fprintf(f, "input file = %s\n", filename); */
  /*   if (g->stats) g->stats(g, f); */
  /*   fprintf(f, "vertices = %d\n", n); */
  /*   fprintf(f, "edges = %d\n", g->sg.e); */
  /*   print_stats(f); */
  /*   fprintf(f, "cpu time (s) = %.2f\n", */
  /* 	    divide(cpu_time, PLATFORM_CLOCKS_PER_SEC)); */
  /* } */

  /* Cleanup */
#ifdef DEBUG_SAUCY
  printf("Grpsize_base: %f\n", stats.grpsize_base);
  printf("Grpsize_exp: %d\n", stats.grpsize_exp);
  printf("Levels: %d\n", stats.levels);
  printf("Nodes: %d\n", stats.nodes);
  printf("Bads: %d\n", stats.bads);
  printf("Gens: %d\n", stats.gens);
  printf("Support: %d\n", stats.support);
#endif
  saucy_free(s);
  g->free(g);
  stack_free(symbs);
  stack_free(nodes);
  stack_free(edges);
#ifdef DEBUG_SAUCY
  for (i = 0; i < stack_size(generators); i++)
    {
      unsigned j;
      Tsymmetry symmetry = stack_get(generators, i);
      printf("Symmetry:\n");
      for (j = 0; j < stack_size(symmetry); j++, j++)
	printf("  %s -> %s\n",
	       DAG_symb_name(stack_get(symmetry, j)),
	       DAG_symb_name(stack_get(symmetry, j + 1)));
    }
#endif
  print_generators(&generators);
  stats_timer_stop(sym_time);
  stats_counter_set(sym_gen, stack_size(generators));
  for (i = 1; stats.grpsize_exp && stats.grpsize_base * i < 1000000;
       i *= 10, stats.grpsize_exp--) ;
  stats_counter_set(sym_size, (int)(stats.grpsize_base * i));
  stats_counter_set(sym_exp, stats.grpsize_exp);
  for (i = 0; i < stack_size(generators); i++)
    stack_free(stack_get(generators, i));
  stack_free(generators);
  stack_free(node_to_symb);
}

/*--------------------------------------------------------------*/

void
symmetry_init(void)
{
  sym_time =
    stats_timer_new("sym_time", "Time for finding symmetry", "%7.2f", STATS_TIMER_ALL);
  sym_gen =
    stats_counter_new("sym_gen", "Number of symmetry generators", "%6d");
  sym_size =
    stats_counter_new("sym_size", "Mantissa for group symmetry size", "%7d");
  sym_exp =
    stats_counter_new("sym_exp", "Exponant for group symmetry size", "%4d");
  sym_nosymb =
    stats_counter_new("sym_nosymb", "Generators without permutation of symbols", "%4d");    
}

/*--------------------------------------------------------------*/

void
symmetry_done(void)
{
}


