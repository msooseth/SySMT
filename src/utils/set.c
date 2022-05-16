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
  set data structure
  --------------------------------------------------------------
*/

#include "general.h"

#include "set.h"

typedef struct TSnode * Tnode;

struct TSnode
{
  void *  value;
  Tnode   left;
  Tnode   right;
  Tsigned balance;
};

struct TSset
{
  Tnode     root;
  Tunsigned size;
  TFcmp     sort_function;
  TFfree    free_function;
};

/*--------------------------------------------------------------*/

Tset
set_new (TFcmp sort_function, TFfree free_function)
{
  Tset result;
  MY_MALLOC(result, sizeof(struct TSset));
  result->root = NULL;
  result->size = 0;
  result->sort_function = sort_function;
  result->free_function = free_function;
  return result;
}

/*--------------------------------------------------------------*/

static TFfree free_function = NULL;

static void 
node_free_1 (Tnode node)
{
  if (node == NULL) return;
  free_function(node->value);
  node_free_1(node->left);
  node_free_1(node->right);
  free(node);
}

/*--------------------------------------------------------------*/

static void 
node_free_2 (Tnode node)
{
  if (node == NULL) return;
  node_free_2(node->left);
  node_free_2(node->right);
  free(node);
}

/*--------------------------------------------------------------*/

void 
set_free (Tset * Pset)
{
  if ((*Pset)->free_function)
    {
      free_function = (*Pset)->free_function;
      node_free_1((*Pset)->root);
    }
  else
    node_free_2((*Pset)->root);
  free(*Pset);
  *Pset = NULL;
}

/*--------------------------------------------------------------*/

void 
set_erase (Tset set)
{
  if (set->free_function)
    {
      free_function = set->free_function;
      node_free_1(set->root);
    }
  else
    node_free_2(set->root);
  set->root = NULL;
  set->size = 0;
}

/*--------------------------------------------------------------*/

bool
set_empty (Tset set)
{
  return set->root == NULL;
}

/*--------------------------------------------------------------*/

Tunsigned
set_size (Tset set)
{
  return set->size;
}

/*--------------------------------------------------------------*/

static TFapply apply_function = NULL;

static void
apply_node_aux (Tnode node)
{
  if (node->left) apply_node_aux (node->left);
  apply_function (node->value);
  if (node->right) apply_node_aux (node->right);
}

/*--------------------------------------------------------------*/

void 
set_apply (Tset set, TFapply fun)
{
  if (set->root)
    {
      apply_function = fun;
      apply_node_aux(set->root);
      apply_function = NULL;
    }
}

/*--------------------------------------------------------------*/

#if 0
static int
sanity_check(const Tnode node)
{
  int left, right;
  if (node == NULL) return 0;
  left = sanity_check(node->left);
  right = sanity_check(node->right);
  assert(node->balance == right - left);
  return (left > right ? left : right) + 1;
}
#endif

/*--------------------------------------------------------------*/

static Tlist  
node_list (const Tnode Pnode)
{
  if (Pnode == NULL) return NULL;
  else
    return list_merge (node_list (Pnode->left), 
		       list_cons (Pnode->value, node_list (Pnode->right)));
}

/*--------------------------------------------------------------*/

Tlist  
set_list (Tset set)
{
  return node_list (set->root);
}

/*--------------------------------------------------------------*/

static void
rotate_left_simple (Tnode * Pnode)
{
  Tnode n = *Pnode;
  Tnode r = n->right;
  *Pnode = r;
  n->right = r->left;
  n->balance = (r->balance == 0) ? 1 : 0;
  r->left = n;
  r->balance = (r->balance == 0) ? -1 : 0;
}

/*--------------------------------------------------------------*/

static void
rotate_right_simple (Tnode * Pnode)
{
  Tnode n = *Pnode;
  Tnode l = n->left;
  *Pnode = l;
  n->left = l->right;
  n->balance = (l->balance == 0) ? -1 : 0;
  l->right = n;
  l->balance = (l->balance == 0) ? 1 : 0;
}

/*--------------------------------------------------------------*/

static void
rotate_left_double (Tnode * Pnode)
{
  Tnode n = *Pnode;
  Tnode r = n->right;
  Tnode rl = r->left;
  *Pnode = rl;
  n->right = rl->left;
  n->balance = rl->balance <= 0 ? 0 : -1;
  r->left = rl->right;
  r->balance = rl->balance >= 0 ? 0 : 1;
  rl->right = r;
  rl->left = n;
  rl->balance = 0;
}

/*--------------------------------------------------------------*/

static void
rotate_right_double (Tnode * Pnode)
{
  Tnode n = *Pnode;
  Tnode l = n->left;
  Tnode lr = l->right;
  *Pnode = lr;
  n->left = lr->right;
  n->balance = lr->balance >= 0 ? 0 : 1;
  l->right = lr->left;
  l->balance = lr->balance <= 0 ? 0 : -1;
  lr->left = l;
  lr->right = n;
  lr->balance = 0;
}

/*--------------------------------------------------------------*/

static void * _value;
static TFcmp _sort_function;
static int _done;

static int 
node_insert (Tnode * Pnode)
{
  if (*Pnode == NULL)
    {
      MY_MALLOC(*Pnode, sizeof(struct TSnode));
      (*Pnode)->value = _value;
      (*Pnode)->left = NULL;
      (*Pnode)->right = NULL;
      (*Pnode)->balance = 0;
      _done = 1;
      return 1;
    }
  else
    {
      int compare = _sort_function (_value, (*Pnode)->value);
      if (compare == 0) return 0;
      if (node_insert (compare < 0 ? &((*Pnode)->left) : &((*Pnode)->right)))
	{
	  if (compare < 0) /* insertion was in left sub-tree */
	    {
	      if ((*Pnode)->balance == 0) 
		{
		  (*Pnode)->balance = -1;
		  return 1;
		}
	      else if ((*Pnode)->balance == 1)
		{
		  (*Pnode)->balance = 0;
		  return 0;
		}
	      else
		{
		  if ((*Pnode)->left->balance == -1)
		    rotate_right_simple (Pnode);
		  else
		    rotate_right_double (Pnode);
		  return 0;
		}
	    }
	  else /* insertion was in right sub-tree */
	    {
	      if ((*Pnode)->balance == 0)
		{
		  (*Pnode)->balance = 1;
		  return 1;
		}
	      else if ((*Pnode)->balance == -1)
		{
		  (*Pnode)->balance = 0;
		  return 0;
		}
	      else
		{
		  if ((*Pnode)->right->balance == 1)
		    rotate_left_simple (Pnode);
		  else
		    rotate_left_double (Pnode);
		  return 0;
		}
	    }
	}
      else
	{
	  return 0;
	}
    }
}

/*--------------------------------------------------------------*/

int 
set_insert (Tset set, void * value)
{
  _value = value;
  _sort_function = set->sort_function;
  _done = 0;
  node_insert (& (set->root));
  if (_done) set->size += 1;
#if 0
  sanity_check(set->root);
#endif
  return _done;
}

/*--------------------------------------------------------------*/

/* DD returns 0 if *Pnode height came back to original value after restore,
   a non-null value otherwise */
static int 
restore_left (Tnode * Pnode)
{
  if (*Pnode == NULL) return 1;
  switch((*Pnode)->balance)
    {
    case 1:
      if ((*Pnode)->right->balance >= 0)
	{
	  rotate_left_simple (Pnode);
	  return (*Pnode)->balance == 0;
	}
      else
	{
	  rotate_left_double (Pnode);
	  return 1;
	}
    case 0:
      (*Pnode)->balance = 1;
      return 0;
    case -1:
      (*Pnode)->balance = 0;
      return 1;
    default:
      assert(0); /* dead code */
    }
  assert(0); /* dead code */
  return 0;
}

/*--------------------------------------------------------------*/

/* DD returns 0 if *Pnode height came back to original value after restore,
   a non-null value otherwise */
static int
restore_right (Tnode * Pnode)
{
  if (*Pnode == NULL) return 1;
  switch((*Pnode)->balance)
    {
    case -1:
      if ((*Pnode)->left->balance <= 0)
	{
	  rotate_right_simple (Pnode);
	  return (*Pnode)->balance == 0;
	}
      else
	{
	  rotate_right_double (Pnode);
	  return 1;
	}
    case 0:
      (*Pnode)->balance = -1;
      return 0;
    case 1:
      (*Pnode)->balance = 0;
      return 1;
    default:
      assert(0); /* dead code */
    }
  assert(0); /* dead code */
  return 0;
}

/*--------------------------------------------------------------*/

static void ** _Pvalue;

static int
remove_smallest (Tnode * Pnode)
{
  if ((*Pnode)->left == NULL) 
    { 
      Tnode tmp = *Pnode;
      *_Pvalue = tmp->value;
      *Pnode = tmp->right;
      free (tmp);
      return 1;
    } 
  else 
    { 
      if (remove_smallest (&((*Pnode)->left)))
	return restore_left (Pnode);
      else
	return 0;
    }
}


/*--------------------------------------------------------------*/

static int
node_remove (Tnode * Pnode)
{
  int compare;
  if (*Pnode == NULL) return 0;
  compare = (*_sort_function) (_value, (*Pnode)->value);
  if (compare < 0)
    {
      if (node_remove (&((*Pnode)->left)))
	return restore_left (Pnode);

    }
  else if (compare > 0)
    {
      if (node_remove (&((*Pnode)->right)))
	return restore_right (Pnode);
    }
  else
    {
      _done = 1;
      if ((*Pnode)->left == NULL)
	{
	  Tnode tmp = (*Pnode);
	  *Pnode = (*Pnode)->right;
	  free (tmp);
	  return 1;
	}
      else if ((*Pnode)->right == NULL)
	{
	  Tnode tmp = (*Pnode);
	  *Pnode = (*Pnode)->left;
	  free (tmp);
	  return 1;
	}
      else
	{
	  _Pvalue = &((*Pnode)->value);
	  if (remove_smallest (&((*Pnode)->right)))
	    return restore_right (Pnode);
	}
    }
  return 0;
}

/*--------------------------------------------------------------*/

void
set_remove (Tset set, void * value)
{
  _done = 0;
  _value = value;
  _sort_function = set->sort_function;
  node_remove (&(set->root));
  if (_done) set->size -= 1;
#if 0
  sanity_check(set->root);
#endif
}

/*--------------------------------------------------------------*/

static void *
node_lookup
(Tnode root)
{
  int compare;
  while (1)
    {
      if (root == NULL) return NULL;
      compare = _sort_function(_value, root->value);
      if (compare < 0) root = root->left;
      else if (compare > 0) root = root->right;
      else return root->value;
    }
}

/*--------------------------------------------------------------*/

void * 
set_lookup (Tset set, void * value)
{
  _value = value;
  _sort_function = set->sort_function;
  return node_lookup (set->root);
}

/*--------------------------------------------------------------*/

static int _first;
static void (* _print_function)(FILE *, const void *);
static FILE * _file;

static void
node_printf(const Tnode node)
{
  if (node == NULL) return;
  node_printf(node->left);
  if (_first) 
    {
      _first = 0;
    }
  else
    {
      fprintf(_file, ", ");
    }
  (*_print_function)(_file, node->value);
  node_printf(node->right);
}

/*
int
node_printf(const Tnode node)
{
  int left, right;
  if (node == NULL) return 0;
  fprintf(_file, "[");
  (*_print_function)(_file, node->value);
  left = node_printf(node->left);
  right = node_printf(node->right);
  fprintf(_file, "]");
  fprintf(_file, "%i:%i", node->balance, right - left);
  assert(node->balance == right - left);
  return (left > right ? left : right) + 1;
}
*/

/*--------------------------------------------------------------*/

void
set_printf(FILE * file, const Tset set,
	   void (* print_function) (FILE *, const void *))
{
  fprintf(file, "{");
  _first = 1;
  _print_function = print_function;
  _file = file;
  node_printf(set->root);
  fprintf(file, "}");
}

/*--------------------------------------------------------------*/

void
set_union (Tset s1, Tset s2)
{
  Tlist l2 = set_list (s2);
  while (l2)
    {
      set_insert (s1, list_car(l2));
      list_remove (l2);
    }
}

/*--------------------------------------------------------------*/

static Tset dest_set = NULL;

static void
set_merge_aux (void * value)
{
  set_insert (dest_set, value);
}

/*--------------------------------------------------------------*/

void
set_merge (Tset s1, Tset s2)
{
  TFfree fun;
  dest_set = s1;
  set_apply (s2, set_merge_aux);
  fun = s2->free_function;
  s2->free_function = NULL;
  set_erase (s2);
  s2->free_function = fun;
}
