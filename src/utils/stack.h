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

/**
   \file Generic stacks
   \brief The module provides generic stacks
   \author David Deharbe
   \author Pascal Fontaine */

#ifndef __STACK_H
#define __STACK_H

#include <stdbool.h>
#include <string.h>

/* Comments
   - nothing garantees everything will always be handled by macros
     so at some point it may be REQUIRED to have differentiated "functions"
     for different stack types
   - stack_INIT() is really a macro, looks like a macro, is a bit ugly as a call
   - typedefing Tstack_EXT to be a stack of type (Tstring, unsigned, etc...)
     can be done using TSstack(EXT, TYPE)
   - see the end of file for usage example */

/* Do not use these macros for your own usage */
#define PROTECT(A) A
#define CC2(A,B) A ## B
/* force prescan */
#define CC(A,B) CC2(A,B)
#define CC3(A,B,C) CC(CC(A,B),C)
#define sizeofdata(stack) sizeof((stack)->data[0])
#ifdef PEDANTIC
#define INSERT_IF_PEDANTIC(A) A
#else
#define INSERT_IF_PEDANTIC(A)
#endif

#include <assert.h>
#include <stdlib.h>

#include "general.h"

/*--------------------------------------------------------------*/

/* A stack of TYPE can be defined as Tstack_EXT using
   TSstack(EXT, TYPE) */
#define TSstack(EXT, TYPE)					\
  typedef struct CC(TSstack, EXT) {				\
    unsigned size;  /*< number of elements in the stack */	\
    unsigned alloc; /*< number of allocated elements */		\
    TYPE data[INSERT_IF_PEDANTIC(1)];    /*< elements in the stack */	\
  } * CC(Tstack, EXT)

/*--------------------------------------------------------------*/

TSstack(_bool, bool);
TSstack(_int, int);
TSstack(_unsigned, unsigned);

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief creates a stack
   \return the created stack */
#define stack_INIT_s(stack, s)						\
  do									\
    {									\
      MY_MALLOC((stack), 2 * sizeof(unsigned) + (s) * sizeofdata(stack)); \
      (stack)->size = 0;						\
      (stack)->alloc = (s);						\
    }									\
  while (0)

/**
   \author Pascal Fontaine
   \brief creates a stack
   \return the created stack */
#define stack_INIT(stack) stack_INIT_s(stack, 4)

/**
   \author Pascal Fontaine
   \brief resize stack such that it contains length elements.
   New elements are set to 0/null
   \param stack a stack
   \param length a number of elements */
#ifndef DMEM
#define stack_resize(stack, length)					\
  do									\
    {									\
      assert(stack);							\
      if (length > (stack)->alloc)					\
	{								\
	  while (length > (stack)->alloc)				\
	    (stack)->alloc *= 2;					\
	  MY_REALLOC((stack), 2 * sizeof(unsigned) +			\
		     (stack)->alloc * sizeofdata(stack));		\
	}								\
      if (length > (stack)->size)					\
	memset((stack)->data + (stack)->size, 0,			\
	       (length - (stack)->size) * sizeofdata(stack));		\
      (stack)->size = length;						\
    }									\
  while (0)
#else
#define stack_resize(stack, length)					\
  do									\
    {									\
      assert(stack);							\
      if (length > (stack)->alloc)					\
	{								\
	  void * P;							\
	  MY_MALLOC(P, 2 * sizeof(unsigned) +				\
		    length * sizeofdata(stack));			\
	  memcpy(P, (stack), 2 * sizeof(unsigned) +			\
		 (stack)->alloc * sizeofdata(stack));			\
	  P->alloc = length;						\
	  free(stack);							\
	  stack = P;							\
	}								\
      if (length > (stack)->size)					\
	memset((stack)->data + (stack)->size, 0,			\
	       (length - (stack)->size) * sizeofdata(stack));		\
      (stack)->size = length;						\
    }									\
  while (0)
#endif

/**
   \author Pascal Fontaine
   \brief adds value on top of stack
   \param stack a stack
   \param value a value */
#ifndef DMEM
#define stack_push(stack, value)					\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	{								\
	  (stack)->alloc *= 2;						\
	  MY_REALLOC((stack), 2 * sizeof(unsigned) +			\
		     (stack)->alloc * sizeofdata(stack));		\
	}								\
      (stack)->data[(stack)->size++] = value;				\
    }									\
  while (0)

#else
#define stack_push(stack, value)					\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	stack_resize(stack, (stack)->alloc + 1);			\
      (stack)->data[(stack)->size++] = value;				\
    }									\
  while (0)

#endif

/**
   \author Pascal Fontaine
   \brief allocate space for a supplementary value on top of stack
   \param stack a stack */
#ifndef DMEM
#define stack_inc(stack)						\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	{								\
	  (stack)->alloc *= 2;						\
	  MY_REALLOC((stack), 2 * sizeof(unsigned) +			\
		     (stack)->alloc * sizeofdata(stack));		\
	}								\
      (stack)->size++;							\
    }									\
  while (0)

#else
#define stack_inc(stack)						\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	stack_resize(stack, (stack)->alloc + 1);			\
      (stack)->size++;							\
    }									\
  while (0)

#endif

/**
   \author Pascal Fontaine
   \brief allocate space for n supplementary value on top of stack
   \param stack a stack */
#ifndef DMEM
#define stack_inc_n(stack, n)						\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size + n > (stack)->alloc)				\
	{								\
	  while ((stack)->size + n > (stack)->alloc)			\
	    (stack)->alloc *= 2;					\
	  MY_REALLOC((stack), 2 * sizeof(unsigned) +			\
		     (stack)->alloc * sizeofdata(stack));		\
	}								\
      (stack)->size += n;						\
    }									\
  while (0)

#else
#define stack_inc_n(stack, n)						\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size + n > (stack)->alloc)				\
	stack_resize(stack, (stack)->size + n);				\
      (stack)->size += n;						\
    }									\
  while (0)

#endif

/**
   \author Pascal Fontaine
   \brief allocate space for a supplementary value on top of stack
   \param stack a stack */
#ifndef DMEM
#define stack_inc_hook(stack, hook)					\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	{								\
	  hook((stack)->alloc, (stack)->alloc * 2);			\
	  (stack)->alloc *= 2;						\
	  MY_REALLOC((stack), 2 * sizeof(unsigned) +			\
		     (stack)->alloc * sizeofdata(stack));		\
	}								\
      (stack)->size++;							\
    }									\
  while (0)

#else
#define stack_inc_hook(stack, hook)					\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size == (stack)->alloc)				\
	{								\
	  stack_resize(stack, (stack)->alloc + 1);			\
	  hook((stack)->alloc, (stack)->alloc + 1);			\
	}								\
      (stack)->size++;							\
    }									\
  while (0)

#endif

/**
   \author Pascal Fontaine
   \brief allocate space for a supplementary value on top of stack
   \param stack a stack */
#define stack_inc0(stack)						\
  do									\
    {									\
      stack_inc(stack);							\
      memset((stack)->data + (stack)->size - 1, 0, sizeofdata(stack));	\
    }									\
  while (0)


/**
   \author Pascal Fontaine
   \brief remove value on top of stack
   \param stack a stack
   \return nothing */
#define stack_dec(stack) do { --(stack)->size; } while (0)

/**
   \author Pascal Fontaine
   \brief remove n values on top of stack
   \param stack a stack
   \return nothing */
#define stack_dec_n(stack, n) do { (stack)->size -= n; } while (0)

/**
   \author Pascal Fontaine
   \brief get value on top of stack, and remove it
   \param stack a stack
   \return the value on top of the stack */
#define stack_pop(stack) ((stack)->data[--(stack)->size])

/**
   \author Pascal Fontaine
   \brief get value on top of stack, and remove it
   \param stack a stack
   \return the value on top of the stack */
#define stack_pop_n(stack, n) ((stack)->data[(stack)->size -= n])

/**
   \author Pascal Fontaine
   \brief get value on top of stack, without removing it
   \param stack a stack
   \return the value on top of the stack */
#define stack_top(stack) ((stack)->data[(stack)->size - 1])

/**
   \author Pascal Fontaine
   \brief get value at n from top of stack, without touching stack
   \param stack a stack
   \return the value */
#define stack_top_n(stack, n) ((stack)->data[(stack)->size - n])

/**
   \author Pascal Fontaine
   \brief get an elements in a stack
   \param stack a stack
   \param i the index of the element
   \return the element at given index */
#define stack_get(stack, i) ((stack)->data[i])

/**
   \author Pascal Fontaine
   \brief set an elements in a stack
   \param stack a stack
   \param i the index of the element
   \param value the element to put at given index */
#define stack_set(stack, i, value) ((stack)->data[i] = (value))

/**
   \author Pascal Fontaine
   \brief free a stack
   \param stack a stack */
#define stack_free(stack) do { free(stack); (stack) = NULL; } while (0)

/**
   \author Pascal Fontaine
   \brief empty a stack
   \param stack a stack */
#define stack_reset(stack) do { (stack)->size = 0; } while (0)

/**
   \author Pascal Fontaine
   \brief check if a stack is empty
   \param stack a stack
   \return 1 iff there is no element in the stack */
#define stack_is_empty(stack) ((stack)->size == 0)

/**
   \author Pascal Fontaine
   \brief get number of elements in a stack
   \param stack a stack
   \return the number of elements in the stack */
#define stack_size(stack) ((stack)->size)

/**
   \author Pascal Fontaine
   \brief apply a function to all elements in a stack
   \param stack a stack
   \param f a function */
#define stack_apply(stack, f)						\
  do									\
    {									\
      unsigned i;							\
      assert(stack);							\
      for (i = 0; i < (stack)->size; ++i)				\
	f((stack)->data[i]);						\
    }									\
  while (0)


/**
   \author Pascal Fontaine
   \brief copy all elements of stack2 into stack
   \param stack a stack
   \param stack2 another stack */
#define stack_merge(stack, stack2)					\
  do									\
    {									\
      unsigned i;							\
      assert(stack);							\
      assert(stack2);							\
      for (i = 0; i < (stack2)->size; ++i)				\
	stack_push(stack, (stack2)->data[i]);				\
    }									\
  while (0)


/**
   \author Pascal Fontaine
   \brief sort a stack
   \param stack a stack
   \param compare a compare function */
#define stack_sort(stack, f)						\
  do									\
    {									\
      assert(stack);							\
      if ((stack)->size > 1)						\
	qsort((stack)->data, (stack)->size, sizeofdata(stack),		\
	      (int (*) (const void *, const void *)) f);		\
    }									\
  while (0)


#endif

/*
#include "stdio.h"

#define MY_MALLOC(A, B) A = malloc(B)
#define MY_REALLOC(A, B) A = realloc(A, B)

#include "stack.h"

void
print_c(char * str)
{
  printf("%s\n", str);
}

void
print_u(unsigned u)
{
  printf("%d\n", u);
}

TSstack(_c, char *);

int
main(void)
{
  unsigned i;
  Tstack(unsigned) stack_u;
  Tstack_c stack_c;
  stack_INIT(stack_u);
  stack_push(stack_u, 1);
  stack_push(stack_u, 2);
  stack_push(stack_u, 3);
  stack_push(stack_u, 3);
  stack_push(stack_u, 4);
  stack_push(stack_u, 5);
  stack_push(stack_u, 6);
  for (i = 0; i < stack_u->size; i++)
    printf("%d\n", stack_u->data[i]);

  stack_apply(stack_u, print_u);

  stack_free(stack_u);

  stack_INIT(stack_c);
  stack_push(stack_c, "c 1");
  stack_push(stack_c, "c 2");
  stack_push(stack_c, "c 3");
  stack_push(stack_c, "c 3");
  stack_push(stack_c, "c 4");
  stack_push(stack_c, "c 5");
  stack_push(stack_c, "c 6");
  for (i = 0; i < stack_c->size; i++)
    printf("%s\n", stack_c->data[i]);

  stack_apply(stack_c, print_c);
  
  stack_free(stack_c);

  return 0;
}
*/
