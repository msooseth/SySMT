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

#ifndef UNDO_H
#define UNDO_H

#include "general.h"
#include "stack.h"

/* Public */

/**
   \author David Déharbe and Pascal Fontaine
   \brief type for undo information */
typedef unsigned Tundo_type;
/**
   \author David Déharbe and Pascal Fontaine
   \brief current level */
extern unsigned undo_level;

/**
   \author David Déharbe and Pascal Fontaine
   \brief function to call when undoing some step */
typedef void (*Tundo_hook)(void *);

#define UNDO_LEVEL 0

#define UNDO_CC 1 /* + 12 */

#define UNDO_OLD_ARITH 20 /* + 6 */

#define UNDO_EMATCH 30 /* + 5 */

#define UNDO_NO 40 /* + 2 */

#define UNDO_ARITH 50

#define UNDO_NB 100

/* TODO Maybe it would be convenient for users to be able to
   themselves push several information and retrieve them manually */

/*--------------------------------------------------------------*/

/* Private */

TSstack(_u, unsigned);

extern Tstack_u undo;
extern Tundo_hook undo_hook[];
extern unsigned undo_hook_arg_size[];

/*--------------------------------------------------------------*/

/* Public */

/**
   \author David Déharbe and Pascal Fontaine
   \brief put some information on the undo stack
   \param type of information
   \return pointer to a memory chunk sufficiently large to hold information */
static __inline__ void *
undo_push(Tundo_type type)
{
  stack_inc_n(undo, undo_hook_arg_size[type]);
  stack_push(undo, type);
  return (void *)(&stack_top(undo) - undo_hook_arg_size[type]);
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief notifies a new level
   \remark Warning: every level del should correspond to a level new */
static __inline__ unsigned
undo_level_new(void)
{
  stack_push(undo, UNDO_LEVEL);
  undo_level++;
  return undo_level;
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief backtrack to previous level
   \remark Warning: every level del should correspond to a level new */
static __inline__ void
undo_level_del(void)
{
  unsigned type = stack_pop(undo);
  while (type != UNDO_LEVEL)
    {
      undo_hook[type](&stack_top_n(undo, undo_hook_arg_size[type]));
      stack_dec_n(undo, undo_hook_arg_size[type]);
      type = stack_pop(undo);
    }
  undo_level--;
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief backtrack to given level
   \param level to backtrack */
static __inline__ void
undo_level_backtrack(unsigned level)
{
  while (undo_level > level)
    undo_level_del();
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief associate a hook function and a size with a type
   \param type of information
   \param f hook function
   \param size number of bytes necessary to store information */
void undo_set_hook(Tundo_type type, Tundo_hook f, unsigned size);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief module init */
void undo_init(void);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe and Pascal Fontaine
   \brief module done */
void undo_done(void);

#ifdef DEBUG
void undo_debug(void);
#endif

#endif
