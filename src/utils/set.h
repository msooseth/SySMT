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

#ifndef __SET_H
#define __SET_H
#include <stdio.h>

#include "types.h"
#include "list.h"

typedef struct TSset * Tset;

/* DD Creates a set, with the comparison function for elements, and
   destructor for elements */
Tset   set_new (TFcmp, TFfree);
/* DD Frees the set, applying destructor to every elmt */
void   set_free (Tset * Pset);

/* DD Tests if the set is empty */
bool    set_empty (Tset set);
/* DD Returns the number of elements */
Tunsigned set_size (Tset set);

/* DD ???? for PF */
void * set_lookup (Tset set, void * criterion);
/* DD Adds a value in the set, 
   returns 1 if the value was not present before */
int    set_insert (Tset set, void * value);
/* DD Removes value from set */
void   set_remove (Tset set, void * value);
/* DD Removes all elements, applying destructor to every elmt */
void   set_erase (Tset set);
/* DD Returns the list of all elements in the set */
Tlist  set_list (Tset set);

/* DD Applies fun to every element in the set */
void   set_apply (Tset set, TFapply fun);
/* DD copies s2 into s1; s2 left unchanged; O(|s2|.log|s1|) */
void   set_union (Tset s1, Tset s2);
/* DD functionally equivalent to {set_union (s1, s2); set_free (s2);} */
void   set_merge (Tset s1, Tset s2);

/* PF (implemented by DD) print function */
void   set_printf (FILE *, const Tset, void (*)(FILE *, const void *));

#endif /* __SET_H */
