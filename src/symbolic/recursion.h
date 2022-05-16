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

#ifndef __RECURSION_H
#define __RECURSION_H

#include "DAG.h"

/**
   \author Pascal Fontaine
   applies DAG_free to every Pflag in src, and set to NULL
   \param src the input DAG
   \remarks Linear with the DAG size
   \remarks Uses Pflag, flag
   \remarks Non destructive */
void      DAG_free_Pflag(TDAG src);

/**
   \author Pascal Fontaine
   builds a new DAG by applying a function
   \param src the input DAG
   \param f a function from DAG to DAG
   \return src in which f has been applied recursively from leaves to root
   \remarks Linear with the DAG size
   \remarks Uses Pflag
   \remarks Non destructive */
TDAG      structural_recursion(TDAG src, TDAG (*f) (TDAG));

/**
   \author Pascal Fontaine
   builds a new DAG by applying a function
   \param src the input DAG
   \param f a function from DAG to DAG (destructive)
   \return src in which f has been applied recursively from leaves to root
   \remarks the only difference with the previous version is that f is destr.
   \remarks Linear with the DAG size
   \remarks Uses Pflag
   \remarks Non destructive */
TDAG      structural_recursion2(TDAG src, TDAG (*f) (TDAG));

/**
   \author Pascal Fontaine
   \brief builds new DAGs by applying a function.  The new DAGs are stored
   in the input array
   \param n the number of input DAGs
   \param Psrc the input DAGs
   \param f a function from DAG to DAG
   \remarks Linear with the DAGs size
   \remarks Uses Pflag
   \remarks Destructive */
void      structural_recursion_array(unsigned n, TDAG * Psrc,
				     TDAG (*f) (TDAG));

/**
   \author David Déharbe
   builds a new DAG by applying a function until halting nodes
   \param src the input DAG
   \param f a function from DAG to DAG
   \param halt a predicate on DAGs
   \return src in which f has been applied recursively from halting
   nodes to root, halting nodes are those nodes where the predicate
   halt is true
   \remarks Linear with the DAG size
   \remarks Uses Pflag
   \remarks Non destructive */
TDAG      cond_structural_recursion (TDAG src, TDAG (*f) (TDAG),
				     int (*halt) (TDAG));

/**
   \author Pascal Fontaine
   applies a predicate in a DAG
   \param src the input DAG
   \param f is a predicate on DAG node
   \return 0 if and only if f(N) is 0 for one node in src, 1 otherwise
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
int       structural_recursion_pred (TDAG src, int (*f) (TDAG));

/**
   \author Pascal Fontaine
   applies f on every node of DAG
   \param src the input DAG
   \param f a void function on DAG node
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
void      structural_recursion_void (TDAG src, void (*f) (TDAG));

#endif /* __RECURSION_H */
