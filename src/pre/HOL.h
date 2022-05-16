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
  Module for handling higher order constants, beta reduction,...
  --------------------------------------------------------------
*/

#ifndef __HOL_H
#define __HOL_H

#include "DAG.h"

/**
   \author Pascal Fontaine
   \brief check a formula for higher-order constructions
   \param src the term (or formula) to check
   \return 1 if src is FOL (no HOL construction), 0 otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
*/
int     is_FOL(TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for higher-order constructions
   \param src the term (or formula) to check
   \return 1 if src is FOL (no HOL construction), 0 otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks Compared to is_FOL, checks also for let, polymorphic sorts,
   and boolean as arguments of functions or as quantified vars
*/
int     is_FOL_strict(TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for binders (lambda, quantifier, let)
   \param src the term (or formula) to check
   \return 1 if src does not contain binders, 0 otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
*/
int     is_binder_free (TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for quantifiers
   \param src the term (or formula) to check
   \return 1 if src does not contain quantifiers, 0 otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
*/
int     is_quantifier_free (TDAG src);

/**
   \author Pascal Fontaine
   \brief applies beta-reduction wherever it can be
   \param src the term (or formula) to rewrite
   \return the beta-reduced term
   \remarks Non destructive
   \remarks DAG-linear with respect to the lambda-free part, tree-linear
   within scope of lambda
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \post binder_rename invariant is satisfied
*/
TDAG    beta_reduce (TDAG src);

/**
   \brief array version of the beta_reduce function
   \remark Destructive
   \seealso beta_reduce
*/
void    beta_reduce_array(unsigned n, TDAG * Psrc);

/**
   \author Pascal Fontaine
   \brief replace every macro by its value
   \param src the term (or formula) to rewrite
   \return the macro-expanded term
   \remarks Non destructive
   \remarks DAG-linear 
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks ite-, quantifier-, lambda-, apply-tolerant
   \pre binder_rename should have been applied on all macros and term
   \post macro-free term
*/
TDAG    macro_substitute (TDAG src);

/**
   \brief array version of the macro_substitute function
   \remark Destructive
   \seealso macro_substitute
*/
void    macro_substitute_array(unsigned n, TDAG * Psrc);

/**
   \author Pascal Fontaine
   applies equality lowering wherever it can be.  Rewrites equalities
   T1 = T2 where T1 and T2 have function (or predicate) sort into
   forall x_1 ... x_n . T1(x_1, ... , x_n) = T2(x_1, ... , x_n)
   New quantified variables symbols are of the form ?veriT__<n>, so
   such symbols should not be used elsewhere to avoid capture
   \param src the term (or formula) to rewrite
   \return the equality-lowered term
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers).
   \remark ite-, quantifier-, lambda-, apply-tolerant
   \pre none
   \post HOL-equality free term.
   \remarks may introduce apply, so beta-reduction should be used
*/
TDAG    equality_lower (TDAG src);

/**
   \brief array version of the equality_lower function
   \remark Destructive
   \seealso equality_lower
*/
void    equality_lower_array(unsigned n, TDAG * Psrc);

#endif /* __HOL_H */
