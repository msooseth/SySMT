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

#include <string.h>

#include "config.h"

#include "general.h"

#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-stat.h"
#include "options.h"

#ifdef DEBUG
#include "DAG-print.h"
#endif

#include "fix-trigger.h"
#include "simp-arith.h"
#include "HOL.h"
#include "binder-rename.h"
#include "bfun-elim.h"
#include "bclauses.h"
#include "distinct-elim.h"
#include "ite-elim.h"
#include "let-elim.h"
#include "nary-elim.h"
#include "NO.h"
#include "pm.h"
#include "pre.h"
#include "qnt-tidy.h"
#include "qnt-trigger.h"
#include "rare-symb.h"
#include "simplify.h"
#include "skolem.h"
#include "simp-sym.h"
#include "simp-unit.h"
#include "proof.h"

static int pre_quantifier = 1;

/**
   \addtogroup arguments_user

   - --enable-simp 

   Enables application of simplifications

 */
static bool enable_simp = 0;
static bool enable_unit_simp = 0;
static bool enable_unit_subst_simp = 0;
static bool enable_bclause = 0;
static bool disable_ackermann = 0;

/**
   \addtogroup arguments_user

   - --enable-assumption-simp 

   Enables application of simplifications of assumptions

 */
static bool enable_assumption_simp = 0;

/*--------------------------------------------------------------*/

#ifdef PROOF

Tstack_DAG snapshot = NULL;

static void
pre_proof_snapshot(unsigned n, TDAG * Psrc)
{
  unsigned i;
  if (!snapshot)
    {
      stack_INIT(snapshot);
    }
  else
    for (i = 0; i < stack_size(snapshot); i++)
      DAG_free(stack_get(snapshot,i));
  stack_resize(snapshot, n);
  for (i = 0; i < n; i++)
    stack_set(snapshot, i, DAG_dup(Psrc[i]));
}

/*--------------------------------------------------------------*/

static void
pre_proof_compare(unsigned n, TDAG * Psrc, Tproof_id * Pproof,
		  Tproof_id (f) (Tproof_id, TDAG))
{
  unsigned i;
  assert (stack_size(snapshot) == n);
  for (i = 0; i < n; i++)
    if (Psrc[i] != stack_get(snapshot, i))
      Pproof[i] = f(Pproof[i], Psrc[i]);
}

/*--------------------------------------------------------------*/

static void
pre_proof_erase_snapshot(void)
{
  unsigned i;
  if (snapshot)
    for (i = 0; i < stack_size(snapshot); i++)
      DAG_free(stack_get(snapshot,i));
  stack_free(snapshot);
}
#endif

/*--------------------------------------------------------------*/

static TDAG
pre_HOL_to_FOL(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  TDAG dest, tmp;
  /**************** fix_triggers */
  /* DD normalizes triggers (quantification patterns)
     this should be done once and forall on every input formula
     instances should not be reprocessed */
  /* In principle this should also be applied on formulas coming from
     macros, etc.  However, since this is a favour for the user who
     writes badly formed formulas, it will not be applied on macros */
  dest = fix_trigger(src);
  DAG_free(src);
  src = dest;

  /**************** binder_rename */
  dest = binder_rename(src); /* rename all binders */
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_alphaconv(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /**************** macro_subst */
  /* PF HOL->FOL: the higher order processing */
  /* binder_rename is applied on macro body before expansion so that
     - no bound variable of the macro interacts with bound/unbound vars
     of the formula
     - no free symbol of the macro interacts with binders of the formulas
     thanks to the fact that binder_rename uses fresh names
     To avoid problems with macro containing macros, this occurs
     at macro expansion in macro_substitute */
  /* requires the binder_rename invariant
     should come high in the list because it will introduce new terms
     that also need processing */
  tmp = macro_substitute(src);
  /* requires the binder_rename invariant */
  dest = equality_lower(tmp);
  DAG_free(tmp);

  /**************** equality_lower */
  /* equality lowering may introduce new quantifiers
     so binder_rename should be applied */
  if (dest != src)
    {
#ifdef PROOF
      *Pproof = proof_tmp_macrosubst(*Pproof, dest);
#endif
      DAG_free(src);
      src = dest;

  /**************** binder_rename */
      dest = binder_rename(src); /* rename all binders */
#ifdef PROOF
      if (src != dest)
	*Pproof = proof_tmp_alphaconv(*Pproof, dest);
#endif
    }
  DAG_free(src);
  src = dest;

  /**************** beta_reduction */
  /* should come after equality lowering because it could rewrite
     X = lambda x. f(x) to forall y . X(y) = ((lambda x . f(x)) y)
   */
  dest = beta_reduce(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_betared(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /* HOL-free below this point, but still let, bfuns, and parametric sorts */

  /**************** let_elim */
  dest = let_elim(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_let_elim(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /**************** pm_process */
  /* The idea here is anyway to handle only polymorphic axioms at the
     "top level" of the formula, i.e. as an element of a large conjunction

     Q and phi where Q is a polymorphic axiom will be rewritten
     Q_1... and Q_n ... and phi, where Q_i are instances of Q.

     Is this sufficient? */
  dest = pm_process(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_pm_process(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /**************** bfun_elim */
  dest = bfun_elim(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_bfun_elim(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;
  return src;
}

/*--------------------------------------------------------------*/

#ifndef PROOF
#if 0
static void
pre_HOL_to_FOL_array(unsigned n, TDAG * Psrc)
{
  /**************** fix_triggers */
  /* DD normalizes triggers (quantification patterns)
     this should be done once and forall on every input formula
     instances should not be reprocessed */
  /* In principle this should also be applied on formulas coming from
     macros, etc.  However, since this is a favour for the user who
     writes badly formed formulas, it will not be applied on macros */
  fix_trigger_array(n, Psrc);
  /**************** binder_rename */
  binder_rename_array(n, Psrc); /* rename all binders */
  /**************** macro_subst */
  /* PF HOL->FOL: the higher order processing */
  /* binder_rename is applied on macro body before expansion so that
     - no bound variable of the macro interacts with bound/unbound vars
     of the formula
     - no free symbol of the macro interacts with binders of the formulas
     thanks to the fact that binder_rename uses fresh names
     To avoid problems with macro containing macros, this occurs
     at macro expansion in macro_substitute */
  /* requires the binder_rename invariant
     should come high in the list because it will introduce new terms
     that also need processing */
  macro_substitute_array(n, Psrc);
  /* requires the binder_rename invariant */
  equality_lower_array(n, Psrc);
  /**************** binder_rename */
  binder_rename_array(n, Psrc); /* rename all binders */
  /**************** beta_reduction */
  /* should come after equality lowering because it could rewrite
     X = lambda x. f(x) to forall y . X(y) = ((lambda x . f(x)) y) */
  beta_reduce_array(n, Psrc);
  /* HOL-free below this point, but still let, bfuns, and parametric sorts */
  /**************** let_elim */
  let_elim_array(n, Psrc);
  /**************** pm_process */
  /* The idea here is anyway to handle only polymorphic axioms at the
     "top level" of the formula, i.e. as an element of a large conjunction

     Q and phi where Q is a polymorphic axiom will be rewritten
     Q_1... and Q_n ... and phi, where Q_i are instances of Q.

     Is this sufficient? */
  pm_process_array(n, Psrc);
  /**************** bfun_elim */
  bfun_elim_array(n, Psrc);
}
#endif
#else

static void
pre_HOL_to_FOL_array(unsigned n, TDAG * Psrc, Tproof_id * Pproof)
{
  /**************** fix_triggers */
  /* DD normalizes triggers (quantification patterns)
     this should be done once and forall on every input formula
     instances should not be reprocessed */
  /* In principle this should also be applied on formulas coming from
     macros, etc.  However, since this is a favour for the user who
     writes badly formed formulas, it will not be applied on macros */
  fix_trigger_array(n, Psrc);
  /**************** binder_rename */
  pre_proof_snapshot(n, Psrc);
  binder_rename_array(n, Psrc); /* rename all binders */
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_alphaconv);
  /**************** macro_subst */
  /* PF HOL->FOL: the higher order processing */
  /* binder_rename is applied on macro body before expansion so that
     - no bound variable of the macro interacts with bound/unbound vars
     of the formula
     - no free symbol of the macro interacts with binders of the formulas
     thanks to the fact that binder_rename uses fresh names
     To avoid problems with macro containing macros, this occurs
     at macro expansion in macro_substitute */
  /* requires the binder_rename invariant
     should come high in the list because it will introduce new terms
     that also need processing */
  pre_proof_snapshot(n, Psrc);
  macro_substitute_array(n, Psrc);
  /* requires the binder_rename invariant */
  equality_lower_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_macrosubst);
  /**************** binder_rename */
  pre_proof_snapshot(n, Psrc);
  binder_rename_array(n, Psrc); /* rename all binders */
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_alphaconv);
  /**************** beta_reduction */
  /* should come after equality lowering because it could rewrite
     X = lambda x. f(x) to forall y . X(y) = ((lambda x . f(x)) y) */
  pre_proof_snapshot(n, Psrc);
  beta_reduce_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_betared);
  /* HOL-free below this point, but still let, bfuns, and parametric sorts */
  /**************** let_elim */
  pre_proof_snapshot(n, Psrc);
  let_elim_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_let_elim);
  /**************** pm_process */
  /* The idea here is anyway to handle only polymorphic axioms at the
     "top level" of the formula, i.e. as an element of a large conjunction

     Q and phi where Q is a polymorphic axiom will be rewritten
     Q_1... and Q_n ... and phi, where Q_i are instances of Q.

     Is this sufficient? */
  pre_proof_snapshot(n, Psrc);
  pm_process_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_pm_process);
  /**************** bfun_elim */
  pre_proof_snapshot(n, Psrc);
  bfun_elim_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_bfun_elim);
  pre_proof_erase_snapshot();
}

#endif

/*--------------------------------------------------------------*/

static TDAG
pre_lang_red(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  TDAG dest;
  /**************** nary_elim */
  /* replace n-ary by binary operators
     necessary for Skolemization */
  dest = nary_elim(src); 
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_nary_elim(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /**************** distinct_elim */
  dest = distinct_elim(src); /* eliminates distinct */
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_distinct_elim(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;

  /**************** simp_arith */
  /* PF elimination of constructs that are not natively supported
     this should be done once and forall on every input formula */
  dest = simp_arith(src); /* eliminates >, >= */
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_simp_arith(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
pre_quant_ite(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  TDAG dest;
  int first = 1, changed = 0;
  dest = qnt_tidy(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_qnt_tidy(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;
  /* Completely breaks the binder_rename invariant */
  /* Skolemization does not go into ite terms
     This should thus be applied after ite elimination */
  dest = qnt_simplify(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_qnt_simplify(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;
  /* here is a loop to eliminate skolem quant and ites */
  do
    {
#ifndef PROOF
      if (enable_simp)
	src = simplify_formula(src);
#endif
      dest = ite_elim(src);
      /* ite elim may reveal new skolemizable quant */
#ifdef PROOF
      if (src != dest)
	*Pproof = proof_tmp_ite_elim(*Pproof, dest);
#endif
      if (!first && src == dest)
	{
	  DAG_free(dest);
	  break;
	}
      else
	first = 0;
      DAG_free(src);
      src = dest;
      /*      dest = skolemize(src OPTC_PROOF(Pproof)); */
      dest = skolemize(src);
      /* skolemize may make new ite terms appear */
#ifdef PROOF
      if (src != dest)
	*Pproof = proof_tmp_skolemize(*Pproof, dest);
#endif
      changed = (src != dest);
      DAG_free(src);
      src = dest;	  
    }
  while (changed);
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
pre_ite(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  TDAG dest;
  /* simplify formula may handle ite in a more gentle way than
     ite_elim, it should therefore come before */
#ifndef PROOF
  if (enable_simp)
    src = simplify_formula(src);
#endif
  /* This has no effect inside quantifiers
     This thus should be applied after any rewrite rule that may
     eliminate quantifiers */
  dest = ite_elim(src);
#ifdef PROOF
  if (src != dest)
    *Pproof = proof_tmp_ite_elim(*Pproof, dest);
#endif
  DAG_free(src);
  src = dest;
  return src;
}

/*--------------------------------------------------------------*/

#ifndef PROOF
static TDAG
pre_non_essential(TDAG src)
{
  TDAG dest;
  if (!disable_ackermann)
    {
      dest = rare_symb(src);
      DAG_free(src);
      src = dest;
    }

  dest = simp_sym(src);
  DAG_free(src);
  src = dest;

  if (enable_unit_subst_simp)
    src = simplify_formula_sat(src);
  return src;
}
#endif

/*--------------------------------------------------------------*/

#ifndef PROOF
/* This uses NO, CC, etc..., and will only replace atoms by TRUE/FALSE
   this should come late */
/* Requires to have free access to the NO stack */
/* TODO: for incrementality, it should only be activated if the NO stack is empty */
static TDAG
pre_unit(TDAG src)
{
  TDAG dest;
  Tunsigned orig_n;
  Tunsigned dest_n = DAG_count_nodes(src);
  do
    {
      dest = simplify_unit(src);
      if (dest == src)
	{
	  DAG_free(dest);
	  break;
	}
      DAG_free(src);
      src = dest;
      src = simplify_formula(src);
      
      orig_n = dest_n;
      dest_n = DAG_count_nodes(src);
      qnt_ground(src);
    }
  while ((dest_n > 1) && /* final formula is not TRUE or FALSE */
	 /* previous decrease at least 10 % of nodes */
	 ((orig_n - dest_n) * 10 > orig_n) &&
	 /* previous decrease of at least 20 nodes */
	 ((orig_n - dest_n) > 20));
  return src;
}
#endif

/*--------------------------------------------------------------*/

TDAG
pre_process(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  src = pre_HOL_to_FOL(src OPTC_PROOF(Pproof));
  if (!is_FOL_strict(src))
    my_error("pre_process: result is not FOL\n");
  /* HOL-free, let-free below this point */
  src = pre_lang_red(src OPTC_PROOF(Pproof));
  /* HOL-free, let-free, symbol-normalized below this point */

  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  if (pre_quantifier && DAG_quant(src))
    {
      src = pre_quant_ite(src OPTC_PROOF(Pproof));
      /* This will only eliminate quantified formulas inside the large AND
	 no need to do any post processing */
#ifndef PROOF
      if (enable_assumption_simp)
	src = simplify_benchmark(src);
#endif
    }
  else
    src = pre_ite(src OPTC_PROOF(Pproof));
#ifndef PROOF
  src = pre_non_essential(src);
  if (enable_simp)
    src = simplify_formula(src);
#endif
  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
  qnt_ground(src);
#ifndef PROOF
  if (enable_unit_simp)
    src = pre_unit(src);

  if (enable_bclause)
    {
      TDAG dest = bclauses_add(src);
      DAG_free(src);
      src = dest;      
      src = simplify_formula(src);
      qnt_ground(src);
    }
#endif
  NO_pre(src);
#ifdef DEBUG
  DAG_check_Pflag();
#endif
  /* HOL-free
     let-free
     symbol-normalized i.e. variety of symbols are rewritten (or n-ary
       to binary) so that no attention to those is necessary in the solver
     qnt_ground should be applied
     qnt_tidy should be applied
     ite should only occur in quantified formulas
     no strong (skolemizable) quantifier outside ite terms
  */
  return src;
}

/*--------------------------------------------------------------*/

#ifdef PROOF

void
pre_process_array(unsigned n, TDAG * Psrc, Tproof_id * Pproof)
{
  unsigned i;
  pre_HOL_to_FOL_array(n, Psrc, Pproof);
  for (i = 0; i < n; i++)
    if (!is_FOL_strict(Psrc[i]))
      my_error("pre_process: result is not FOL\n");
  /* HOL-free, let-free below this point */
  for (i = 0; i < n; i++)
    Psrc[i] = pre_lang_red(Psrc[i], &Pproof[i]);
  /* HOL-free, let-free, symbol-normalized below this point */

  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  for (i = 0; i < n; i++)
    if (pre_quantifier && DAG_quant(Psrc[i]))
      Psrc[i] = pre_quant_ite(Psrc[i], &Pproof[i]);
    else
      Psrc[i] = pre_ite(Psrc[i], &Pproof[i]);
  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
#ifndef PROOF
  src = pre_non_essential(src);
  if (enable_simp)
    src = simplify_formula(src);
#endif
  for (i = 0; i < n; i++)
    qnt_ground(Psrc[i]);
#ifndef PROOF
  if (enable_unit_simp)
    src = pre_unit(src);
#endif
  for (i = 0; i < n; i++)
    NO_pre(Psrc[i]);
#ifdef DEBUG
  DAG_check_Pflag();
#endif
  /* HOL-free
     let-free
     symbol-normalized i.e. variety of symbols are rewritten (or n-ary
       to binary) so that no attention to those is necessary in the solver
     qnt_ground should be applied
     qnt_tidy should be applied
     ite should only occur in quantified formulas
     no strong (skolemizable) quantifier outside ite terms
  */
}

#endif

/*--------------------------------------------------------------*/

TDAG
pre_process_instance(TDAG src OPTC_PROOF(Tproof_id * Pproof))
{
  TDAG quant = DAG_arg0(src), instance = DAG_dup(DAG_arg1(src)), lemma;
#ifdef PROOF
  Tproof_id proof_id;
  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  proof_subproof_begin();
  proof_id = proof_add_formula(DAG_dup(instance));
#endif
  if (pre_quantifier && DAG_quant(instance))
    instance = pre_quant_ite(instance OPTC_PROOF(&proof_id));
  else
    instance = pre_ite(instance OPTC_PROOF(&proof_id));
#ifdef PROOF
  if (DAG_arg1(src) != instance)
    {
      Tproof_id proof_id1, proof_id2, proof_id3;
      proof_id = proof_subproof_end();
      lemma = DAG_dup(DAG_or2(quant, instance));
      proof_id1 = proof_or(*Pproof);
      proof_id2 = proof_or_neg(lemma, 0);
      proof_id3 = proof_or_neg(lemma, 1);
      *Pproof = proof_resolve(4, proof_id1, proof_id, proof_id2, proof_id3);
    }
  else
    {
      proof_subproof_remove();
      lemma = DAG_dup(src);
    }
#else
  if (enable_simp)
    instance = simplify_formula(instance);
  lemma = DAG_dup(DAG_or2(quant, instance));
#endif
  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
  qnt_ground(instance);
#ifdef DEBUG
  DAG_check_Pflag();
#endif
  DAG_free(src);
  DAG_free(instance);
  NO_pre(lemma);
  return lemma;
}

/*--------------------------------------------------------------*/

void
pre_init(void)
{
  distinct_elim_init();
  skolemize_init();
  simp_arith_init();
  simp_sym_init();
  bclauses_init();
  options_new(0, "enable-simp", "Enable simplifications",
	      &enable_simp);
  options_new(0, "enable-unit-simp",
	      "Enable unit clause propagation as simplification.  "
	      "Only available in non-interactive mode",
	      &enable_unit_simp);
  options_new(0, "enable-unit-subst-simp",
	      "Enable unit clause rewriting as simplification.  "
	      "Only available in non-interactive mode",
	      &enable_unit_subst_simp);
  options_new(0, "disable-ackermann",
	      "Disable local Ackermannization and elimination of rare symbols.",
	      &disable_ackermann);
  options_new(0, "enable-assumption-simp", "Enable simplifications of assumptions",
	      &enable_assumption_simp);
  options_new(0, "enable-bclause",
	      "Add binary clauses for speed-up.",
	      &enable_bclause);
  pre_quantifier = 1;
}

/*--------------------------------------------------------------*/

void
pre_logic(char * logic)
{
  if (strcmp(logic, "QF_UF") == 0 ||
      strcmp(logic, "QF_UFIDL") == 0 ||
      strcmp(logic, "QF_IDL") == 0 ||
      strcmp(logic, "QF_RDL") == 0 ||
      strcmp(logic, "QF_LRA") == 0 ||
      strcmp(logic, "QF_UFLRA") == 0 ||
      strcmp(logic, "QF_LIA") == 0 ||
      strcmp(logic, "QF_UFLIA") == 0)
    pre_quantifier = 0;
  else
    pre_quantifier = 1;
  simp_arith_logic(logic);
}

/*--------------------------------------------------------------*/

void
pre_done(void)
{
  distinct_elim_done();
  bclauses_done();
  skolemize_done();
  simp_arith_done();
  simp_sym_done();
}
