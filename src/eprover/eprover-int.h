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
  E prover interface module

  module level declarations
  --------------------------------------------------------------
*/
#ifndef __EPROVER_INT_H
#define __EPROVER_INT_H
#include <stdio.h>

#include "DAG.h"
#include "hash.h"
#include "set.h"
#include "table.h"

#include "veriT-status.h"

#include "tstp-parser.h"
#include "eprover.h"

/* #define DEBUG_E */

/** \brief a type to represent hypothesis used in inference: an unsigned */
typedef uintptr_t Tpremisse;

/** \brief eprover-derived inferences are labeled c_0_X where X is unsigned */
#define is_internal_name(str) (strncmp((str), "c_0_", 4) == 0)
/** \brief eprover-given axioms are labeled veriT_clueX where X is unsigned */
#define is_external_name(str) (strncmp((str), "veriT_clue", 10) == 0)
/** \brief eprover inferences: label left-shifted one bit, leftmost bit 0 */
#define premisse_of_internal(str) (((uintptr_t) atoi((str)+4)) << 1)
/** \brief eprover axioms: label left-shifted one bit, leftmost bit 1 */
#define premisse_of_external(str) (1 | ((uintptr_t) atoi((str)+10) << 1))
/** \brief tests if a premisse is an eprover-derived inference */
#define premisse_is_internal(p) (((p) & 1) == 0)
/** \brief tests if a premisse is an eprover-given axiom (clue) */
#define premisse_is_external(p) ((p) & 1)
/** \brief recovers the label from a premisse */
#define premisse_value(p) ((p) >> 1)

/** \brief records an inference from the E prover. */
typedef struct TSinference
{
  TDAG      DAG;         /** the formula derived */
  Tlist     premisses;   
  Trole     role;        /** the type of inference performed */
  int       final : 1;   /** states if the inference is registered as final */
  int       ignore : 1;  /** do not give inference as a lemma to client */
  int       flag : 1;    /** auxiliary bit */
} * Tinference;


/**
   \brief records a full derivation from the E prover
*/
typedef struct TSderivation
{
  /** inference steps, stored in the order they were output by E.
      position 0 is always filled with a dummy value, as E identifies
      inferences starting from 1.  The table is thus filled with
      region A: 0: dummy region B: 1..nb_axioms: formulas given to E
      (clues and number disequalities) region C:
      nb_axioms+1..table_length(inferences)-1: derived formulas region
      A is always filled; region B is filled when the input file of E
      is printed; region C is filled when the output file from E is
      read.  regions B and C are emptied before printing a new file to
      E. */
  Ttable   steps;      
  Tunsigned nb_axioms;  /** indicates how many formulas were given to E */
  Tunsigned conflict;   /** inference where a conflict was detected 
			    is 0 if no conflict has been detected */
} * Tderivation;

/* DD records the inference number of the conflict, if any */

extern void e_set_status(Tstatus status);
extern void e_eq_queue_push(Tclue clue);

extern Tsort e_sort;

/** the current (or last) derivation performed by E */
extern Tderivation e_derivation;

extern Tinference  inference_new (TDAG conclusion, Tlist premisses, 
				  Trole role, int final);
extern void        inference_free (Tinference inf);
extern void        inference_reset_flag (Tinference);
#ifdef DEBUG_E
extern void        inference_fprint (FILE * file, Tinference inf);
#endif

extern Tderivation derivation_new ();
extern  void       derivation_reset (Tderivation);
extern void        derivation_free (Tderivation *);
#ifdef DEBUG_E
extern void        derivation_fprint (FILE * file, Tderivation);
extern void        derivation_print (Tderivation);
#endif

#endif /* __EPROVER_INT_H */
