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
  Module for printing formulas and terms
  --------------------------------------------------------------
*/

#ifndef DAG_PRINT_H
#define DAG_PRINT_H

#include <stdio.h>

#include "DAG.h"

typedef struct TDAG_fprint_opt
{
  char *    logic;            /**< string specifying the logic of the printed formula */
  int       newlines;         /**< (0-1) add new lines when line too long */
  int       columns;          /**< number of columns for printing */
  int       column_to_indent; /**< number of columns d'indentation */
  bool      flat;             /**< (0-1) add definitions for definitions used multiple times */
  int       version;          /**< version.  1: SMT-LIB 1.x  2: SMT-LIB 2.x */
  int       verbosity;        /**< if 0, warnings are not output */
} TDAG_fprint_opt;
extern TDAG_fprint_opt DAG_fprint_opt;

/**
   \author Pascal Fontaine
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes)
   \param file the output file
   \param DAG the formula to output
*/
void DAG_fprint(FILE * file, TDAG DAG);
/**
   \author David Déharbe
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes) on stdout
   \param DAG the formula to output
*/
void DAG_print(TDAG DAG);
/**
   \brief prints a sort to stdout (useful for debugging)
   \param sort the sort to output
*/
void DAG_sort_print(Tsort sort);

/**
   \author Pascal Fontaine
   prints the DAG in SMT-LIB 2 notation, without linefeed.  Introduces definitions
   e.g. #12:(+ a 1), so that #12 may later be used
   \param file the output file
   \param DAG the formula to output
   \remark uses the misc field of DAGs.  Take care of side effects with other
   functions that use the same field.
*/
void DAG_fprint_sharing(FILE * file, TDAG DAG);
/**
   \author Pascal Fontaine
   \param DAG the formula to output
*/
void DAG_fprint_sharing_reset(TDAG DAG);

/**
   \author Pascal Fontaine
   prints formula in Isabelle language (deprecated)
   \param file the output file
   \param DAG the formula to output
*/
void DAG_isa_fprint(FILE * file, TDAG DAG);

/**
   \author David Deharbe
   prints formula in SMT-LIB 2 notation, as a full benchmark file
   \param file the output file
   \param DAG the formula to output
   \param status the status of the formula
*/
void DAG_fprint_smt2_bench(FILE * file, TDAG DAG, char * status);
/**
   \author Pascal Fontaine
   prints a set of formulas in SMT-LIB 1 notation, as a full benchmark file
   \param file the output file
   \param DAG the formula to output
   \param status the status of the formula
*/
void DAG_fprint_smt2_set(FILE * file, TDAG * DAG, unsigned n, char * status);
/**
   \author David Deharbe
   prints formula in B notation, as a full machine file
   \param file the output file
   \param DAG the formula to output
   \note only for benchmarks with Bool and Int as sole sorts.
*/
void DAG_fprint_b(FILE * file, TDAG DAG);

/**
   \author Thomas Bouton
   prints a custom error with a printf-like format to stderr.
   Supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string
*/
void my_DAG_error(char *format, ...);

/**
   \author Thomas Bouton
   prints a custom message with a printf-like format to stderr.
   Supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string
*/
void my_DAG_message(char *format, ...);

/**
   \author Thomas Bouton
   prints a custom waring with a printf-like format to stderr.
   Supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string
*/
void my_DAG_warning(char *format, ...);
#endif
