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
    \mainpage VERI(T) documentation

    \section intro_sec Introduction

    VERI(T) is a Satisfiability Modulo Theory (SMT) solver.

    The solver is currently integrating a quantifier instantiation
    mechanism with decision procedures for the following:
    uninterpreted functions with equality, difference arithmetics
    (integers and reals), linear arithmetics (integers and reals).
    The superposition-based prover E is also integrated as a fall-back
    verification engine for verification conditions with a unique
    sort. 

    \section execution_sec Execution

    The input of the solver is a proof obligation in one of the
    following formats:

    - SMT-LIB 2.0: This is the default input format and may be employed 
    as long as interactive features and incrementality are not used.
    See http://www.smtlib.org for information on this format.

    - DIMACS: This format may be employed when one wants to use 
    veriT as a SAT-solver (with proof production capabilities).

    SMT-LIB 1.2 is no longer supported.
 
    In the case of the SMT-LIB format, the input language is actually
    slightly expanded and includes parametric sorts, macro definitions
    and lambda expressions. Note the "dot" separator in notation for
    lambda abstractions, as shown in the following example (in format
    SMT-LIB 1.2):

    \include macro.smt

    The solver outputs the result on stdout as a one-line
    message, which is either: 
    
    - sat when the formula in the proof obligation is satisfiable; 

    - unsat when the formula in the proof obligation is unsatisfiable;

    - unknown when the solver has not been able to conclude.

    Also possible is a run-time error. The authors of the tool made
    their best to catch all possible errors and output a meaningful
    message.

    The solver may be executed in two modes: batch and interactive.

    In batch mode the solver expects as argument the name of a file
    name in one of the supported formats. In interactive mode the
    solver expects a series of clauses in SMT-LIB 2.0 format. Several
    formulas may be added, and they are conjunctively checked for
    satisfiability. There is no provision for backtracking.

    veriT may be compiled with proof-producing capabilities (this is
    optional). When the result is unsat, a derivation of the result
    might be produced and checked by a third party.

    Command-line options may be used to output information about the
    proof obligation or about the proof process itself into files or
    to the standard output stream. See the specific documentation
    modules for \ref arguments_user and \ref arguments_developer.

    \section smtlib_2_sec Support for SMT-LIB 2.0

    - AUFLIA Incomplete
    - AUFLIRA Not supported
    - AUFNIRA Not supported
    - LRA Incomplete
    - QF_ABV Not supported
    - QF_AUFBV Not supported
    - QF_AUFLIA Incomplete
    - QF_AX Incomplete
    - QF_BV Not supported
    - QF_IDL Complete
    - QF_LIA Incomplete
    - QF_LRA Complete
    - QF_NIA Incomplete
    - QF_RDL Complete
    - QF_UF Complete, proof-producing
    - QF_UFIDL Complete

    The following commands are supported:
    - set-logic
    - set-info: :status and :version are supported.
    - set-option: :diagnostic-output-channel, :regular-output-channel,
    :print-success are supported.
    - get-option: only for the options listed with set-option
    - declare-sort
    - define-sort
    - declare-fun
    - define-fun
    - assert
    - check-sat
    - exit

    The following commands are parsed but their interpretation
    is not compliant:
    - push
    - pop

    The following commands are parsed but are not supported:
    - set-option
    - get-assertions
    - get-proof (but see proof production for SMT-LIB 1.2)
    - get-unsat-core
    - get-value
    - get-assignment

    veriT currently does not support indexed symbols as identifiers.

    \section install_sec Installation

    The source code is available on the Web at
    http://www.verit-solver.org/ , along with a series of binaries.

    To install the solver from the sources, once it is downloaded and
    unpacked, change to the top level directory and set the values in
    the file "Makefile.variables". Run the command line make.  This
    will fetch some third-party components and compile the
    sources. Once the build is complete, copy the binary program,
    named "verit", to the location of your choice.

    \section licence_sec Licence
    
    VERI(T) uses third-party components and, as such, is subject to
    some constraints. To relieve our potential users from such
    constraints we are providing libveriT under two licences BSD and
    LGPL.

    The functionality between these licenses is the same. 

    LGPL-VERI(T) links against the GMP library to handle arbitrary
    precision arithmetics.

    BSD-VERI(T) uses native data types and only supports fixed
    precision arithmetics. However, should an overflow occur at
    runtime, it will be detected and an error will be reported.

    \section authors_sec Authors

    Pascal Fontaine, David Deharbe are the two main developpers. Diego
    Caminha has developed the arithmetic decision procedures and
    contributed to the design of the combination schema of the
    different "little engines" for reasoning. Thomas Bouton has
    contributed improvements to the interaction with the boolean
    satisfiability engine as well as the QA infrastructure.

    The solver is being developed by the <a
    href="http://sites.google.com/site/forallufrn/people">ForAll</a>
    group at <a href="http://www.ufrn.br">Universidade Federal do Rio
    Grande do Norte</a> (Brazil) and the <a
    href="http://www.loria.fr/equipes/mosel/">Mosel</a> group at <a
    href="http://www.uhp-nancy.fr">Universit&eacute; Nancy 2</a> and
    <a href="http://www.loria.fr">LORIA</a> (France).

    \defgroup arguments_user Options

    \defgroup arguments_developer Developer options

 */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#ifdef DEBUG
#ifdef MACOS
#include <unistd.h>
#endif
#endif
#include "config.h"

#include "general.h"
#include "metrics.h"
#include "options.h"
#include "statistics.h"
#include "sys.h"
#include "table.h"

#include "veriT.h"
#include "complete.h"
#include "DAG-print.h"
#include "DAG.h"
#include "global.h"
#include "pre.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "dimacs.h"
#include "smtlib2.h"

/* TODO: make sure veriT_init contains EVERYTHING to initialise.
   Now, options and stats are outside */


/**
   \addtogroup arguments_user

   - --disable-banner 

   The message identifying the program is not printed to stdout.
 */
static bool option_disable_banner;

#ifdef PROOF
/**
   \addtogroup arguments_developer

   - --print-proof-format-and-exit 

   Loads formula, expands macros, applies selected simplifications,
   and prints on stdout in SMT format.
*/
/** \todo update 2.0: Only for SMT-LIB 1.2.  From 2.0 on, use commands. */
static bool option_proof_format_and_exit;

#endif

/**
   \addtogroup arguments_developer

   - --print-simp-and-exit 

   Loads formula, expands macros, applies selected simplifications,
   and prints on stdout in SMT format.
*/
/** \todo update 2.0: Only for SMT-LIB 1.2.  From 2.0 on, use commands. */
bool option_print_simp_and_exit;

/**
   \addtogroup arguments_developer

   - --verbose

   Prints some statistics
*/
static bool option_verbose;

#ifdef OPTION_CHECK_TIME
/**
   \addtogroup arguments_user

   - --max-time=n 

   Sets maximal execution time to n (in seconds). Caveat: the
   execution time limit is individual to each process (i.e. the main
   process and the possible calls to external provers).
*/
int option_max_time = 0;
#endif

/**
   \addtogroup arguments_user

   - --input=(smtlib2|dimacs)

   Sets the input format (smtlib2 is default).
*/
static char * input_format = NULL;

/**
   \addtogroup arguments_user

   - --output=(smtlib2|b)

   Sets the output format (smtlib2 is default). Meaningful only when output formulas are produced.
*/
char * output_format = NULL;

/**
   \addtogroup arguments_user

   - --max-time=n 

   Sets maximal execution time to n (in seconds). Caveat: the
   execution time limit is individual to each process (i.e. the main
   process and the possible calls to external provers.)
*/


/**
   \addtogroup arguments_user

   - --disable-print-success 

   Overrides the default SMT-LIB 2 behavior regarding the option
   :print-success.
 */
static bool option_disable_print_success;

/**
   @}
*/

static char *filename;

/*--------------------------------------------------------------*/
/* Some output                                                  */
/*--------------------------------------------------------------*/

static void
output_banner (FILE * out)
{
  if (option_disable_banner == 0)
    fprintf (out, "%s %s - the VERI(T) theorem prover (UFRN/LORIA).\n",
	     PROGRAM_NAME, PROGRAM_VERSION);
}

/*--------------------------------------------------------------*/

static void
veriT_exit (int status)
{
  /* DD+PF exit library */
  DAG_smtlib_logic_done();
  veriT_done();
  /* DD+PF print some statistics */
  if (option_verbose)
    {
      stats_fprint_formats(stdout);
      stats_fprint(stdout);
    }
  stats_done();
  options_done();
#ifdef DEBUG 
#ifdef MACOS
  pause();
#endif
#endif
  exit(status);
}

/*
  --------------------------------------------------------------
  Core function
  --------------------------------------------------------------
*/

static Ttable filename_table = NULL;
static FILE * input_file = NULL;

static void
set_options (void)
{
  /* DD+PF setup, declare and parse options */
  options_setup (filename_table,
		 PROGRAM_NAME, PROGRAM_VERSION,
		 PROGRAM_MAIL, "FILENAME",
		 "the veriT solver "
		 "-- checking verification conditions with Theories.",
		 "\nPlease notice that symbol names beginning"
		 " with veriT__ or ?veriT__ are reserved.\n", "VERIT_");
  options_new ('v', "verbose", "Output options, gives statistics, ...",
	       &option_verbose);
  options_new_string ('i', "input", "input format (smtlib2 is default)",
		      "(smtlib2|dimacs)",
		      &input_format);
  input_format = strmake("smtlib2");
  options_new_string ('o', "output", "output format (smtlib2 is default)",
		      "(smtlib2|b|py_graph)",
		      &output_format);
  output_format = strmake("smtlib2");
#ifdef PROOF
  options_new (0, "proof-format-and-exit",
	       "Print proof format on stdout and exits",
	       &option_proof_format_and_exit);
#endif
  options_new (0, "print-simp-and-exit",
	       "Loads formula, simplifies," "and print on stdout (smt)",
	       &option_print_simp_and_exit);
  options_new (0, "print-flat",
	       "print formula in flattened mode"
	       " (no shared subterms or formulas)", &DAG_fprint_opt.flat);
  options_new (0, "disable-banner",
	       "disable printing of program banner",
	       &option_disable_banner);
  options_new (0, "disable-print-success", 
	       "cancel SMT-LIB 2 default",
	       &option_disable_print_success);

#ifdef OPTION_CHECK_TIME
  options_new_int (0, "max-time",
		   "Exit when time is exceeded", "SECONDS", 
	           &option_max_time);
#endif
}
#define STATS_LEVEL 1

/*--------------------------------------------------------------*/

int
main(int argc, char **argv)
{
#ifdef DEBUG
  setbuf(stdout, 0);		/* makes it easier to catch bugs */
#endif
  stats_init();
  veriT_init();
  DAG_smtlib_logic_init();

  filename_table = table_new(10, 10);

  set_options();
  options_parse(argc, argv);

  /* DD+PF output some basic information */
  output_banner(stdout);

#ifdef PROOF
  if (option_proof_format_and_exit)
    {
      proof_doc(stdout);
      proof_satisfiable();
      veriT_exit(0);
    }
#endif

  if (option_verbose)
    options_fprint(stdout);

  if (table_length(filename_table) > 1)
    {
      fprintf(stderr, "Only one file name is allowed\n");
      options_usage(stderr);
      veriT_exit(-1);
    }

  if (table_length(filename_table) == 1)
    {
      /* DD+PF parse file */
      filename = (char *) table_get(filename_table, 0);
      input_file = sys_open_file(filename, "r");
      if (option_verbose)
	fprintf(stdout, "Reading file %s.\n", filename);
#ifdef PROOF
      proof_set_input_file(filename);
#endif
    }
  else
    input_file = stdin;


  if (!strcmp(input_format,"smtlib2"))
    parse_smtlib2(input_file, option_disable_print_success);
  else if (!strcmp(input_format,"dimacs"))
    parse_dimacs(input_file);

  if (input_file != stdin)
    sys_close_file(input_file);

  veriT_exit(0);
  return 0; /* no gcc warning */
}
