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
   \file options.h
   \author David Deharbe, Pascal Fontaine

   \brief Generic module for handling options

   The module must be initialised before any other module that declares program
   options and rely on program arguments.

   A set-up function is available to store information about the 
   running program (this was available before through the initialization
   function, but that causes problems if code using the options module
   needs to be distributed as a library).

   New options can be declared, with association with variables of the
   corresponding type.  As this is generally done in the init part of
   other modules, this enforces that options_init should be called BEFORE
   any init of module using options.
   Just AFTER declaring an option, a DEFAULT value can be assigned to any
   option variable.
   When every option has been declared (i.e. after all inits of modules
   using options) options_parse is called, with program arguments (as passed
   to main).  Now the value of every option is set.

   Also environment variables corresponding to the long name of
   options, prefixed by env_prefix (string given as argument for
   options_setup), upcased, and with each '-' replaced by '_' are
   automatically bound to those options.

   Such a non-zero environment  variable sets the boolean option.  For
   integer and string options, the interpretation is natural.

   Command line options override environment variables.
   Both override default values.

   Names for options should use "-" rather than "_"

   When the command line is parsed, the table passed as argument to
   options_setup, is filled with all the arguments that do not
   correspond to options (i.e. do not follow a short option or long
   follow with argument).
*/

#ifndef OPTIONS_H
#define OPTIONS_H

#include <stdio.h>
#include <stdbool.h>

#include "table.h"

/*--------------------------------------------------------------*/

/* PF Do we use argp for parsing options?
   ARGP is not available everywhere.
   It may (???) taint the program with LGPL ? */
/* #define WITH_ARGP */

/** declares boolean option
    
    declares boolean option to store in *aint with short name, long
    name, description (doc)

    \param short_name char with option short name
    \param long_name pointer to string of option long name
    \param doc pointer to string documenting option
    \param aint pointer to a bool where the value of the argument is stored
*/
void      options_new (char short_name, char *long_name,
		       char *doc, bool *abool);

/** declares integer option
    
    declares integer option to store in *aint with short name, long
    name, description (doc)

    \param short_name char with option short name
    \param long_name pointer to string of option long name
    \param doc pointer to string documenting option
    \param arg pointer to string explaining authorised values
    \param aint pointer to an int where the value of the argument is stored
*/
void      options_new_int (char short_name, char *long_name,
			   char *doc, char *arg, int *aint);

/** declares integer option
    
    declares string-valued option to store in *str with short name, long
    name, description (doc)

    \param short_name char with option short name
    \param long_name pointer to string of option long name
    \param doc pointer to string documenting option
    \param arg pointer to string explaining authorised values
    \param str pointer to string where the value of the argument is stored
*/
void      options_new_string (char short_name, char *long_name,
			      char *doc, char *arg, char **str);

/** parse options 

    parses program arguments

    \param argc number of arguments
    \param argv array of pointers to argument strings
*/
void      options_parse (int argc, char **argv);

/** print options 

    print options and their values to file

    \param file the stream where options are printed
*/
void      options_fprint (FILE * file);

/** initialization 
*/
void      options_init (void);

/** tests if module has been initialised
*/
int       options_initialised (void);

/** setup

   sets up miscellaneous informations about the program usage and options
   obs. client code shall not free these objects until after options_done()

   \param arg_table table where non-optional argument strings are stored (destructive)
   \param name program name
   \param version program version
   \param bug_address email address to report bugs 
   \param doc_args string describing non-optional argument strings (e.g. FILENAME)
   \param doc_head short header string, coming before option descriptions in usage
   \param doc_foot additional documentation string, coming after option descriptions in usage 
   \param env_prefix prefix string for environment variables
*/

void      options_setup (Ttable arg_table, char *name, char *version,
			 char *bug_address, char *doc_args,
			 char *doc_head, char *doc_foot, char *env_prefix);
/** closing the module */
void      options_done (void);

/** print usage 

    prints usage message to file

    \param file the stream where options are printed
*/
void      options_usage (FILE * file);

#endif
