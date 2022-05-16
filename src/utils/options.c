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

/* TO DD: following line circumvent bug with some vers of libs */
#include <ctype.h>
#include <sys/time.h>
#include <string.h>
#include <stdlib.h>

#ifdef WITH_ARGP
#include <argp.h>
#endif

#include "general.h"
#include "options.h"
#include "table.h"

#ifdef WITH_ARGP
static struct argp_option *argp_options;
#endif

#define COLUMN_WIDTH 79

typedef enum
  {OPTION_BOOL, OPTION_INT, OPTION_STR} option_type;

struct TSoption
{
  option_type type;
  char *name;
  char *doc;
  char *arg;
  /* PF one character option */
  int key;
  union
  {
    char **astr;
    int *aint;
    bool *abool;
  } val;
};
typedef struct TSoption Toption;

static Ttable option_table;
static Ttable options_arguments_table;
static char *options_args_doc;
static char *options_program_doc_head;
static char *options_program_doc_foot;
#ifdef WITH_ARGP
static char *options_program_doc;
#endif
static char *options_program_name;
static char *options_program_version;
static char *options_program_bug_address;
static char *options_env_prefix;
static int options_nb;

/* TO DD: In principle, it is not necessary to initialise static
   variables : they are automatically set to 0 */
#ifndef WITH_ARGP
static bool options_print_help = false;
static bool options_print_usage = false;
#endif

static int initialised = 0;

/*--------------------------------------------------------------*/

/* cuts the text into pieces so that it fits into the 
   column width */ 
static void
print_indent(FILE * file, int first_ind, int ind, char *str)
{
  int c = ind;
  int i, j;
  int k;
  if (first_ind < 0)
    {
      fprintf(file, "\n");
      first_ind = ind;
    }
  for (i = first_ind; i > 0; i--)
    fprintf(file, " ");
  k = (int)strlen(str);
  for (i = 0, j = 0; i < k; i++, c++)
    {
      if (i == j)
	{
	  j++;
	  while (j < k && str[j] != ' ' && str[j] != '\n')
	    j++;
	}
      if (j - i - 1 + c > COLUMN_WIDTH || str[i] == '\n')
	{
	  while (str[i] == ' ')
	    i++;
	  fprintf(file, "\n");
	  for (c = 0; c < ind; c++)
	    fprintf(file, " ");
	}
      if (str[i] != '\n')
	fprintf(file, "%c", str[i]);
    }
  fprintf(file, "\n");
}

/*--------------------------------------------------------------*/

void
options_usage(FILE * file)
{
  unsigned i;

  if (options_program_doc_head)
    fprintf(file, "%s\n", options_program_doc_head);
  if (options_program_version)
    fprintf(file, "Version: %s\n", options_program_version);
  if (options_program_name)
    fprintf(file, "Usage: %s [OPTION...] %s\n", options_program_name,
	     options_args_doc);
  if (options_program_doc_head || options_program_version || 
      options_program_name)
  fprintf(file, "\n");
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption *Poption = table_get(option_table, i);
      int sz = 0;
      if (Poption->key < 256)
	fprintf(file, "  -%c, ", (char) Poption->key);
      else
	fprintf(file, "      ");
      if (Poption->name)
	fprintf(file, " --%s", Poption->name);
      else
	fprintf(file, "   ");
      sz += Poption->name ? (int) strlen(Poption->name) : 0;
      if (Poption->type == OPTION_INT || Poption->type == OPTION_STR)
	{
	  fprintf(file, "=%s", Poption->arg);
	  sz += 1 + (int) strlen(Poption->arg);
	}
      fprintf(file, " ");
      print_indent(file, 20 - sz, 30, Poption->doc);
    }
  fprintf(file, "\n");
  if (options_program_doc_foot)
    print_indent(file, 0, 0, options_program_doc_foot);
  if (options_program_bug_address)
    fprintf(file, "Report bugs to %s.\n", options_program_bug_address);
}

/*--------------------------------------------------------------*/

static Toption *
options_new_generic(char short_name, char *long_name, char *doc, char *arg)
{
  int i;
  Toption *Poption;
  MY_MALLOC(Poption, sizeof(Toption));
  /* TO DD: just to avoid being quadratic if we can be linear :-) */
  for (i = (int) strlen(long_name) - 1; i >= 0; i--)
    if (long_name[i] == '_')
      my_error("options_new : options should not contain underscore\n");
  options_nb++;

#ifdef WITH_ARGP
  MY_REALLOC(argp_options, (options_nb + 1) * sizeof(struct argp_option));
  argp_options[options_nb - 1].name = long_name;
  argp_options[options_nb - 1].key =
    (short_name == '\0') ? 256 + options_nb : (signed char) short_name;
  if (!arg || !strcmp(arg, ""))
    argp_options[options_nb - 1].arg = NULL;
  else
    argp_options[options_nb - 1].arg = arg;
  argp_options[options_nb - 1].flags = 0;
  argp_options[options_nb - 1].doc = doc;
  argp_options[options_nb - 1].group = 0;
  argp_options[options_nb].name = NULL;
  argp_options[options_nb].key = 0;
  argp_options[options_nb].arg = NULL;
  argp_options[options_nb].flags = 0;
  argp_options[options_nb].doc = NULL;
  argp_options[options_nb].group = 0;
#endif

  Poption->name = long_name;
  Poption->key = (short_name == '\0') ? 256 + options_nb : short_name;
  Poption->doc = doc;
  Poption->arg = arg;
  Poption->val.astr = NULL;
  table_push(option_table, Poption);

  return Poption;
}

/*--------------------------------------------------------------*/

#ifdef WITH_ARGP
static error_t
options_parser(int key, char *arg, struct argp_state *state)
{
  int i;
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption option = * (Toption *) table_get(option_table, i);
      if (option.key == key)
	switch (option.type)
	  {
	  case OPTION_BOOL:
	    *(option.val.abool) = true;
	    return 0;
	  case OPTION_INT:
	    if (!arg)
	      my_error("No argument given for option %s\n",option.key);
	    *(option.val.aint) = atoi(arg);
	    return 0;
	  case OPTION_STR:
	    if (*(option.val.astr))
	      free(*(option.val.astr));
	    *(option->val.astr) = strmake(arg);
	    return 0;
	  default:
	    my_error("options: internal error\n");
	  }
    }

  if (key == ARGP_KEY_ARG)
    {
      if (state->arg_num < 1)
	{
	  table_push(options_arguments_table, strmake(arg));
	  return 0;
	}
      else
	argp_usage(state);
    }
  if (key == ARGP_KEY_END && state->arg_num < 1)
    argp_usage(state);
  return ARGP_ERR_UNKNOWN;
}
#endif

/*--------------------------------------------------------------*/

void
options_new(char short_name, char *long_name, char *doc, bool *abool)
{
  Toption * Poption = options_new_generic(short_name, long_name, doc, "");
  Poption->val.abool = abool;
  *(Poption->val.abool) = false;
  Poption->type = OPTION_BOOL;
}

/*--------------------------------------------------------------*/

void
options_new_int(char short_name, char *long_name,
		 char *doc, char *arg, int *aint)
{
  Toption * Poption = options_new_generic(short_name, long_name, doc, arg);
  Poption->val.aint = aint;
  *(Poption->val.aint) = 0;
  Poption->type = OPTION_INT;
}

/*--------------------------------------------------------------*/

void
options_new_string(char short_name, char *long_name,
		    char *doc, char *arg, char **str)
{
  Toption * Poption = options_new_generic(short_name, long_name, doc, arg);
  Poption->val.astr = str;
  *(Poption->val.astr) = NULL;
  Poption->type = OPTION_STR;
}

/*--------------------------------------------------------------*/

#ifdef WITH_ARGP
void
options_parse(int argc, char **argv)
{
  int i, j;
  struct argp argp;
  if (!initialised)
    my_error("options: not initialised\n");
  for (i = 0; i < table_length(option_table); i++)
    {
      char str[255];
      Toption option = * (Toption *) table_get(option_table, i);
      strcpy(str, options_env_prefix);
      strcat(str, option.name);
      for (j = strlen(str) - 1; j >= 0; j--)
	if (str[j] == '-')
	  str[j] = '_';
	else
	  str[j] = (char) toupper(str[j]);
      if (getenv(str))
	switch (option.type)
	  {
	  case OPTION_BOOL:
	    if (strcmp(getenv(str), "0"))
	      *(option.val.abool) = true;
	    break;
	  case OPTION_INT:
	    *(option.val.aint) = atoi(getenv(str));
	    break;
	  case OPTION_STR:
	    if (*(option->val.astr))
	      free(*(option->val.astr));
	    *(option->val.astr) = strmake(getenv(str));
	    break;
	  default:
	    my_error("options: internal error\n");
	  }
    }
  argp.options = argp_options;
  argp.parser = options_parser;
  argp.args_doc = "FILENAME";
  argp.doc = options_program_doc;
  argp.children = NULL;
  argp.help_filter = NULL;
  argp.argp_domain = NULL;
  argp_parse(&argp, argc, argv, 0, 0, 0);
}

/*--------------------------------------------------------------*/

#else

/* DD/PF WITHOUT_ARGP */
static int
options_parse_short(int key, char *arg, Tunsigned *counter)
{
  unsigned i;
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption option = * (Toption *) table_get(option_table, i);
      if (option.key == key)
	switch (option.type)
	  {
	  case OPTION_BOOL:
	    *(option.val.abool) = true;
	    return 1;
	  case OPTION_INT:
	    if (!arg)
	      my_error("No argument given for option %s\n",option.key);
	    *(option.val.aint) = atoi(arg);
	    ++(*counter);
	    return 1;
	  case OPTION_STR:
	    if (*(option.val.astr))
	      free (*(option.val.astr));
	    ++(*counter);
	    *(option.val.astr) = strmake(arg);
	    return 1;
	  default:
	    my_error("options: internal error\n");
	  }
    }
  return 0;
}

/*--------------------------------------------------------------*/

/* DD/PF WITHOUT_ARGP */
static int
options_parse_long(char *name, char *arg)
{
  unsigned i;
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption option = * (Toption *) table_get(option_table, i);
      if (strcmp(option.name, name) == 0)
	switch (option.type)
	  {
	  case OPTION_BOOL:
	    *(option.val.abool) = true;
	    return 1;
	  case OPTION_INT:
	    if (!arg)
	      my_error("No argument given for option %s\n",option.name);
	    *(option.val.aint) = atoi(arg);
	    return 1;
	  case OPTION_STR:
	    if (*(option.val.astr))
	      free(*(option.val.astr));
	    *(option.val.astr) = strmake(arg);
	    return 1;
	  default:
	    my_error("options: internal error\n");
	  }
    }
  return 0;
}


/*--------------------------------------------------------------*/

/* DD/PF WITHOUT_ARGP */
void
options_parse(int argc, char **argv)
{
  Tunsigned i;
  int j;
  if (!initialised)
    my_error("options: not initialised\n");
  /* DD - handling options set in the environment */
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption option = * (Toption *) table_get(option_table, i);
      char *str = malloc(strlen(options_env_prefix) + strlen(option.name) + 1);
      strcpy(str, options_env_prefix);
      strcat(str, option.name);
      for (j = (int) strlen(str) - 1; j >= 0; j--)
	if (str[j] == '-')
	  str[j] = '_';
	else
	  str[j] = (char) toupper(str[j]);
      if (getenv(str))
	switch (option.type)
	  {
	  case OPTION_BOOL:
	    if (strcmp(getenv(str), "0"))
	      *(option.val.abool) = true;
	    break;
	  case OPTION_INT:
	    *(option.val.aint) = atoi(getenv(str));
	    break;
	  case OPTION_STR:
	    if (*(option.val.astr))
	      free(*(option.val.astr));
	    *(option.val.astr) = strmake(getenv(str));
	    break;
	  default:
	    my_error("options: internal error\n");
	  }
      free(str);
    }
  /* DD - handling options set in command line */
  for (i = 1; i < (unsigned) argc; ++i)
    {
      char *opt = NULL, *arg = NULL;
      int status = 0;
      opt = strmake(argv[i]);
      if (opt[0] == '-')
	{
	  switch (opt[1])
	    {
	    case '\0':
	      options_usage(stderr);
	      exit(-1);
	      break;
	    case '-':
	      for (j = (int) strlen(opt) - 1; j >= 0; j--)
		if (opt[j] == '=')
		  {
		    opt[j] = 0;
		    arg = opt + j + 1;
		    break;
		  }
	      status = options_parse_long(opt + 2, arg);
	      break;
	    default:
	      if (opt[2]!='\0')
		{
		  fprintf(stderr, "options: error in command line (%s)\n",
			   opt);
		  options_usage(stderr);
		  exit(-1);

		}
	      status = options_parse_short(opt[1], argv[i + 1], & i);
	      break;
	    }
	  if (status == 0)
	    {
	      fprintf(stderr, "options: error in command line (%s)\n", opt);
	      options_usage(stderr);
	      exit(-1);
	    }
	}
      else if (options_arguments_table)
	table_push(options_arguments_table, strmake(opt));
      free(opt);
    }
  if (options_print_usage || options_print_help)
    {
      options_usage(stderr);
      exit(0);
    }
}
#endif

/*--------------------------------------------------------------*/

void
options_fprint(FILE * file)
{
  Tunsigned i;
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption option = * (Toption *) table_get(option_table, i);
      fprintf(file, "%s : ", option.name);
      switch (option.type)
	{
	case OPTION_BOOL:
	  fprintf(file, "%s\n", (*(option.val.abool)) ? "on" : "off");
	  break;
	case OPTION_INT:
	  fprintf(file, "%d\n", *(option.val.aint));
	  break;
	case OPTION_STR:
	  fprintf(file, "%s\n", *(option.val.astr));
	  break;
	default:
	  my_error("options: internal error\n");
	}
    }
}

/*--------------------------------------------------------------*/

void
options_init(void)
{
  if (initialised)
    my_error("Module options initialised twice.\n");
  initialised = 1;
#ifdef WITH_ARGP
  argp_program_version = NULL;
  argp_program_bug_address = NULL;
  argp_options = NULL;
#endif
  options_nb = 0;
  option_table = table_new(10, 10);
  options_arguments_table = NULL;
  options_program_name = NULL;
  options_program_version = NULL;
  options_program_bug_address = NULL;
  options_args_doc = NULL;
  options_program_doc_head = NULL;
  options_env_prefix = NULL;
  options_program_doc_foot = NULL;
#ifdef WITH_ARGP
  options_program_doc = NULL;
#else
  options_print_help = false;
#endif
}

void
options_setup(Ttable arg_table, char *name, char *version,
	      char *bug_address, char *doc_args,
	      char *doc_head, char *doc_foot, char *env_prefix)
{
  size_t sz = 0;
#ifdef WITH_ARGP
  argp_program_version = version;
  argp_program_bug_address = bug_address;
  argp_options = NULL;
#endif
  options_arguments_table = arg_table;

  options_program_name = name;
  options_program_version = version;
  options_program_bug_address = bug_address;
  options_args_doc = doc_args;
  options_program_doc_head = doc_head;
  options_env_prefix = env_prefix;

  options_program_doc_foot =
    strapp(NULL, &sz,
	    "There is a corresponding environment variable for every option.\n"
	    "The names of those environment variables are the long name"
	    " of options, prefixed by ");
  options_program_doc_foot =
    strapp(options_program_doc_foot, &sz, options_env_prefix);
  options_program_doc_foot =
    strapp(options_program_doc_foot, &sz,
	    ", upcased, and with each '-' replaced by '_'.  "
	    "Such a non-zero environment variable sets the boolean option.  "
	    "For integer and string options, the interpretation is natural.\n"
	    "Command line options override environment variables.\n");
  options_program_doc_foot =
    strapp(options_program_doc_foot, &sz, doc_foot);
#ifdef WITH_ARGP
  sz = 0;
  options_program_doc = strapp(NULL, &sz, options_program_doc_head);
  options_program_doc = strapp(options_program_doc, &sz, "\v");
  options_program_doc =
    strapp(options_program_doc, &sz, options_program_doc_foot);
#else
  options_print_help = false;
  options_new('?', "help", "Give this help list", &options_print_help);
  options_new('\0', "usage", "prints help message and exits",
	       &options_print_usage);
#endif
}

/*--------------------------------------------------------------*/

void
options_done(void)
{
  unsigned i;
  if (initialised == 0)
    my_error("Module options closed without being initialised.\n");
  initialised = 0;
#ifdef WITH_ARGP
  free(argp_options);
  free(options_program_doc);
#endif
  free(options_program_doc_foot);
  for (i = 0; i < table_length(option_table); i++)
    {
      Toption * Poption = (Toption *) table_get(option_table, i);
      if (Poption->type == OPTION_STR && *(Poption->val.astr))
	free(*(Poption->val.astr));
      free(Poption);
    }
  table_free(&option_table);
  if (options_arguments_table)
    {
      for (i = 0; i < table_length(options_arguments_table); i++)
        free((char *) table_get(options_arguments_table, i));
      table_free(&options_arguments_table);
    }
}

