#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "config.h"

#include "general.h"
#include "hashmap.h"
#include "list.h"
#include "options.h"
#include "set.h"
#include "stack.h"
#include "statistics.h"
#include "response.h"

#include "smtfun.h"

#include "DAG.h"
#include "DAG-ptr.h"
#include "DAG-prop.h"
#include "DAG-print.h"
#include "DAG-symb-DAG.h"
#include "HOL.h"
#include "simplify.h"
#include "veriT.h"

#include "dbg-trigger.h"

#define yylineno yy2lineno

extern int yylineno;

#define ptr_of_symb(s) DAG_ptr_of_symb(s)
#define symb_of_ptr(s) DAG_symb_of_ptr(s)
#define ptr_of_sort(s) DAG_ptr_of_sort(s)
#define sort_of_ptr(s) DAG_sort_of_ptr(s)

enum Tkw {
  KW_NONE = 0,
  KW_ALL_STATISTICS,
  KW_AUTHORS,
  KW_CATEGORY,
  KW_DIAGNOSTIC_OUTPUT_CHANNEL,
  KW_ERROR_BEHAVIOR,
  KW_EXPAND_DEFINITIONS,
  KW_INTERACTIVE_MODE,
  KW_NAME,
  KW_NOTES,
  KW_PRINT_SUCCESS,
  KW_PRODUCE_ASSIGNMENTS,
  KW_PRODUCE_MODELS,
  KW_PRODUCE_PROOFS,
  KW_PRODUCE_UNSAT_CORES,
  KW_RANDOM_SEED,
  KW_REASON_UNKNOWN,
  KW_REGULAR_OUTPUT_CHANNEL,
  KW_SMT_LIB_VERSION,
  KW_SOURCE,
  KW_STATUS,
  KW_VERBOSITY,
  KW_VERSION,
  KW_SIZE
};

char * kw_table [] =
  {
      "none",
      ":all-statistics",
      ":authors",
      ":category",
      ":diagnostic-output-channel",
      ":error-behavior",
      ":expand-definitions",
      ":interactive-mode",
      ":name",
      ":notes",
      ":print-success",
      ":produce-assignments",
      ":produce-models",
      ":produce-proofs",
      ":produce-unsat-cores",
      ":random-seed",
      ":reason-unknown",
      ":regular-output-channel",
      ":smt-lib-version",
      ":source",
      ":status",
      ":verbosity",
      ":version",
  };

Tstatus smt2_status = UNDEF; /**< status as given in the input */

/* ------------------------------------------------------- */
/*                      SMT2 solver options                */
/* ------------------------------------------------------- */

bool   smt2_print_success;                /**< required SMT2 option */
char * smt2_diagnostic_output_channel;    /**< required SMT2 option */
char * smt2_regular_output_channel;       /**< required SMT2 option */

#if STATS_LEVEL > 1
static unsigned stat_nb_nodes, stat_nb_nodes_tree, stat_nb_atoms;
#endif
static unsigned stat_result;

/*
  --------------------------------------------------------------
  help functions
  --------------------------------------------------------------
*/

static enum Tkw
defstring(char * str)
{
  int i;
  for (i = 1; i < KW_SIZE; ++i)
    if (!strcmp(kw_table[i], str))
      return i;
  return 0;
}

static char *
smt2_status_str(int status)
{
  switch (status) 
    {
    case UNDEF: return "unknown";
    case SAT: return "sat";
    case UNSAT: return "unsat";
    default:
      veriT_error("unknown status %i", status);
      return "";
    }
}

/*--------------------------------------------------------------*/
 
/* PF returns 1 if a decimal, 0 if number, error if none of both */
static int
check_decimal(char * str)
{
  if (!isdigit(*str))
    veriT_error("ill-formed on line %d", yylineno);
  ++str;
  while (isdigit(*str)) ++str;
  if (*str == 0)
    return 0;
  if (*str != '.')
    veriT_error("ill-formed decimal on line %d", yylineno);
  ++str;
  if (!isdigit(*str))
    veriT_error("ill-formed decimal on line %d", yylineno);
  ++str;
  while (isdigit(*str)) ++str;
  if (*str == 0)
    return 1;
  veriT_error("ill-formed decimal on line %d", yylineno);
  return 0;
}

/*--------------------------------------------------------------*/
 
static int
check_binary(char * str)
{
  while (*str == '0' || *str == '1') str++;
  if (*str == 0)
    return 1;
  veriT_error("ill-formed binary on line %d", yylineno);
  return 0;
}

/*--------------------------------------------------------------*/
 
static int
check_hex(char * str)
{
  while (isxdigit(*str)) str++;
  if (*str == 0)
    return 1;
  veriT_error("ill-formed hexadecimal on line %d", yylineno);
  return 0;
}

/*--------------------------------------------------------------*/
 
static int
check_str(char * str)
{
  while (*str != '\0' && *str != '"')
    if (*str == '\\')
      str += 2;
    else
      str++;
  if (*str == '"' && *(str + 1) == '\0')
    return 1;
  veriT_error("ill-formed string on line %d", yylineno);
  return 0;
}

/*--------------------------------------------------------------*/
 
static void
check_protected_symbol(char * str)
{
  if (!strncmp(str, "veriT__", 7) ||
      !strncmp(str, "?veriT__", 8))
    veriT_error("reserved symbol used on line %d", yylineno);  
}

/*
  --------------------------------------------------------------
  symbol finding functions
  --------------------------------------------------------------
*/

/* PF this section is necessary because quantifiers and let may
   define atomic terms */

Thashmap hashmap_str = NULL;

static unsigned
hash_function(char * str)
{
  unsigned hash = hash_one_at_a_time(str);
  return hash_one_at_a_time_inc_end(hash);
} 

/*--------------------------------------------------------------*/
 
static Tsigned
hash_str_equal(char * str1, char * str2)
{
  return !strcmp(str1, str2);
}

/*--------------------------------------------------------------*/
 
static void
hash_key_free(char * str)
{
  /* free(str); */
#ifdef PEDANTIC
  printf("%p\n", str);
#endif
}

/*--------------------------------------------------------------*/
 
static void
hash_value_free(Tlist list)
{
  list_free(&list);
}

/*--------------------------------------------------------------*/

/** 
    \author Pascal Fontaine
    add a link for str to symb in LIFO style
    \param str a string for the symbol
    \param symb the symbol to link to str
*/
static void
declare_str(char * str, Tsymb symb)
{
  Tlist * symb_list = (Tlist *) hashmap_lookup(hashmap_str, str);
  if (symb_list)
    {
      assert(*symb_list);
      *symb_list = list_cons(ptr_of_symb(symb), *symb_list);
      return;
    }
  hashmap_insert(hashmap_str, str, 
		 list_cons(ptr_of_symb(symb), NULL));
}

/*--------------------------------------------------------------*/
 
/** 
    \author Pascal Fontaine
    remove up link for str (should be to symb)
    \param str a string for the symbol
    \param symb the symbol to unlink to str
*/
static void
undeclare_str(char * str, Tsymb symb)
{
  Tlist * symb_list = (Tlist *) hashmap_lookup(hashmap_str, str);
  if (!symb_list || !(*symb_list) || 
      symb_of_ptr(list_car(*symb_list)) != symb)
    veriT_error("undeclare_str: internal error (line %d)", yylineno);
  *symb_list = list_remove(*symb_list);
  if (!(*symb_list))
    hashmap_remove(hashmap_str, str);
}

/*--------------------------------------------------------------*/

/** 
    \author Pascal Fontaine
    \brief find symbol linked to str
    \param str a string for the symbol
    \return the symbol linked to str
*/
static Tsymb
lookup_str(char * str)
{
  Tlist * symb_list = (Tlist *) hashmap_lookup(hashmap_str, str);
  if (!symb_list)
    return DAG_SYMB_NULL;
  assert(*symb_list);
  return symb_of_ptr(list_car(*symb_list));
}

/*
  --------------------------------------------------------------
  Commands
  --------------------------------------------------------------
*/

void
smt2_set_logic(char * symbol)
{
  veriT_logic(symbol);
  free(symbol);
}

/*--------------------------------------------------------------*/

/* PF (declare-sort Array 2) */
void
smt2_declare_sort(char * symbol, char * numeral)
{
  unsigned arity;
  long int tmp;
  check_protected_symbol(symbol);
  tmp = strtol(numeral, NULL, 10);
  if (tmp > UINT_MAX)
    my_error("smt2_declare_sort: arity too large\n");
  arity = (unsigned) tmp;
  if (DAG_sort_lookup(symbol))
    my_warning("line %d: redefining sort %s\n", yylineno, symbol);
  if (arity > 0)
    DAG_sort_new_param(symbol, arity);
  else
    DAG_sort_new(symbol, 0, NULL);
  free(symbol);
  free(numeral);
}

/*--------------------------------------------------------------*/

/* PF (define-sort Integer_Array_of_List (Integer List) Array) */
void
smt2_define_sort(char * symbol, Tlist symbol_list, Tsort sort)
{
  unsigned i, arity;
  Tsort * sub;
  check_protected_symbol(symbol);
  arity = list_length(symbol_list);
  MY_MALLOC(sub, arity*sizeof(Tsort));
  for (i = 0; i < arity; ++i, symbol_list = list_cdr(symbol_list))
    {
      char * symbol = (char *) list_car(symbol_list);
      Tsort sort2 = DAG_sort_lookup(symbol);
      if (!sort2) my_error("unknown sort %s on line %d.", symbol, yylineno);
      sub[i] = sort2;
    }
  DAG_sort_new_inst(symbol, sort, arity, sub);
  list_apply(symbol_list, free);
  list_free(&symbol_list);
  free(symbol);
}

/*--------------------------------------------------------------*/

void
smt2_declare_poly_fun(char * symbol, Tlist sort_list1, 
		      Tlist sort_list2, Tsort sort)
{
  unsigned i, arity, type;
  Tsort *sub;
  type = sort == SORT_BOOLEAN ? SYMB_PREDICATE : SYMB_FUNCTION;
  check_protected_symbol(symbol);
  if (!sort_list2)
    {
      DAG_symb_new(symbol, type, sort);
      free(symbol);
      return;
    }
  arity = list_length(sort_list2);
  MY_MALLOC(sub, (arity + 1) * sizeof(Tsort));
  for (i = 0; i < arity; i++, sort_list2 = list_cdr(sort_list2))
    sub[i] = sort_of_ptr(list_car(sort_list2));
  sub[i] = sort;
  DAG_symb_new(symbol, type, DAG_sort_new(NULL, arity + 1, sub));
  free(symbol);
  list_free(&sort_list1);
  list_free(&sort_list2);
}

/*--------------------------------------------------------------*/

void
smt2_declare_fun(char * symbol, Tlist sort_list, Tsort sort)
{
  unsigned i, arity;
  Tsymb_type type;
  Tsort *sub;
  type = sort == SORT_BOOLEAN ? SYMB_PREDICATE : SYMB_FUNCTION;
  check_protected_symbol(symbol);
  if (!sort_list)
    {
      DAG_symb_new(symbol, type, sort);
      free(symbol);
      return;
    }
  arity = list_length(sort_list);
  MY_MALLOC(sub, (arity + 1) * sizeof(Tsort));
  for (i = 0; i < arity; i++, sort_list = list_cdr(sort_list))
    {
      Tsort sort2 = sort_of_ptr(list_car(sort_list));
      if (DAG_sort_parametric(sort2))
	veriT_error("ill-formed sort on line %i", yylineno);
      sub[i] = sort2;
    }
  sub[i] = sort;
  DAG_symb_new(symbol, type, DAG_sort_new(NULL, arity + 1, sub));
  free(symbol);
  list_free(&sort_list);
}

/*--------------------------------------------------------------*/

void
smt2_define_fun(char * symbol, Tstack_symb stack_var, Tsort sort, TDAG term)
{
  unsigned i;
  Tsymb symb;
  TDAG DAG;
  Tstack_DAG stack_arg;
  stack_INIT(stack_arg);
  check_protected_symbol(symbol);
  for (i = 0; i < stack_var->size; i++)
    stack_push(stack_arg, DAG_new_args(stack_var->data[i], NULL));
  stack_push(stack_arg, term);
  DAG = DAG_dup(DAG_new_stack(LAMBDA, stack_arg));
  if (DAG_sort(term) != sort)
    my_error("smt2_define_fun: sort mismatch\n");
  symb = DAG_symb_new(symbol, SYMB_MACRO, DAG_sort(DAG));
  DAG_symb_macro(symb, DAG);
  stack_free(stack_arg);
  DAG_free(term);
  free(symbol);
}

/*--------------------------------------------------------------*/

void
smt2_define_poly_fun(char * symbol, T_SORT_LIST sort_list, 
		     Tstack_symb stack_var, T_SORT Tsort, T_TERM term)
{
  unsigned i;
  Tsymb symb;
  TDAG DAG;
  Tstack_DAG stack_arg;
  stack_INIT(stack_arg);
  check_protected_symbol(symbol);
  for (i = 0; i < stack_var->size; i++)
    stack_push(stack_arg, DAG_new_args(stack_var->data[i], NULL));
  stack_push(stack_arg, term);
  DAG = DAG_dup(DAG_new_stack(LAMBDA, stack_arg));
  symb = DAG_symb_new(symbol, SYMB_MACRO, DAG_sort(DAG));
  DAG_symb_macro(symb, DAG);
  stack_free(stack_arg);
  stack_free(stack_var);
  DAG_free(term);
  free(symbol);
}

/*--------------------------------------------------------------*/

void
smt2_define_fun_short(char * symbol, TDAG term)
{
  Tsymb symb;
  check_protected_symbol(symbol);
  symb = DAG_symb_new(symbol, SYMB_MACRO, DAG_sort(term));
  DAG_symb_macro(symb, term);
  free(symbol);
}

/*--------------------------------------------------------------*/

void
smt2_push(char * numeral)
{
  unsigned n;
  char * tmp;
  long l;
  l = strtol(numeral, &tmp, 10);
  if (l < 0 || l > UINT_MAX)
    veriT_error("push: range");
  n = (unsigned) l;
  if (*tmp != '\0')
    veriT_error("smt2_push: internal error");
  if ((errno == ERANGE && n == UINT_MAX)
      || (errno != 0 && n == 0))
    veriT_error("push: range");
  veriT_push(n);
  free(numeral);
}

/*--------------------------------------------------------------*/

void
smt2_pop(char * numeral)
{
  unsigned n;
  char * tmp;
  long l;
  l = strtol(numeral, &tmp, 10);
  if (l < 0 || l > UINT_MAX)
    veriT_error("push: range");
  n = (unsigned) l;
  if (*tmp != '\0')
    veriT_error("smt2_push: internal error");
  if ((errno == ERANGE && n == UINT_MAX)
      || (errno != 0 && n == 0))
    veriT_error("push: range");
  veriT_pop(n);
  free(numeral);
}

/*--------------------------------------------------------------*/

void
smt2_assert(TDAG term)
{
  if (DAG_sort(term) != SORT_BOOLEAN)
    veriT_error("asserting a non Boolean term on line %d", yylineno);
  veriT_assert(term);
  
#if STATS_LEVEL > 1
  stats_counter_add(stat_nb_nodes, DAG_count_nodes(term));
  stats_counter_add(stat_nb_nodes_tree, DAG_count_nodes_tree(term));
  stats_counter_add(stat_nb_atoms, DAG_count_atoms(term));
#endif

  DAG_free(term);
}

/*--------------------------------------------------------------*/

void
smt2_check_sat(void)
{
  Tstatus status = veriT_check_sat();
  switch (status)
    {
    case UNSAT :
      veriT_out("unsat");
      stats_counter_set(stat_result, 0);
      break;
    case SAT   :
      veriT_out("sat");
      stats_counter_set(stat_result, 1);
      break;
    case UNDEF :
      veriT_out("unknown");
      stats_counter_set(stat_result, -1);
      /* TODO here include completion test */
      break;
    default : veriT_error("strange returned status");
    }
}

/*--------------------------------------------------------------*/

void
smt2_get_assertions(void)
{
  /* TODO */
  veriT_error("unsupported");
}

/*--------------------------------------------------------------*/

void
smt2_get_proof(void)
{
  /* TODO */
  veriT_error("unsupported");
}

/*--------------------------------------------------------------*/

void
smt2_get_unsat_core(void)
{
  /* TODO */
  veriT_error("unsupported");
}

/*--------------------------------------------------------------*/

void
smt2_get_model(void)
{
  veriT_model();
}

/*--------------------------------------------------------------*/

void
smt2_get_value(Tlist term_list)
{
  /* TODO */
  veriT_error("unsupported");
  list_free(&term_list);
}

/*--------------------------------------------------------------*/

void
smt2_get_assignment(void)
{
  /* TODO */
  veriT_error("unsupported");
}

/*--------------------------------------------------------------*/

void
smt2_get_info(char * keyword)
{
  switch (defstring(keyword))
    {
    case KW_ERROR_BEHAVIOR:
      veriT_out("%s \"%s\"", keyword, "immediate-exit");
      break;
    case KW_NAME:
      veriT_out("%s \"%s\"", keyword, "veriT");
      break;
    case KW_VERSION:
      /* TODO make-distrib script should fill this automatically */
      veriT_out("%s \"%s\"", keyword, PROGRAM_VERSION); 
      break;
    case KW_AUTHORS:
      veriT_out("%s \"%s\"", keyword, 
		"main developers: P. Fontaine, D. Deharbe"
		" - arithmetic: D. Caminha de Oliveira");
      break;
    case KW_STATUS:
      veriT_out("%s \"%s\"", keyword, smt2_status_str(veriT_status()));
      break;
    default:
      veriT_out("unsupported");
      break;
    }
  free(keyword);
}

/*--------------------------------------------------------------*/

void
smt2_get_option(char * keyword)
{
  switch (defstring(keyword))
    {
    case KW_PRINT_SUCCESS:
      veriT_out("%s \"%s\"", keyword, smt2_print_success ? "true" : "false");
      break;
    case KW_DIAGNOSTIC_OUTPUT_CHANNEL:
      veriT_out("%s \"%s\"", keyword, smt2_diagnostic_output_channel);
      break;
    case KW_REGULAR_OUTPUT_CHANNEL:
      veriT_out("%s \"%s\"", keyword, smt2_regular_output_channel);
      break;
    default:
      veriT_out("%s \"%s\"", keyword, "unsupported");
      break;
    }
  free(keyword);
}

/*--------------------------------------------------------------*/

void
smt2_exit(void)
{
  Tstatus status = veriT_status();
  if (smt2_status != UNDEF && status != UNDEF &&
      smt2_status != status)
    veriT_error("soundness error");
}

/*--------------------------------------------------------------*/


void
smt2_set_option(char * keyword)
{
  /* TODO */
  veriT_out("unsupported");
  free(keyword);
}

/*--------------------------------------------------------------*/

void
smt2_set_option_str(char * keyword, char * str)
{
  switch (defstring(keyword))
    {
    case KW_DIAGNOSTIC_OUTPUT_CHANNEL:
      if (strcmp(str, smt2_diagnostic_output_channel) != 0)
	{
	  free(smt2_diagnostic_output_channel);
	  smt2_diagnostic_output_channel = strmake(str);
	  veriT_set_err_file(str);
	}
      break;
    case KW_REGULAR_OUTPUT_CHANNEL:
      if (strcmp(str, smt2_regular_output_channel) != 0)
	{
	  free(smt2_regular_output_channel);
	  smt2_diagnostic_output_channel = strmake(str);
	  veriT_set_out_file(str);
	}
      break;
    default:
      veriT_out("unsupported");
    }
  free(keyword);
  free(str);
}

/*--------------------------------------------------------------*/

void
smt2_set_option_bool(char * keyword, unsigned int value)
{
  switch (defstring(keyword)) {
  case KW_PRINT_SUCCESS:
    smt2_print_success = value;
    break;
  default:
    veriT_out("unsupported");
    break;
  }
  /* TODO */
  free(keyword);
}

/*--------------------------------------------------------------*/


void
smt2_info(char * keyword)
{
  free(keyword);
}

/*--------------------------------------------------------------*/

void
smt2_info_str(char * keyword, char * str)
{
  switch (defstring(keyword))
    {
    case KW_CATEGORY :
      break;
    case KW_NOTES :
      break;
    case KW_STATUS :
      if (!strcmp(str,"sat"))
	smt2_status = SAT;
      else if (!strcmp(str,"unsat"))
	smt2_status = UNSAT;
      else if (!strcmp(str,"unknown"))
	smt2_status = UNDEF;
      break;
    case KW_SMT_LIB_VERSION :
      if (strcmp(str,"2.0"))
	my_warning("unknown SMT-LIB version\n");
      break;
    case KW_SOURCE :
      break;
    default :
      my_warning("discarding %s\n", keyword);
    }
  free(keyword);
  free(str);
}

/*
  --------------------------------------------------------------
  TDAG
  --------------------------------------------------------------
*/

TDAG
smt2_term_const(char * str)
{
  TDAG DAG = DAG_NULL;
  /* PF string may be:
     NUMERAL
     DECIMAL
     HEXADECIMAL
     BINARY
     STRING
  */
  if (str[0] == 0)
    veriT_error("unexpected constant on line %d", yylineno);
  else if (isdigit(str[0]))
    {
      if (check_decimal(str))
	DAG = DAG_new_decimal_str(str);
      else
	DAG = DAG_new_numeral_str(str);
    }
  else if (str[1] == 0)
    veriT_error("unexpected constant on line %d", yylineno);
  else if (str[0] == '#')
    {
      if (str[1] == 'b')
	{
	  check_binary(str + 2);
	  DAG = DAG_new_binary_str(str);
	}
      else if (str[1] == 'x')
	{
	  check_hex(str + 2);
	  DAG = DAG_new_hex_str(str);
	}
      else
	veriT_error("unexpected constant on line %d", yylineno);
    }
  else if (str[0] == '"')
    {
      check_str(str + 2);
      DAG = DAG_new_str(str);
    }
  else
    veriT_error("unexpected constant on line %d", yylineno);
  free(str);
  return DAG_dup(DAG);
}

/*--------------------------------------------------------------*/

TDAG
smt2_term(char * str)
{
  Tsymb symb = lookup_str(str);
  if (!symb)
    symb = DAG_symb_lookup(str, 0, NULL, DAG_SORT_NULL);
  if (!symb)
    veriT_error("unresolved symbol %s on line %d", str, yylineno);
  free(str);
  return DAG_dup(DAG_new_args(symb, DAG_NULL));
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_app(char * str, Tlist term_list)
{
  unsigned i, arity = list_length(term_list);
  Tsymb symb;
  TDAG *sub, DAG;
  MY_MALLOC(sub, arity * sizeof(TDAG));
  for (i = 0; i < arity; i++, term_list = list_cdr(term_list))
    sub[i] = DAG_of_ptr(list_car(term_list));
  assert(!(strcmp(str, "=") == 0) || arity >= 2);
  if (strcmp(str, "=") == 0)
    {
      if (DAG_sort(sub[0]) == SORT_BOOLEAN)
	symb = CONNECTOR_EQUIV;
      else
	symb = PREDICATE_EQ;
    }
  else if (strcmp(str, "ite") == 0)
    {
      if (DAG_sort(sub[0]) != SORT_BOOLEAN ||
	  DAG_sort(sub[1]) != DAG_sort(sub[2]))
	veriT_error("typing error in ite application on line %d.", yylineno);
      else if (DAG_sort(sub[1]) == SORT_BOOLEAN)
	symb = CONNECTOR_ITE;
      else
	symb = FUNCTION_ITE;
    }
  else
    {
      Tsort * Psort;
      MY_MALLOC(Psort, arity * sizeof(Tsort));
      for (i = 0; i < arity; i++)
	Psort[i] = DAG_sort(sub[i]);
      symb = DAG_symb_lookup(str, arity, Psort, DAG_SORT_NULL);
      free(Psort);
    }
  if (!symb)
    veriT_error("unresolved symbol %s on line %d.", str, yylineno);
  DAG = DAG_dup(DAG_new(symb, arity, sub));
  for (i = 0; i < arity; i++)
    DAG_free(DAG_arg(DAG, i));
  free(str);
  list_free(&term_list);
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
smt2_lambda_app(TDAG lambda, Tlist term_list)
{
  unsigned i, arity = list_length(term_list);
  TDAG *sub, DAG;
  MY_MALLOC(sub, (arity + 1) * sizeof(TDAG));
  sub[0] = lambda;
  for (i = 0; i < arity; i++, term_list = list_cdr(term_list))
    sub[i + 1] = DAG_of_ptr(list_car(term_list));
  DAG = DAG_dup(DAG_new(APPLY_LAMBDA, arity + 1, sub));
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_free(DAG_arg(DAG, i));
  list_free(&term_list);
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
smt2_iterm(char * str, Tlist numeral_list)
{
  veriT_error("unimplemented indexed symbol on line %d", yylineno);
  list_free(&numeral_list);
  free(str);
  /* should certainly free elements in numeral_list */
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

TDAG
smt2_iterm_app(char * str, Tlist term_list, Tlist numeral_list)
{
  veriT_error("unimplemented indexed symbol on line %d", yylineno);
  /*
  for (i = 0; i < arity; i++)
    DAG_free(DAG_arg(DAG, i));
  */
  list_free(&term_list);
  list_free(&numeral_list);
  free(str);
  /* should certainly free elements in numeral_list */
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

static Tsymb
qualified_symb(char * str, Tsort sort)
{
  Tsymb result;
  result = DAG_symb_lookup_sort(str, sort);
  if (result == DAG_SYMB_NULL)
    veriT_error("unresolved qualified symbol %s on line %d.", 
		str, yylineno);
  free(str);
  return result;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_s(char * str, Tsort sort)
{
  Tsymb symb;
  symb = qualified_symb(str, sort);
  if (symb == DAG_SYMB_NULL) 
    return DAG_NULL;
  return DAG_dup(DAG_new_args(symb, DAG_NULL));
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_app_s(char * str, Tlist term_list, Tsort sort)
{
  unsigned i, arity;
  Tsymb symb;
  TDAG *sub, DAG;
  symb = qualified_symb(str, sort);
  if (symb == DAG_SYMB_NULL)
    return DAG_NULL;
  arity = list_length(term_list);
  MY_MALLOC(sub, arity * sizeof(TDAG));
  for (i = 0; i < arity; i++, term_list = list_cdr(term_list))
    sub[i] = DAG_of_ptr(list_car(term_list));
  DAG = DAG_dup(DAG_new(symb, arity, sub));
  for (i = 0; i < arity; i++)
    DAG_free(DAG_arg(DAG, i));
  list_free(&term_list);
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
smt2_iterm_s(char * str, Tlist numeral_list, Tsort sort)
{
  veriT_error("unimplemented indexed identifier on line %d", yylineno);
  list_free(&numeral_list);
  free(str);
  /* should certainly free elements in numeral_list */
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

TDAG
smt2_iterm_app_s(char * str, Tlist term_list, Tlist numeral_list, Tsort sort)
{
  veriT_error("unimplemented indexed identifier on line %d", yylineno);
  /*
  for (i = 0; i < arity; i++)
    DAG_free(DAG_arg(DAG, i));
  */
  list_free(&term_list);
  list_free(&numeral_list);
  /* should certainly free elements in numeral_list */
  free(str);
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

TDAG
smt2_let(Tlist bind_list, TDAG term)
{
  TDAG DAG;
  Tlist list_DAG = NULL;
  if (!bind_list)
    veriT_error("ill-formed let on line %d", yylineno);
  LIST_LOOP_BEGIN(bind_list, Tbind, bind);
    list_DAG = list_add(list_DAG, DAG_ptr_of(DAG_dup(DAG_new_args(bind->symb, DAG_NULL))));
    list_DAG = list_add(list_DAG, DAG_ptr_of(bind->DAG));
  LIST_LOOP_END(bind_list);
  list_DAG = list_add(list_DAG, DAG_ptr_of(term));
  DAG = DAG_dup(DAG_new_list(LET, list_DAG));
  list_apply(list_DAG, (TFapply) DAG_free);
  list_free(&list_DAG);
  /* PF bind list will be freed in smt2_undeclare_bind_list */
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_binder(Tsymb binder, Tstack_symb stack_var, TDAG term,
		 const char * str)
{
  unsigned i;
  TDAG DAG;
  Tstack_DAG stack_arg;
  stack_INIT(stack_arg);
  if (!stack_var || !stack_var->size)
    veriT_error("ill-formed %s on line %d", str, yylineno);
  for (i = 0; i < stack_var->size; i++)
    stack_push(stack_arg, DAG_new_args(stack_var->data[i], DAG_NULL));
  stack_push(stack_arg, term);
  DAG = DAG_dup(DAG_new_stack(binder, stack_arg));
  stack_free(stack_arg);
  DAG_free(term);
  return DAG;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_forall(Tstack_symb stack_var, TDAG term)
{
  return smt2_term_binder(QUANTIFIER_FORALL, stack_var, term, 
			  "quantified formula");
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_exists(Tstack_symb stack_var, TDAG term)
{
  return smt2_term_binder(QUANTIFIER_EXISTS, stack_var, term, 
			  "quantified formula");
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_lambda(Tstack_symb stack_var, TDAG term)
{
  return smt2_term_binder(LAMBDA, stack_var, term, "lambda term");
}

/*--------------------------------------------------------------*/


TDAG
smt2_term_attr(TDAG term, char * keyword)
{
  veriT_error("unimplemented attributed term on line %d", yylineno);
  free(keyword);
  return term;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_attr_str(TDAG term, char * keyword, char * str)
{
  if (keyword && !strcmp(keyword, ":named"))
    {
      char * name = strmake(str);
      DAG_prop_set(term, DAG_PROP_NAMED, &name);
    }
  else
    veriT_error("unimplemented attributed term on line %d", yylineno);
  free(keyword);
  free(str);
  return term;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_attr_value(TDAG term, char * keyword, void * value)
{
  veriT_error("unimplemented attributed term on line %d", yylineno);
  free(keyword);
  return term;
}

/*--------------------------------------------------------------*/

TDAG
smt2_term_attr_named(TDAG term, char * str)
{
  DAG_prop_set(term, DAG_PROP_NAMED, &str);
  return term;
}

/*--------------------------------------------------------------*/

/*
  DAG_PROP_TRIGGER is a list of lists of DAGs.
  Each time a term_list has been parsed as the value of
  the :pattern keyword, it is added to the property
  value.
*/
TDAG
smt2_term_attr_pattern(TDAG formula, Tlist term_list)
{
  Tstack_DAGstack *Pannot = DAG_prop_get(formula, DAG_PROP_TRIGGER);
  Tstack_DAG trigger;
  stack_INIT_s(trigger, list_length(term_list));
  /* PF terms in term_list already have been DAG_dupped */
  while (term_list)
    {
      stack_push(trigger, DAG_of_ptr(list_car(term_list)));
      term_list = list_remove(term_list);
    }
  if (!Pannot)
    {
      Tstack_DAGstack annot;
      stack_INIT(annot);
      stack_push(annot, trigger);
      DAG_prop_set(formula, DAG_PROP_TRIGGER, &annot);
    }
  else
    stack_push(*Pannot, trigger);

  return formula;
}

/*--------------------------------------------------------------*/

Tbind
smt2_bind(char * symbol, TDAG term)
{
  Tbind bind;
  MY_MALLOC(bind, sizeof(struct TSbind));
  bind->symb = DAG_symb_lookup(symbol, 0, NULL, DAG_sort(term));
  if (!bind->symb)
    bind->symb = DAG_symb_new(symbol, SYMB_VARIABLE, DAG_sort(term));
  free(symbol);
  bind->DAG = term;
  return bind;
}

/*
  --------------------------------------------------------------
  Binders
  --------------------------------------------------------------
*/

void
smt2_declare_bind_list(Tlist bind_list)
{
  LIST_LOOP_BEGIN(bind_list, Tbind, bind);
    declare_str(DAG_symb_name(bind->symb), bind->symb);
  LIST_LOOP_END(bind_list);
}

/*--------------------------------------------------------------*/

void
smt2_undeclare_bind_list(Tlist bind_list)
{
  LIST_REVLOOP_BEGIN(bind_list, Tbind, bind);
  undeclare_str(DAG_symb_name(bind->symb), bind->symb);
  free(bind);
  LIST_REVLOOP_END(bind_list);
  list_free(&bind_list);
}

/*--------------------------------------------------------------*/

void
smt2_declare_stack_var(Tstack_symb stack_var)
{
  unsigned i;
  for (i = 0; i < stack_var->size; i++)
    declare_str(DAG_symb_name(stack_var->data[i]), stack_var->data[i]);
}

/*--------------------------------------------------------------*/

void
smt2_undeclare_stack_var(Tstack_symb stack_var)
{
  unsigned i;
  for (i = stack_var->size; i-- > 0;)
    undeclare_str(DAG_symb_name(stack_var->data[i]), stack_var->data[i]);
  /* PF Should we do this? free(symb); */
  stack_free(stack_var);
}

/*
  --------------------------------------------------------------
  Tsymb
  --------------------------------------------------------------
*/

Tsymb
smt2_var(char * symbol, Tsort sort)
{
  Tsymb symb = DAG_symb_lookup(symbol, 0, NULL, sort);
  if (!symb)
    symb = DAG_symb_new(symbol, SYMB_VARIABLE, sort);
  if (!symb)
    veriT_error("unable to create variable %s on line", symbol, yylineno);
  free(symbol);
  return symb;
}

/*
  --------------------------------------------------------------
  Sorts
  --------------------------------------------------------------
*/

/**
   \author David Deharbe
   \brief Creates a sort variable
   \param str The name of the sort variable
*/
Tsort
smt2_sort_var(char * str)
{
  Tsort sort = DAG_SORT_NULL;
  sort = DAG_sort_new_var(str);
  free(str);
  return sort;
}

/*--------------------------------------------------------------*/

Tlist
smt2_sort_var_list_one(Tsort sort)
{
  return list_add(NULL, ptr_of_sort(sort));
}

/*--------------------------------------------------------------*/

Tlist
smt2_sort_var_list_add(Tlist sort_var_list, Tsort sort)
{
  return list_add(sort_var_list, ptr_of_sort(sort));
}

/*--------------------------------------------------------------*/

void 
smt2_declare_sort_var_list(T_SORT_LIST sort_list)
{
}

/*--------------------------------------------------------------*/

void 
smt2_undeclare_sort_var_list(T_SORT_LIST sort_list)
{
}

/*--------------------------------------------------------------*/

/** 
    \author Pascal Fontaine
    \brief check if the sort is parametric
    \param sort the sort to check
*/
int
smt2_sort_parametric(Tsort sort)
{
  return DAG_sort_parametric(sort);
}

/*--------------------------------------------------------------*/

Tsort
smt2_sort_lookup(char * symbol)
{
  Tsort sort = DAG_sort_lookup(symbol);
  if (!sort)
    veriT_error("undefined sort %s on line %d", symbol, yylineno);
  free(symbol);
  return sort;
}

/*--------------------------------------------------------------*/

Tsort
smt2_sort_lookup_index(char * symbol, Tlist sort_list)
{
  veriT_error("unimplemented");
  list_free(&sort_list);
  return DAG_SORT_NULL;
}

/*--------------------------------------------------------------*/

Tsort
smt2_sort_functional(Tlist sort_list)
{
  unsigned i, arity = list_length(sort_list);
  Tsort *sub;
  MY_MALLOC(sub, arity * sizeof(Tsort));
  for (i = 0; i < arity; i++, sort_list = list_cdr(sort_list))
    sub[i] = sort_of_ptr(list_car(sort_list));
  list_free(&sort_list);
  return DAG_sort_new(NULL, arity, sub);
}

/*--------------------------------------------------------------*/

Tsort
smt2_sort_apply(Tsort sort, Tlist sort_list)
{
  unsigned i, arity;
  Tsort *sub, result;
  arity = list_length(sort_list);
  MY_MALLOC(sub, arity*sizeof(Tsort));
  for (i = 0; i < arity; ++i, sort_list = list_cdr(sort_list))
    {
      Tsort sort2 = DAG_sort_of_ptr(list_car(sort_list));
      if (!sort2) 
	my_error("line %d: unknown sort %s.", yylineno, DAG_sort_name(sort2));
      sub[i] = sort2;
    }
  if (arity != DAG_sort_arity(sort))
    veriT_error("wrong number of sort arguments for %s on line %i", 
		DAG_sort_name(sort), yylineno);
  result = DAG_sort_new_inst(NULL, sort, arity, sub);
  list_free(&sort_list);
  return result;
}


/*
  --------------------------------------------------------------
  List building functions
  --------------------------------------------------------------
*/

Tlist
smt2_term_list_one(TDAG term)
{
  return list_add(NULL, DAG_ptr_of(term));
}

/*--------------------------------------------------------------*/

Tlist
smt2_term_list_add(Tlist term_list, TDAG term)
{
  return list_add(term_list, DAG_ptr_of(term));
}

/*--------------------------------------------------------------*/

Tlist
smt2_numeral_list_one(char * numeral)
{
  return list_add(NULL, (void *) numeral);
}

/*--------------------------------------------------------------*/

Tlist
smt2_numeral_list_add(Tlist numeral_list, char * numeral)
{
  return list_add(numeral_list, (void *) numeral);
}

/*--------------------------------------------------------------*/

Tlist
smt2_bind_list_new(void)
{
  return NULL;
}

/*--------------------------------------------------------------*/

Tlist
smt2_bind_list_one(Tbind bind)
{
  return list_add(NULL, (void *) bind);
}

/*--------------------------------------------------------------*/

Tlist
smt2_bind_list_add(Tlist bind_list, Tbind bind)
{
  return list_add(bind_list, (void *) bind);
}

/*--------------------------------------------------------------*/

Tstack_symb
smt2_stack_var_new(void)
{
  Tstack_symb stack_var;
  stack_INIT(stack_var);
  return stack_var;
}

/*--------------------------------------------------------------*/

Tstack_symb
smt2_stack_var_one(Tsymb var)
{
  Tstack_symb stack_var;
  stack_INIT(stack_var);
  stack_push(stack_var, var);
  return stack_var;
}

/*--------------------------------------------------------------*/

Tstack_symb
smt2_stack_var_add(Tstack_symb stack_var, Tsymb var)
{
  stack_push(stack_var, var);
  return stack_var;
}

/*--------------------------------------------------------------*/

Tlist
smt2_sort_list_new(void)
{
  return NULL;
}

/*--------------------------------------------------------------*/

Tlist
smt2_sort_list_one(Tsort sort)
{
  return list_add(NULL, DAG_ptr_of_sort(sort));
}

/*--------------------------------------------------------------*/

Tlist
smt2_sort_list_add(Tlist sort_list, Tsort sort)
{
  return list_add(sort_list, DAG_ptr_of_sort(sort));
}

/*--------------------------------------------------------------*/


Tlist
smt2_symbol_list_new(void)
{
  return NULL;
}

/*--------------------------------------------------------------*/

Tlist
smt2_symbol_list_add(Tlist symbol_list, char * symbol)
{
  return list_add(symbol_list, (void *) symbol);
}

/*--------------------------------------------------------------*/

void 
smt2_command(void)
{
  if (smt2_print_success)
    veriT_out("success");
} 

/*
  --------------------------------------------------------------
  module init and done
  --------------------------------------------------------------
*/

void
smt2_init(bool option_disable_print_success)
{
  hashmap_str = hashmap_new(200, (TFhash)hash_function,
			    (TFequal)hash_str_equal,
			    (TFfree)hash_key_free,
			    (TFfree)hash_value_free);
  stat_result = stats_counter_new("res", "0 (UNSAT), 1 (SAT), -1 (UNKNOWN)",
				  "%5d");
  smt2_print_success = !option_disable_print_success;
  smt2_diagnostic_output_channel = strmake("stderr");
  smt2_regular_output_channel = strmake("stdout");
#if STATS_LEVEL > 1
  stat_nb_nodes = stats_counter_new("nodes",
				    "Number of nodes in the input formula"
				    " as a DAG representation", "%6d");
  stat_nb_nodes_tree = stats_counter_new("nodes_tree",
					 "Number of nodes in the input"
					 " formula as a tree"
					 " representation",
					 "%6d");
  stat_nb_atoms = stats_counter_new("atoms",
				    "Number of atoms in the input"
				    " formula as a tree representation",
				    "%6d");
#endif
}

/*--------------------------------------------------------------*/

void
smt2_done(void)
{
  free(smt2_regular_output_channel);
  free(smt2_diagnostic_output_channel);
  hashmap_free(&hashmap_str);
}

