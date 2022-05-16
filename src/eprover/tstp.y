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

/* File header */

/* C declarations */
%{
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "general.h"

#include "DAG.h"
#include "DAG-ptr.h"
#include "hash.h"
#include "list.h"
#include "table.h"

#include "eprover-int.h"
#include "tstp-parser.h"

#include "tstpfun.h"
  
extern int tstp_lex(void);
%}
/* terminal and non-terminal value types */
%union{
  Tsymb symb;
  TDAG term;
  Tlist string_list;
  Tlist symb_list;
  Tlist term_list;
  Tlist uint_list;
  char* string;
  Trole formula_role;
  Tbinary_connective binary_connective;
  Tpremisse premisse;
  Tlist premisse_list;
  uintptr_t uint;
}

/* keywords */
%token TK_AC "ac"
%token TK_ANSWERS "answers"
%token TK_ASSUMPTION "assumption"
%token TK_AXIOM "axiom"
%token TK_AXIOM_OF_CHOICE "axiom_of_choice"
%token TK_CNF "cnf"
%token TK_CONJECTURE "conjecture"
%token TK_CREATOR "creator"
%token TK_DEFINITION "definition"
%token TK_DESCRIPTION "description"
%token TK_EQUALITY "equality"
%token TK_EQUALITY_S "equality:s"
%token TK_FOF "fof"
%token TK_FILE "file"
%token TK_HYPOTHESIS "hypothesis"
%token TK_INCLUDE "include"
%token TK_INFERENCE "inference"
%token TK_INTRODUCED "introduced"
%token TK_IQUOTE "iquote"
%token TK_LEMMA "lemma"
%token TK_LEMMA_CONJECTURE "lemma_conjecture"
%token TK_NEGATED_CONJECTURE "negated_conjecture"
%token TK_PLAIN "plain"
%token TK_REFUTATION "refutation"
%token TK_STATUS "status"
%token TK_SYMMETRY "symmetry"
%token TK_TAUTOLOGY "tautology"
%token TK_THEOREM "theorem"
%token TK_THEORY "theory"
%token TK_UNKNOWN "unkown"

/* operators */
%token TK_AND "&"
%token TK_DIFF "!="
%token TK_EQU "="
%token TK_EQUAL "$equal"
%token TK_EQV "<=>"
%token TK_FALSE "$false"
%token TK_LIMPL "<="
%token TK_NEQV "<~>"
%token TK_NAND "~&"
%token TK_NEQ "$neq"
%token TK_NOR "~|"
%token TK_NOT "~"
%token TK_OR "|"
%token TK_RIMPL "=>"
%token TK_TRUE "$true"
%token TK_BANG "!"
%token TK_QUESTION_MARK "?"
%token TK_PLUS "+"
%token TK_MINUS "-"

/* separators */
%token TK_COLON ":"
%token TK_COMMA ","
%token TK_DOT "."
%token TK_LP "("
%token TK_LSQ "["
%token TK_RP ")"
%token TK_RSQ "]"

 /* valued tokens */
%token REAL
%token <string> UPPER_WORD
%token <string> LOWER_WORD
%token <string> SINGLE_QUOTED
%token <term> TERM
%token <symb> SYMB
%token DOUBLE_QUOTED

%token <string> PERCENT_COMMENT

%type <term> fof_formula
%type <term> fof_binary_formula
%type <term> fof_binary_non_assoc
%type <term> fof_binary_assoc
%type <term> fof_or_formula
%type <term_list> fof_or_unitary_formula_list1
%type <term> fof_and_formula
%type <term_list> fof_and_list
%type <term> fof_unitary_formula
%type <term> fof_quantified_formula
%type <term_list> fof_variable_list
%type <term> fof_unary_formula
%type <term> cnf_formula
%type <term_list> disjunction
%type <term> literal
%type <term> fol_infix_unary
%type <symb> fol_quantifier
%type <binary_connective> binary_connective
%type <term> atomic_formula
%type <term> plain_atomic_formula
%type <term> defined_atomic_formula 
%type <term> defined_plain_formula
%type <term> defined_prop
%type <term> defined_infix_formula
%type <term> term
%type <term> function_term
%type <term> constant
%type <symb> functor
%type <term> qvariable
%type <term> variable
%type <term_list> arguments
%type <premisse_list> annotations
%type <premisse_list> source
%type <premisse_list> dag_source
%type <premisse_list> inference_record
%type <premisse_list> parent_info_list1_comma
%type <premisse_list> parent_info
%type <premisse_list> external_source
%type <premisse_list> file_source
%type <premisse> name
%type <formula_role> formula_role
%type <string> atomic_word
%start tptp_file

%%

 /*

%----v5.2.0.0 (TPTP version.internal development number)
%------------------------------------------------------------------------------
%----README ... this header provides important meta- and usage information
%----
%----Intended uses of the various parts of the TPTP syntax are explained
%----in the TPTP technical manual, linked from www.tptp.org.
%----
%----Four kinds of separators are used, to indicate different types of rules:
%----  ::= is used for regular grammar rules, for syntactic parsing.
%----  :== is used for semantic grammar rules. These define specific values
%----      that make semantic sense when more general syntactic rules apply.
%----  ::- is used for rules that produce tokens.
%----  ::: is used for rules that define character classes used in the
%----       construction of tokens.
%----
%----White space may occur between any two tokens. White space is not specified
%----in the grammar, but there are some restrictions to ensure that the grammar
%----is compatible with standard Prolog: a <TPTP_file> should be readable with
%----read/1.
%----
%----The syntax of comments is defined by the <comment> rule. Comments may
%----occur between any two tokens, but do not act as white space. Comments
%----will normally be discarded at the lexical level, but may be processed
%----by systems that understand them (e.g., if the system comment convention
%----is followed).
%----
%----Four languages are defined first - THF, TFF, FOF, and CNF. Depending on
%----your need, you can implement just the one(s) you need. The common rules
%----for atoms, terms, etc, come after the definitions of the languages, and
%----they are all needed for all four languages (except for the core THF0,
%----which is a defined subset of THF).
%------------------------------------------------------------------------------
/*

/* %----Files. Empty file is OK. */
/* <TPTP_file>          ::= <TPTP_input>*  */

tptp_file: tptp_input_list
;

tptp_input_list: 
| tptp_input_list tptp_input
;

/* <TPTP_input>         ::= <annotated_formula> | <include> [DD -] */
/*                      | <comment> [DD +]                  */

tptp_input:
annotated_formula
| comment
;

/*
%----Formula records
<annotated_formula>  ::= <thf_annotated> [DD -] | <tff_annotated> [DD -]
                         | <fof_annotated> | <cnf_annotated>
%----Future languages may include ...  english | efof | tfof | mathml | ...
*/

annotated_formula:
fof_annotated
| cnf_annotated
;

/* <fof_annotated>      ::= fof(<name>,<formula_role>,<fof_formula><annotations>). */
fof_annotated:
TK_FOF TK_LP name TK_COMMA formula_role TK_COMMA fof_formula annotations TK_RP TK_DOT
  { tstp_inference ($3, $5, $7, $8); } 
;

/* <cnf_annotated>      ::= cnf(<name>,<formula_role>,<cnf_formula><annotations>). */
cnf_annotated:
TK_CNF TK_LP name TK_COMMA formula_role TK_COMMA cnf_formula annotations TK_RP TK_DOT
  { tstp_inference ($3, $5, $7, $8); } 
;

/* <annotations>        ::= ,<source><optional_info> | <null> */

/* <annotations>        ::= <null> | ,<source> | ,<source>,<useful info> */
/* returns the list of names of premisses */
annotations:
  { $$ = NULL; }
| TK_COMMA source { $$ = $2; }
| TK_COMMA source TK_COMMA useful_info { $$ = $2; }
;

/*
%----Types for problems.
%----Note: The previous <source_type> from ...
%----   <formula_role> ::= <user_role>-<source>
%----... is now gone. Parsers may choose to be tolerant of it for backwards
%----compatibility.
<formula_role>       ::= <lower_word>
<formula_role>       :== axiom | hypothesis | definition | assumption |
                         lemma | theorem | conjecture | negated_conjecture |
                         plain | fi_domain [DD -]| fi_functors [DD -]| 
			 fi_predicates [DD -]| type [DD -] | unknown

*/
formula_role:
TK_AXIOM { $$ = AXIOM; } | 
TK_HYPOTHESIS { $$ = HYPOTHESIS; } | 
TK_DEFINITION { $$ = DEFINITION; } | 
TK_LEMMA { $$ = LEMMA; } | 
TK_THEOREM { $$ = THEOREM; } | 
TK_CONJECTURE { $$ = CONJECTURE; } | 
TK_LEMMA_CONJECTURE { $$ = LEMMA_CONJECTURE; } | 
TK_NEGATED_CONJECTURE { $$ = NEGATED_CONJECTURE; } | 
TK_PLAIN { $$ = PLAIN; } | 
TK_UNKNOWN { $$ = UNKNOWN; }
;

/*
%------------------------------------------------------------------------------
%----FOF formulae.
<fof_formula>        ::= <fof_logic_formula> | <fof_sequent> [DD -]
<fof_logic_formula>  ::= <fof_binary_formula> | <fof_unitary_formula>
*/

fof_formula: 
fof_binary_formula { $$ = $1; }
| fof_unitary_formula { $$ = $1; }
;

/* <fof_binary_formula> ::= <fof_binary_nonassoc> | <fof_binary_assoc> */
fof_binary_formula:
fof_binary_non_assoc { $$ = $1; }
| fof_binary_assoc   { $$ = $1; }
;

/*
%----Only some binary connectives are associative
%----There's no precedence among binary connectives
<fof_binary_nonassoc> ::= <fof_unitary_formula> <binary_connective>
                         <fof_unitary_formula>
*/
fof_binary_non_assoc:
fof_unitary_formula binary_connective fof_unitary_formula 
  { $$ = tstp_binary_connective ($2, $1, $3); } 
;

/* %----Associative connectives & and | are in <binary_assoc> */
/* <fof_binary_assoc>   ::= <fof_or_formula> | <fof_and_formula> */

fof_binary_assoc:
fof_or_formula { $$ = $1; }
| fof_and_formula { $$ = $1; }
;

/* <fof_or_formula>     ::= <fof_unitary_formula> <vline> <fof_unitary_formula> |
   <fof_or_formula> <vline> <fof_unitary_formula> */

fof_or_formula:
fof_unitary_formula TK_OR fof_or_unitary_formula_list1 
{ $$ = tstp_or(list_cons(DAG_ptr_of($1), $3)); }
;

fof_or_unitary_formula_list1:
fof_unitary_formula { $$ = list_add(NULL, DAG_ptr_of($1)); }
| fof_or_unitary_formula_list1 TK_OR fof_unitary_formula 
{ $$ = list_add ($1, DAG_ptr_of($3)); }
;

/* <fof_and_formula>    ::= <fof_unitary_formula> & <fof_unitary_formula> |
                         <fof_and_formula> & <fof_unitary_formula> */

fof_and_formula:
fof_unitary_formula TK_AND fof_and_list 
{ $$ = tstp_and (list_cons(DAG_ptr_of($1), $3)); }
;

fof_and_list:
fof_unitary_formula { $$ = list_add(NULL, DAG_ptr_of($1)); }
| fof_and_list TK_AND fof_unitary_formula { $$ = list_add($1, DAG_ptr_of($3)); }
;

/*
%----<fof_unitary_formula> are in ()s or do not have a <binary_connective> at
%----the top level.
<fof_unitary_formula> ::= <fof_quantified_formula> | <fof_unary_formula> |
                         <atomic_formula> | <fof_let> [DD -]| <variable> |
                         <fof_conditional> [DD -] | (<fof_logic_formula>)
%----<variable>s make sense only when they are the <term> of a <fof_let>.
%----<fof_let>, <variable>, and <fof_conditional> are part of FOFX.
*/
fof_unitary_formula:
fof_quantified_formula          { $$ = $1; }
| fof_unary_formula             { $$ = $1; }
| atomic_formula                { $$ = $1; }
| TK_LP fof_formula TK_RP { $$ = $2; }
;

/*
<fof_quantified_formula> ::= <fol_quantifier> [<fof_variable_list>] : <fof_unitary_formula>
%----! is universal quantification and ? is existential. Syntactically, the
%----quantification is the left operand of :, and the <fof_unitary_formula> is
%----the right operand. Although : is a binary operator syntactically, it is
%----not a <binary_connective>, and thus a <quantified_formula> is a
%----<fof_unitary_formula>.
%----Universal   example: ! [X,Y] : ((p(X) & p(Y)) => q(X,Y)).
%----Existential example: ? [X,Y] : (p(X) & p(Y)) | ~ q(X,Y).
%----Quantifiers have higher precedence than binary connectives, so in
%----the existential example the quantifier applies to only (p(X) & p(Y)).
*/

fof_quantified_formula:
fol_quantifier TK_LSQ fof_variable_list TK_RSQ TK_COLON fof_unitary_formula
{ $$ = tstp_quantified_formula($1, &$3, $6); }
;


/* <fof_variable_list>  ::= <variable> | <variable>,<fof_variable_list> */

/* DD Non-terminal <qvariable> is used in place of <variable> since 
   different actions are needed when variable is declared and used */
fof_variable_list: 
qvariable  { $$ = list_add(NULL, DAG_ptr_of($1)); }
| fof_variable_list TK_COMMA qvariable { $$ = list_add($1, DAG_ptr_of($3)); }
;

/*
<fof_unary_formula>  ::= <unary_connective> <fof_unitary_formula> |
                         <fol_infix_unary>
<unary_connective>   ::= ~ */
fof_unary_formula:
TK_NOT fof_unitary_formula { $$ = DAG_not($2); }
| fol_infix_unary { $$ = $1; }
;

/*
%------------------------------------------------------------------------------
%----CNF formulae (variables implicitly universally quantified)
*/
/* <cnf_formula>        ::= (<disjunction>) | <disjunction> */

cnf_formula:
TK_LP disjunction TK_RP { $$ = tstp_cnf_formula ($2); }
| disjunction { $$ = tstp_cnf_formula ($1); }
;

/* <disjunction>        ::= <literal> | <disjunction> <vline> <literal> */
disjunction:
literal { $$ = list_add(NULL, DAG_ptr_of($1)); }
| disjunction TK_OR literal { $$ = list_add($1, DAG_ptr_of($3)); }
;

/* <literal> ::= <atomic_formula> | ~ <atomic_formula> | <fol_infix_unary> */
literal:
atomic_formula { $$ = $1; }
| TK_NOT atomic_formula { $$ = DAG_not($2); }
| fol_infix_unary { $$ = $1; }
;

/* %------------------------------------------------------------------------------
   %----Special formulae
   <fol_infix_unary>    ::= <term> <infix_inequality> <term>
   <infix_inequality>   ::= != 
*/
fol_infix_unary: 
term TK_DIFF term { $$ = tstp_equality ($1, $3, POL_NEG); }
;

/* %----Connectives - FOF */
/* <fol_quantifier>     ::= ! | ? */
fol_quantifier:
TK_BANG { $$ = QUANTIFIER_FORALL; }
| TK_QUESTION_MARK { $$ = QUANTIFIER_EXISTS; }

/* <binary_connective>  ::= <=> | => | <= | <~> | ~<vline> | ~&  */
binary_connective:
TK_EQV { $$ = EQV; } 
| TK_RIMPL { $$ = RIMPL; } 
| TK_LIMPL { $$ = LIMPL; } 
| TK_NEQV { $$ = NEQV; } 
| TK_NOR { $$ = NOR; } 
| TK_NAND { $$ = NAND; }
;

/* %----First order atoms */

/* <atomic_formula>     ::= <plain_atomic_formula> | <defined_atomic_formula> |
   <system_atomic_formula> [DD -] */
atomic_formula:
plain_atomic_formula
| defined_atomic_formula
;

/* <plain_atomic_formula> ::= <plain_term> */
/* <plain_atomic_formula> :== <proposition> | <predicate>(<arguments>) */
plain_atomic_formula :
term { $$ = $1; }
;

/* %----Using <plain_term> removes a reduce/reduce ambiguity in lex/yacc.
   %----Note: "defined" means a word starting with one $ and "system" means $$. */

/* <defined_atomic_formula> ::= <defined_plain_formula> | <defined_infix_formula> */
defined_atomic_formula:
defined_plain_formula { $$ = $1; }
| defined_infix_formula { $$ = $1; }
;

/* <defined_plain_formula> ::= <defined_plain_term>
   <defined_plain_formula> :== <defined_prop> | <defined_pred>(<arguments>)
   <defined_pred>       :== <atomic_defined_word>
   <defined_pred>       :== $equal | $distinct [DD -]| $itef [DD -]|
   $less [DD -]| $lesseq [DD -]| $greater [DD -]| $greatereq [DD -]| 
   $evaleq [DD -]| $is_int [DD -]| $is_rat [DD -]
*/
defined_plain_formula:
defined_prop { $$ = $1; }
| TK_EQUAL TK_LP term TK_COMMA term TK_RP 
    { $$ = tstp_equality($3, $5, POL_POS); }
| TK_NEQ TK_LP term TK_COMMA term TK_RP 
    { $$ = tstp_equality($3, $5, POL_NEG); }
;

/* <defined_prop>       :== <atomic_defined_word>
   <defined_prop>       :== $true | $false */
defined_prop:
TK_TRUE { $$ = DAG_TRUE; }
| TK_FALSE { $$ = DAG_FALSE; }
;

/* <defined_infix_formula>  ::= <term> <defined_infix_pred> <term>
   <defined_infix_pred> ::= <infix_equality>
   <inflix_equality> ::= = */
defined_infix_formula:
term TK_EQU term { $$ = tstp_equality ($1, $3, POL_POS); }
;

/* %----First order terms */
/* <term>            ::= <function_term> | <variable> | <conditional_term> [DD -] */

term:
function_term
    { $$ = $1; }
| variable
    { $$ = $1; }
;

/* <function_term>   ::= <plain_term> | <defined_term> [DD -] | <system_term> [DD -]
   <plain_term>         ::= <constant> | <functor>(<arguments>) */
function_term:
constant
{ $$ = $1; }
| functor TK_LP arguments TK_RP
{ $$ = tstp_function_term($1, $3); }
;

/* <constant>           ::= <functor> [DD -]
   <constant>           ::= <symb_word> | <abstract_term> [DD +] */

constant:
SYMB { $$ = DAG_new($1, 0, NULL); }
| TERM { $$ = $1; }
;

/* <functor>            ::= <atomic_word> */
functor:
SYMB { $$ = $1; }
;

/* %----Variables, and only variables, start with uppercase */
/*<variable>           ::= <upper_word> */
/* DD: one non-terminal for occurence as argument to a quantifier */
qvariable: 
UPPER_WORD { $$ = tstp_quantified_variable($1); } 
;
/* DD: one terminal for occurence in a term */
variable: 
UPPER_WORD { $$ = tstp_expression_variable ($1); }
;

/* %----Arguments recurse back up to terms (this is the FOF world here)
   <arguments>          ::= <term> | <term>,<arguments> */
arguments:
term { $$ = list_add(NULL, DAG_ptr_of($1)); }
| arguments TK_COMMA term { $$ = list_add($1, DAG_ptr_of($3)); }

/* %----Formula sources
   <source>             ::= <dag source> | <internal source> | 
                            <external source> | unknown [DD-]
*/
source:
dag_source        { $$ = $1; }
| internal_source { $$ = NULL; }
| external_source { $$ = $1; }
;

/*
  %----Only a <dag source> can be a <name>, i.e., derived formulae can be
  %----identified by a <name> or an <inference record> 
  <dag source>         ::= <name> | <inference record>
*/
dag_source:
name { $$ = list_add(NULL, (void *) $1); }
| inference_record { $$ = $1; }
;

/* <inference record>   ::= inference(<inference rule>,<useful info>,
   [<parent info><rest parent info>*])
*/
inference_record: 
TK_INFERENCE TK_LP inference_rule TK_COMMA useful_info TK_COMMA 
TK_LSQ parent_info_list1_comma TK_RSQ TK_RP
{ $$ = $8; }
;

/* <inference rule>     ::= <atomic word> */
inference_rule: 
atomic_word { free ($1); }
;
/*
Examples are        deduction | modus_tollens | modus_ponens | rewrite | 
                    resolution | paramodulation | factorization | 
                    cnf_conversion | cnf_refutation | ...
*/
/* <rest parent info>   ::= ,<parent info>
   <parent info>        ::= <source><parent details>
*/
parent_info_list1_comma:
parent_info
{ 
  $$ = $1; 
}
| parent_info_list1_comma TK_COMMA parent_info
{ $$ = list_merge($1, $3); }
;

parent_info: 
source
{ $$ = $1; }
;

/* <external source>    ::= <file source> | <theory> | <creator source> [DD-] */
external_source:
file_source { $$ = $1; }
| theory    { $$ = NULL; }
;
/*
  <internal_source>    :== introduced(<intro_type><optional_info>)
  <intro_type>         :== definition | axiom_of_choice | tautology | assumption
*/
internal_source:
TK_INTRODUCED TK_LP intro_type optional_info TK_RP
;

intro_type:
TK_DEFINITION | TK_AXIOM_OF_CHOICE | TK_TAUTOLOGY | TK_ASSUMPTION;

/* <theory>             :== theory(<theory_name>[DD -<optional_info>])
   <theory_name>        :== equality | ac | answers [DD +]*/
theory:
TK_THEORY TK_LP theory_name optional_info TK_RP
;

theory_name:
TK_AC 
| TK_ANSWERS 
| TK_EQUALITY
| TK_EQUALITY_S
;

optional_info:
| TK_COMMA TK_LSQ TK_SYMMETRY TK_RSQ

/*
  <file source>        ::= file(<file name>,<file node name>)
  <file name>          ::= <single quoted>
  <file node name>     ::= <name> | unknown [DD-]*/
file_source: 
TK_FILE TK_LP SINGLE_QUOTED TK_COMMA name TK_RP
{
  $$ = list_add(NULL, (void *)$5);
  free($3);
}
;


/* %----Useful info fields */

/* <useful info>        ::= [] | [<info items>] */
useful_info: 
TK_LSQ TK_RSQ
| TK_LSQ info_items TK_RSQ
;

/* 
<info items>         ::= <info item><rest of info items>*
<rest of info items> ::= ,<info item> */
info_items:
info_item_list1_comma
;

info_item_list1_comma:
info_item
| info_item_list1_comma TK_COMMA info_item
;

/* <info item>          ::= <formula item> [DD-] | <inference item> | <general function>[DD-] */
/* <inference item>     ::= <inference status> | <refutation> [DD-]*/
/* DD The output from E does not seem to comply to the restrictions
   for info_item, it is just a general term, that we restrict here as
   an "atomic word". */
info_item:
  TK_STATUS TK_LP status_value TK_RP 
| atomic_word
;

/* These are the status values from the SZS ontology
   <status value>       ::=    tau | tac | eqv | thm | sat | cax | noc | csa | cth |
   ceq | unc | uns | sab | sam | sar | sap | csp | csr |
   csm | csb 
*/
status_value: 
LOWER_WORD { free ($1); }
;

/* %----Comments. These may be retained for non-logical purposes. Comments
   %----can occur only between annotated formulae (see <TPTP input>), but
   %----it seems likely that people will put them elsewhere and simply
   %----strip them before tokenising.
   <comment>            ::= %<char until eoln>* | /<star><char>*<star>/

   DD: C-like comments are handled by the lexer.
*/
comment: 
PERCENT_COMMENT { tstp_comment ($1); }
;

/* 
%----Annotations are used for system specific annotation of anything. Notice
%----that they look like comments, so by default they are discarded. However,
%----a wily user of the syntax can notice the @ and store/extract information 
%----from the "comment". System specific annotations should identify the 
%----system. 
<system comment>     ::= %$$<char until eoln>* | /<star>$$<char>*<star>/ 
*/

/* %----The following are reserved <name>s: unknown file inference creator */
/* <name>               ::= <atomic word> | <unsigned integer> */
name:
atomic_word
{
  if (is_internal_name($1))
    $$ = premisse_of_internal($1);
  else if (is_external_name($1))
    $$ = premisse_of_external($1);
  else
    $$ = 0;
  free ($1);
}
;

/* <atomic word>        ::= <lower word> | <single quoted> */
atomic_word:
LOWER_WORD { $$ = $1; }
| SINGLE_QUOTED { $$ = tstp_single_quoted($1); }
;

/* see tokenizer
   <real>               ::= <integer><decimal part>
   <unsigned integer>   ::= <0-9>+
   <decimal part>       ::= .<0-9>+ | <null>
   %----All strings are implicitly distinct
   <double quoted>      ::= "<char>*"
   <char>               ::= ... any printable ASCII character
   <vline>              ::= ... a vertical line character
   <star>               ::= ... a star character
   <plus>               ::= ... a plus character
*/

%%
