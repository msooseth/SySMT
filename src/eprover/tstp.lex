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

/* file header */
%{
#include <stdlib.h>

#include "general.h"

#include "eprover-int.h"
#include "tptp-logic.h"
#include "tstp-parser.h"
#include "tstpsyn.h"

extern int tstp_lineno;

%}
%option noyywrap
%x c_comment

/* <upper word>         ::= <A-Z><a-z0-9A-Z_>* */
upper_word      [A-Z][a-zA-Z0-9_]*
/* <epred symbol>      ::= <a-z><a-z0-9A-Z_>*   DD: this is specific to E */
epred_symbol   epred[0-9]+_[0-9]+
/* <skolem symbol>      ::= <a-z><a-z0-9A-Z_>*  DD: this is specific to E */
skolem_symbol   esk[0-9]+_[0-9]+
/* <lower word>         ::= <a-z><a-z0-9A-Z_>* */
lower_word      [a-z][a-zA-Z0-9_]*
/* <symbol pointer>      ::= 's0xhexadigit*' */ 
symbol_pointer   \'s[a-fA-F0-9]+\'
/* <term_pointer>      ::= 't0xhexadigit*' */ 
term_pointer   \'t[a-fA-F0-9]+\'
/* <single quoted>      ::= '<char>*' */ 
single_quoted   \'[^\'\n]*\'
/* <double quoted>      ::= "<char>*" */
double_quoted   \"[^\"\n]*\"
/* <real>               ::= <integer><decimal part>
   <sign>               ::= + | - | <null>
   <unsigned integer>   ::= <0-9>+
   <decimal part>       ::= .<0-9>+ | <null> */
/* DD: we cannot maintain the ambiguity in the TPTP3/TSTP definition that
   any integer is also a real */
unsigned_integer         [0-9]+
integer         [\-\+]?{unsigned_integer}
decimal_part    \.[0-9]*
real {integer}{decimal_part}
percent_comment \#[^\n]*
%%
"/*"         BEGIN(c_comment); 

<c_comment>[^*\n]*
<c_comment>[^*\n]*\n      { ++tstp_lineno; }
<c_comment>"*"+[^*/\n]*
<c_comment>"*"+[^*/\n]*\n { ++tstp_lineno; }
<c_comment>"*"+"/"        BEGIN(INITIAL);
<c_comment><<EOF>> { tstp_error("unterminated comment"); }

"ac" { return TK_AC; }
"answers" { return TK_ANSWERS; }
"axiom_of_choice" { return TK_AXIOM_OF_CHOICE ; }
"axiom" { return TK_AXIOM ; }
"cnf" { return TK_CNF ; }
"conjecture" { return TK_CONJECTURE ; }
"creator" { return TK_CREATOR ; }
"definition" { return TK_DEFINITION ; }
"description" { return TK_DESCRIPTION ; }
"equality:s" { return TK_EQUALITY_S ; }
"equality" { return TK_EQUALITY ; }
"fof" { return TK_FOF ; }
"file" { return TK_FILE ; }
"hypothesis" { return TK_HYPOTHESIS ; }
"include" { return TK_INCLUDE ; }
"inference" { return TK_INFERENCE ; }
"introduced" { return TK_INTRODUCED ; }
"iquote" { return TK_IQUOTE ; }
"lemma_conjecture" { return TK_LEMMA_CONJECTURE ; }
"lemma" { return TK_LEMMA ; }
"negated_conjecture" { return TK_NEGATED_CONJECTURE ; }
"plain" { return TK_PLAIN ; }
"refutation" { return TK_REFUTATION ; }
"status" { return TK_STATUS ; }
"symmetry" { return TK_SYMMETRY ; }
"tautology" { return TK_TAUTOLOGY ; }
"theorem" { return TK_THEOREM ; }
"theory" { return TK_THEORY ; }
"unknown" { return TK_UNKNOWN ; }

"&" { return TK_AND ; }
"!=" { return TK_DIFF ; }
"$neq" { return TK_NEQ ; }
"=" { return TK_EQU ; }
"$equal" { return TK_EQUAL ; }
"<=>" { return TK_EQV ; }
"$false" { return TK_FALSE ; }
"=>" { return TK_LIMPL ; }
"<~>" { return TK_NEQV ; }
"~&" { return TK_NAND ; }
"~|" { return TK_NOR ; }
"~" { return TK_NOT ; }
"|" { return TK_OR ; }
"<=" { return TK_RIMPL ; }
"$true" { return TK_TRUE ; }
"!" { return TK_BANG ; }
"?" { return TK_QUESTION_MARK ; }
"+" { return TK_PLUS ; }
"-" { return TK_MINUS ; }

":" { return TK_COLON ; }
"," { return TK_COMMA ; }
"." { return TK_DOT ; }
"(" { return TK_LP ; }
")" { return TK_RP ; }
"[" { return TK_LSQ ; }
"]" { return TK_RSQ ; }

{upper_word} { 
  tstp_lval.string = strmake(yytext); 
  return UPPER_WORD ; 
}
{epred_symbol} {
  int count, arity;
  sscanf(yytext, "epred%i_%i", &arity, &count);
  tstp_lval.symb = tptp_logic_epred(arity, count);
  return SYMB;
}
{skolem_symbol} {
  int count, arity;
  sscanf(yytext, "esk%i_%i", &count, &arity);
  tstp_lval.symb = tptp_logic_skolem(arity, count);
  return SYMB;
}
{lower_word} { 
  tstp_lval.string = strmake(yytext); 
  return LOWER_WORD ; 
}
{symbol_pointer} { 
  sscanf(yytext, "'s%x'", (Tsymb *) & tstp_lval.symb); 
  return SYMB ; 
}
{term_pointer} { 
  TDAG DAG; 
  sscanf(yytext, "'t%x'", (TDAG *) & DAG); 
  tstp_lval.term = DAG; 
  return TERM ; 
}
{single_quoted} { 
  tstp_lval.string = strmake(yytext); 
  return SINGLE_QUOTED ; 
}
{double_quoted} { 
  return DOUBLE_QUOTED ; 
}
{real} { 
  return REAL ; 
}
{percent_comment} { 
  tstp_lval.string = strmake(yytext); 
  return PERCENT_COMMENT ; 
}

"\n" { ++tstp_lineno; }

\' { tstp_error("unmatched '"); }
\" { tstp_error("unmatched \""); }

[ \t]+		/* eat up space */
.		{ tstp_error("unrecognized character"); }
%%

