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

/* DC+DD number representation and manipulation */

#ifndef __NUMBER_H_
#define __NUMBER_H_

#include <limits.h>
#include <string.h>

#include "DAG.h"

/* DC
   The number representation is set with a compilation directive.
   There are four different alternatives:
   1. NUMBER_GMP_RATIONAL: The representation is with GNU MP library
   2. NUMBER_NATIVE_RATIONAL: Represented numbers are rationals,
   using native data types.
   3. NUMBER_NATIVE_INTEGER: Represented numbers shall all be integers,
   using native data types. The sort Real from SMT-LIB cannot be handled
   in this alternative. It can handle QF_RDL theory, as long as number in
   the files are all integers.
   4. NUMBER_INTEGER_THEORY: Represented numbers shall all be integers,
   using native data types. The sort Real from SMT-LIB cannot be handled
   in this alternative. It cannot handle QF_RDL theory when strict
   inequalities are in the formula. 
*/

#ifdef NUMBER_GMP_RATIONAL

#include <gmp.h>

typedef struct TSnumber{
  mpq_t num;
  mpq_t delta;
}*Tnumber;

#endif

#ifdef NUMBER_GMP_RATIONAL_INFINITY

#include <gmp.h>

typedef struct TSnumber{
  mpq_t num;
  mpq_t delta;
  char inf; /* DC 0 = normal number; 1 = '+ infinity'; -1 = '- infinity' */
}*Tnumber;

#endif

#ifdef NUMBER_NATIVE_RATIONAL

typedef struct {
  int numerator;
  unsigned denominator;
} Trational;

typedef struct TSnumber{
  Trational num;
  int delta;
} *Tnumber;

#endif

#ifdef NUMBER_NATIVE_INTEGER

typedef struct TSnumber{
  int num;
  int delta;
} *Tnumber;

#endif

#ifdef NUMBER_INTEGER_THEORY
typedef struct TSnumber{
  int num;
} *Tnumber;

#endif

/* DD module initialization: creates useful constants */
void    number_init();
/* DD module is closed, constants are not available anymore */
void    number_done();

/* DD+DC some useful constants */
extern Tnumber number_zero;
extern Tnumber number_one;
extern Tnumber number_not_zero;
extern Tnumber number_small_neg_int;
extern Tnumber number_small_neg_real;
/* DC it makes no sense using 'infinity' for !NUMBER_GMP_RATIONAL_INFINITY */
extern Tnumber number_infinity;
extern Tnumber number_minus_infinity;

/* DD numbers are references to objects - Objects must be created with
   number_new() before any use. Once they are no longer useful, they
   shall be disposed with number_free() */

Tnumber number_new(void);
Tnumber number_dup(Tnumber n);
Tnumber number_set(Tnumber dest, const int num);
Tnumber number_cpy(Tnumber dest, const Tnumber src);
void    number_free(Tnumber n);

/* DD arithmetic operations - note that the first two return their
   result, in addition to storing it in the object referenced by
   the first argument;
   this is not the most efficient, but calls may be composed */
Tnumber number_add(Tnumber res, const Tnumber n1, const Tnumber n2);
Tnumber number_sub(Tnumber res, const Tnumber n1, const Tnumber n2);
Tnumber number_mul(Tnumber res, const Tnumber b1, const Tnumber n2);
Tnumber number_div(Tnumber res, const Tnumber b1, const Tnumber n2);

/* DD number_neg modifies its argument */
Tnumber number_neg(Tnumber n);

/* DC changes n to its absolute value */
Tnumber number_abs(Tnumber n);

/* DD conversion functions */

Tnumber number_from_DAG(Tnumber dest, const TDAG DAG);
TDAG    number_to_DAG(const Tnumber n);

Tnumber number_from_double(Tnumber dest, const double d);

/* DD + DC comparison functions */

#ifdef NUMBER_GMP_RATIONAL
int     number_less(const Tnumber n1, const Tnumber n2);
#define number_equal(n1, n2) (mpq_cmp(n1->num, n2->num) == 0 && mpq_cmp(n1->delta, n2->delta) == 0)
int     number_greater(const Tnumber n1, const Tnumber n2);
#endif

#ifdef NUMBER_GMP_RATIONAL_INFINITY
int     number_less(const Tnumber n1, const Tnumber n2);
#define number_equal(n1, n2) (n1->inf == n2->inf && mpq_cmp(n1->num, n2->num) == 0 && mpq_cmp(n1->delta, n2->delta) == 0)
int     number_greater(const Tnumber n1, const Tnumber n2);
#endif

#ifdef NUMBER_NATIVE_RATIONAL
int number_less(const Tnumber n1, const Tnumber n2);
#define number_equal(n1, n2) (n1->num.numerator == n2->num.numerator && n1->num.denominator == n2->num.denominator && n1->delta == n2->delta)
int number_greater(const Tnumber n1, const Tnumber n2);
#endif

#ifdef NUMBER_NATIVE_INTEGER
#define number_less(n1, n2) (n1->num < n2->num ? 1 : n1->num == n2->num && n1->delta < n2->delta)
#define number_equal(n1, n2) (n1->num == n2->num && n1->delta == n2->delta)
#define number_greater(n1, n2) (n1->num > n2->num ? 1 : n1->num == n2->num && n1->delta > n2->delta)
#endif

#ifdef NUMBER_INTEGER_THEORY
#define number_less(n1, n2) (n1->num < n2->num)
#define number_equal(n1, n2) (n1->num == n2->num)
#define number_greater(n1, n2) (n1->num > n2->num)
#endif

#define number_leq(n1, n2) (!number_greater((n1), (n2)))
#define number_geq(n1, n2) (!number_less((n1), (n2)))

#define number_min(n1, n2) (number_less(n1, n2) ? n1 : n2)
#define number_max(n1, n2) (number_less(n1, n2) ? n2 : n1)


/* DC Other fuctions */
#ifdef NUMBER_GMP_RATIONAL_INFINITY
Tnumber number_floor(Tnumber n);
Tnumber number_ceil(Tnumber n);

/* DC If the number is rational returns the denominator and '1' if integer */
Tnumber number_denominator(Tnumber res, const Tnumber n);

int number_is_int(const Tnumber n);
int number_is_rational(const Tnumber n);

/* DC PRE-condition: n1 and n2 are integer numbers */
Tnumber number_mod(Tnumber res, const Tnumber n1, const Tnumber n2);

Tnumber number_gcd(Tnumber res, const Tnumber n1, const Tnumber n2);
Tnumber number_lcm(Tnumber res, const Tnumber n1, const Tnumber n2);
#endif

/* DC The following conversion functions should be only used for debugging.
   If they are really necessary they should be reimplemented properly (if possible) */

#ifdef NUMBER_GMP_RATIONAL
#define number_to_double(n) (mpq_get_d(n->num) + 1e-12 * mpq_get_d(n->delta))
extern char buffer[1000];
#define number_to_str(n) (mpq_get_str(buffer, 10, n->num))
#endif

#ifdef NUMBER_GMP_RATIONAL_INFINITY
#define number_to_double(n) (n->inf == 0 ? mpq_get_d(n->num) + 1e-12 * mpq_get_d(n->delta) : n->inf*999999999)
extern char buffer[1000];
#define number_to_str(n) (n->inf == 0 ? (mpq_sgn(n->delta) != 0 ? \
  strcat(strcat(strcat(strcat(strcpy(buffer, "("),\
    mpq_get_str(NULL, 10, n->num)),\
      "+"),\
        mpq_get_str(NULL, 10, n->delta)),\
          "δ)")\
 : mpq_get_str(NULL, 10, n->num) ) : n->inf > 0 ? "INF" : "-INF") 
#endif

#ifdef NUMBER_NATIVE_RATIONAL
#define number_to_double(n) (n->num.numerator / n->num.denominator + 1e-12 * n->delta)
#define number_to_str(n) "NOT DEFINED")
#endif

#ifdef NUMBER_NATIVE_INTEGER
#define number_to_double(n) (n->num + 1e-12 * n->delta)
#define number_to_str(n) "NOT DEFINED")
#endif

#ifdef NUMBER_INTEGER_THEORY
#define number_to_double(n) (n->num)
#define number_to_str(n) "NOT DEFINED")
#endif

#endif /* __NUMBER_H_*/
