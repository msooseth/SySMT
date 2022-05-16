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

/* DC number representation module */

#include "general.h"
#include "number.h"
#include "DAG-print.h"

/* DD+DC some useful constants */
Tnumber number_zero;
Tnumber number_one;
Tnumber number_not_zero;
Tnumber number_small_neg_int;
Tnumber number_small_neg_real;
/* DC it makes no sense using 'infinity' for !NUMBER_GMP_RATIONAL_INFINITY */
Tnumber number_infinity;
Tnumber number_minus_infinity;
char buffer[1000];

#ifdef NUMBER_GMP_RATIONAL
#warning "number representation is with GMP"
static mpq_t mpq_zero;
static mpq_t mpq_one;

Tnumber
number_new()
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  mpq_init(n->num);
  mpq_init(n->delta);
  return n;
}

Tnumber
number_dup(Tnumber src)
{
  Tnumber res;
  MY_MALLOC(res, sizeof(struct TSnumber));
  mpq_init(res->num);
  mpq_init(res->delta);
  mpq_set(res->num, src->num);
  mpq_set(res->delta, src->delta);
  return res;
}

static Tnumber
number_set2(Tnumber dest, const int num, const int delta)
{
  mpq_set_si(dest->num, num, 1);
  mpq_set_si(dest->delta, delta, 1);
  return dest;
}

Tnumber
number_cpy(Tnumber dest, const Tnumber src)
{
  mpq_set(dest->num, src->num);
  mpq_set(dest->delta, src->delta);
  return dest;
}

void 
number_free(Tnumber n)
{
  mpq_clear(n->num);
  mpq_clear(n->delta);
  free(n);
}

Tnumber
number_add(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  mpq_add(res->num, n1->num, n2->num);
  mpq_add(res->delta, n1->delta, n2->delta);
  
  return res;
}

Tnumber
number_sub(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  mpq_sub(res->num, n1->num, n2->num);
  mpq_sub(res->delta, n1->delta, n2->delta);
  
  return res;
}

Tnumber
number_mul(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  mpq_t t1, t2, t3;
  mpq_init(t1);
  mpq_init(t2);
  mpq_init(t3);
  mpq_mul(t1, n1->num, n2->num);
  if (mpq_cmp(n1->delta, mpq_zero) != 0 && mpq_cmp(n2->delta, mpq_zero) != 0)
    my_error ("Cannot perform multiplication between two non-exact numbers.\n");
  mpq_mul(t2, n1->num, n2->delta);
  mpq_mul(t3, n1->delta, n2->num);
  mpq_add(res->delta, t2, t3);
  mpq_set(res->num, t1);
  mpq_clear(t1);
  mpq_clear(t2);
  mpq_clear(t3);
  
  return res;
}

Tnumber
number_div(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  mpq_div(res->num, n1->num, n2->num);
  if (mpq_cmp(n2->delta, mpq_zero) != 0)
    my_error ("Cannot perform division by a non-exact number.\n");
  mpq_div(res->delta, n1->delta, n2->num);
  
  return res;
}

Tnumber
number_neg(Tnumber n)
{
  mpq_neg(n->num, n->num);
  mpq_neg(n->delta, n->delta);
  
  return n;
}

/* DC Pre-condition: the double is a "int like", i.e., "x.00" */
Tnumber
number_from_double(Tnumber dest, const double d)
{
  if (d >= 0.0)
    mpq_set_si(dest->num, (int)(d+0.1), 1);
  else
    mpq_set_si(dest->num, (int)(d-0.1), 1);
  mpq_set_si(dest->delta, 0, 1);
  
  return dest;
}

Tnumber
number_from_DAG (Tnumber dest, const TDAG DAG)
{
  mpq_set_str(dest->num, DAG_symb_name(DAG_symb(DAG)), 0);
  mpq_canonicalize(dest->num);
  mpq_set_si(dest->delta, 0, 1);
  
  return dest;
}

TDAG
number_to_DAG (const Tnumber number)
{
  mpz_t den;
  mpz_t num;
  char * str;
  TDAG DAG;
  
  if (mpq_cmp_si(number->delta, 0, 1) != 0)
    my_error("Error when creating a DAG representation for the number.\n");
  
  mpz_init (den);
  mpz_init (num);
  mpq_get_den (den, number->num);
  mpq_get_num (num, number->num);
  if (mpz_cmp_si(den, 1) != 0)
    {
      str = mpq_get_str (NULL, 10, number->num);
      DAG = DAG_new_rational_str (str);
    }
  else
    {
      str = mpz_get_str (NULL, 10, num);
      DAG = DAG_new_numeral_str(str);
    }
  mpz_clear (den);
  mpz_clear (num);
  free (str);
  return DAG;
}

int
number_less(const Tnumber n1, const Tnumber n2)
{
  int cmp = mpq_cmp(n1->num, n2->num);
  if (cmp < 0)
    return 1;
  else
    return cmp == 0 && mpq_cmp(n1->delta, n2->delta) < 0;
}

int
number_greater(const Tnumber n1, const Tnumber n2)
{
  int cmp = mpq_cmp(n1->num, n2->num);
  if (cmp > 0)
    return 1;
  else
    return cmp == 0 && mpq_cmp(n1->delta, n2->delta) > 0;
}

#endif


#ifdef NUMBER_GMP_RATIONAL_INFINITY
#warning "number representation is with GMP + infinity"
static mpq_t mpq_zero;
static mpq_t mpq_one;

Tnumber
number_new()
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  mpq_init(n->num);
  mpq_init(n->delta);
  n->inf = 0;
  return n;
}

Tnumber
number_dup(Tnumber src)
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  mpq_init(n->num);
  mpq_init(n->delta);
  mpq_set(n->num, src->num);
  mpq_set(n->delta, src->delta);
  n->inf = src->inf;
  return n;
}

static Tnumber
number_set2(Tnumber dest, const int num, const int delta)
{
  mpq_set_si(dest->num, num, 1);
  mpq_set_si(dest->delta, delta, 1);
  dest->inf = 0;
  
  return dest;
}

Tnumber
number_cpy(Tnumber dest, const Tnumber src)
{
  mpq_set(dest->num, src->num);
  mpq_set(dest->delta, src->delta);
  dest->inf = src->inf;
  return dest;
}

void 
number_free(Tnumber n)
{
  mpq_clear(n->num);
  mpq_clear(n->delta);
  free(n);
}

#define neg_inf(n) (-n)

Tnumber
number_add(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (n1->inf == 0 && n2->inf == 0)
    {
      mpq_add(res->num, n1->num, n2->num);
      mpq_add(res->delta, n1->delta, n2->delta);
      res->inf = 0;
    }
  else if (n1->inf == 0)
    res->inf = n2->inf;
  else if (n2->inf == 0)
    res->inf = n1->inf;    
  else if (n1->inf == n2->inf)
    res->inf = n1->inf;
  else
    my_error ("Cannot perform addition between two -INFINITY and +INFINITY.\n");
  
  return res;
}

Tnumber
number_sub(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (n1->inf == 0 && n2->inf == 0)
    {
      mpq_sub(res->num, n1->num, n2->num);
      mpq_sub(res->delta, n1->delta, n2->delta);
      res->inf = 0;
    }
  else if (n1->inf == 0)
    res->inf = neg_inf(n2->inf);
  else if (n2->inf == 0)
    res->inf = n1->inf;
  else if (n1->inf == neg_inf(n2->inf))
    res->inf = n1->inf;
  else
    my_error ("Cannot perform subtraction between two INFINITY numbers of same sign.\n");
  
  return res;
}

Tnumber
number_mul(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (n1->inf == 0 && n2->inf == 0)
    {
      mpq_t t1, t2, t3;
      mpq_init(t1);
      mpq_init(t2);
      mpq_init(t3);
      mpq_mul(t1, n1->num, n2->num);
      if (mpq_cmp(n1->delta, mpq_zero) != 0 && mpq_cmp(n2->delta, mpq_zero) != 0)
        my_error ("Cannot perform multiplication between two non-exact numbers.\n");
      mpq_mul(t2, n1->num, n2->delta);
      mpq_mul(t3, n1->delta, n2->num);
      mpq_add(res->delta, t2, t3);
      mpq_set(res->num, t1);
      
      res->inf = 0;
      mpq_clear(t1);
      mpq_clear(t2);
      mpq_clear(t3);
    }
  else
    {
      int r1 = mpq_cmp(n1->num, mpq_zero);
      int r2 = mpq_cmp(n2->num, mpq_zero);
      if (r1 == 0)
	r1 = mpq_cmp(n1->delta, mpq_zero);
      if (r2 == 0)
	r2 = mpq_cmp(n2->delta, mpq_zero);
      if (n1->inf == 0)
        {
	  if (r1 == 0)
	  {
	    printf("error: %s and %s\n", number_to_str(n1), number_to_str(n2));
            my_error ("Cannot perform multiplication between an INFINITY number and zero.\n");
	  }
	  else if (r1 > 0)
            res->inf = n2->inf;
          else
            res->inf = neg_inf(n2->inf);
	}
      else if (n2->inf == 0)
	{
	  if (r2 == 0)
	    my_error ("Cannot perform multiplication between an INFINITY number and zero.\n");
          else if (r2 > 0)
            res->inf = n1->inf;
          else
            res->inf = neg_inf(n1->inf);
        }
      else
        res->inf = n1->inf * n2->inf;
    }
  
  return res;
}

Tnumber
number_div(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (n2->inf == 0)
    {
      if (mpq_cmp(n2->delta, mpq_zero) != 0)
	my_error ("Cannot perform division by a non-exact number.\n");
      else if (mpq_cmp(n2->num, mpq_zero) == 0)
        my_error ("Division by zero.\n");
      else if (n1->inf == 0)
	{
          mpq_div(res->num, n1->num, n2->num);
          mpq_div(res->delta, n1->delta, n2->num);
          res->inf = 0;
        }
      else
	{
	  if (mpq_cmp(n2->num, mpq_zero) > 0)
	    res->inf = n1->inf;
	  else
	    res->inf = neg_inf(n1->inf);
        }
    }
  else if (n1->inf == 0)
    {
      mpq_set_si(res->num, 0, 1);
      mpq_set_si(res->delta, 0, 1);
      res->inf = 0;
    }
  else if (n1->inf != 0 && n2->inf != 0)
    my_error ("Cannot perform division between two INFINITY numbers.\n");
  
  return res;
}

Tnumber
number_mod(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (mpq_cmp(n1->delta, mpq_zero) != 0 || mpq_cmp(n2->delta, mpq_zero) != 0)
    my_error ("The numbers should be integer in the module operation.\n");
  else if (mpq_cmp(n2->num, mpq_zero) == 0)
    my_error ("Division by zero.\n");
  else if (n1->inf != 0 || n2->inf != 0)
    my_error ("The numbers should be finite in the module operation.\n");
  else if (mpz_cmp(mpq_denref(n1->num), mpq_numref(mpq_one)) != 0 
	   || mpz_cmp(mpq_denref(n2->num), mpq_numref(mpq_one)) != 0)
    my_error ("The numbers should be integer in the module operation.\n");
  else
    {
      mpq_set_si(res->delta, 0, 1);
      mpz_mod(mpq_numref(res->num), mpq_numref(n1->num), mpq_numref(n2->num));
      mpz_set_si(mpq_denref(res->num), 1);
      res->inf = 0;
    }
  
  return res;
}

Tnumber
number_neg(Tnumber n)
{
  if (n->inf == 0)
    {
      mpq_neg(n->num, n->num);
      mpq_neg(n->delta, n->delta);
    }
  else
    n->inf = neg_inf(n->inf);
  
  return n;
}

/* DC Pre-condition: the double is a "int like", i.e., "x.00" */
Tnumber
number_from_double(Tnumber dest, const double d)
{
  if (d >= 0.0)
    mpq_set_si(dest->num, (int)(d+0.1), 1);
  else
    mpq_set_si(dest->num, (int)(d-0.1), 1);
  mpq_set_si(dest->delta, 0, 1);
  dest->inf = 0;
  
  return dest;
}

Tnumber
number_from_DAG (Tnumber dest, const TDAG DAG)
{
  /* DC Fraction format */
  if (mpq_set_str(dest->num, DAG_symb_name(DAG_symb(DAG)), 0) == 0)
    {
      mpq_canonicalize(dest->num);
      mpq_set_si(dest->delta, 0, 1);
    }
  /* DC Float point format */
  else
    {
      mpf_t tmp;
      mpf_init(tmp);
      if (mpf_set_str(tmp, DAG_symb_name(DAG_symb(DAG)), 10) == -1)
	my_DAG_error("Unexpected number format: %D", DAG);
      else
	{
	  mpq_set_f(dest->num, tmp);
	  mpq_canonicalize(dest->num);
	  mpq_set_si(dest->delta, 0, 1);
	}
      mpf_clear(tmp);
    }

  return dest;
}

TDAG
number_to_DAG (const Tnumber number)
{
  mpz_t den;
  mpz_t num;
  char * str;
  TDAG DAG;
  
  if (mpq_cmp_si(number->delta, 0, 1) != 0)
    my_error("Error when creating a DAG representation for the number.\n");
  else if (number->inf != 0)
    my_error("Cannot represent an INFINITY number as a DAG.\n");
  
  mpz_init (den);
  mpz_init (num);
  mpq_get_den (den, number->num);
  mpq_get_num (num, number->num);
  if (mpz_cmp_si(den, 1) != 0)
    {
      str = mpq_get_str (NULL, 10, number->num);
      DAG = DAG_new_rational_str (str);
    }
  else
    {
      str = mpz_get_str (NULL, 10, num);
      DAG = DAG_new_numeral_str(str);
    }
  mpz_clear (den);
  mpz_clear (num);
  free (str);
  return DAG;
}

int
number_less(const Tnumber n1, const Tnumber n2)
{
  if (n1->inf == 0 && n2->inf == 0)
    {
      int cmp = mpq_cmp(n1->num, n2->num);
      if (cmp < 0)
        return 1;
      else
        return cmp == 0 && mpq_cmp(n1->delta, n2->delta) < 0;
    }
  else 
    return n1->inf < n2->inf;
}

int
number_greater(const Tnumber n1, const Tnumber n2)
{
  if (n1->inf == 0 && n2->inf == 0)
    {
      int cmp = mpq_cmp(n1->num, n2->num);
      if (cmp > 0)
        return 1;
      else
        return cmp == 0 && mpq_cmp(n1->delta, n2->delta) > 0;
    }
  else
    return n1->inf > n2->inf;
}

Tnumber
number_floor(Tnumber n)
{
  int r;
  if ((r = mpq_cmp(n->delta, mpq_zero)) != 0 && mpz_cmp(mpq_denref(n->num), mpq_numref(mpq_one)) == 0)
    {
      if (r < 0)
        mpz_sub_ui(mpq_numref(n->num), mpq_numref(n->num), 1);
      mpz_set_si(mpq_numref(n->delta), 0);
    }
  else    
    {
      mpz_fdiv_q(mpq_numref(n->num), mpq_numref(n->num), mpq_denref(n->num));
      mpz_set_si(mpq_denref(n->num), 1);
    }
  return n;
}

Tnumber
number_ceil(Tnumber n)
{
  int r;
  if ((r = mpq_cmp(n->delta, mpq_zero)) != 0 && mpz_cmp(mpq_denref(n->num), mpq_numref(mpq_one)) == 0)
    {
      if (r > 0)
        mpz_add_ui(mpq_numref(n->num), mpq_numref(n->num), 1);
      mpz_set_si(mpq_numref(n->delta), 0);
    }
  else
    {
      mpz_cdiv_q(mpq_numref(n->num), mpq_numref(n->num), mpq_denref(n->num));
      mpz_set_si(mpq_denref(n->num), 1);
    }
  return n;
}

Tnumber
number_denominator(Tnumber res, const Tnumber n)
{
  if (mpq_cmp(n->delta, mpq_zero) != 0)
    my_error ("The number should be integer.\n");
  mpq_set_si(res->delta, 0, 1);
  mpz_set(mpq_numref(res->num), mpq_denref(n->num));
  mpz_set_si(mpq_denref(res->num), 1);
  res->inf = 0;
  return res;
}

int
number_is_int(Tnumber n)
{
  return mpq_cmp(n->delta, mpq_zero) == 0 && mpz_cmp(mpq_denref(n->num), mpq_numref(mpq_one)) == 0;
}

int
number_is_rational(const Tnumber n)
{
  return mpq_cmp(n->delta, mpq_zero) == 0;
}

Tnumber
number_gcd(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (mpq_cmp(n1->delta, mpq_zero) != 0 || mpq_cmp(n2->delta, mpq_zero) != 0)
    my_error ("The numbers should be integer when calculation the GCD.\n");
  else if (n1->inf != 0 || n2->inf != 0)
    my_error ("The numbers should be finite when calculation the GCD.\n");
  else if (mpz_cmp(mpq_denref(n1->num), mpq_numref(mpq_one)) != 0 
	   || mpz_cmp(mpq_denref(n2->num), mpq_numref(mpq_one)) != 0)
    my_error ("The numbers should be integer when calculation the GCD.\n");
  else
    {
      mpq_set_si(res->delta, 0, 1);
      mpz_gcd(mpq_numref(res->num), mpq_numref(n1->num), mpq_numref(n2->num));
      mpz_set_si(mpq_denref(res->num), 1);
      res->inf = 0;
    }
  
  return res;
}

Tnumber
number_lcm(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  if (mpq_cmp(n1->delta, mpq_zero) != 0 || mpq_cmp(n2->delta, mpq_zero) != 0)
    my_error ("The numbers should be integer when calculation the GCD.\n");
  else if (n1->inf != 0 || n2->inf != 0)
    my_error ("The numbers should be finite when calculation the GCD.\n");
  else if (mpz_cmp(mpq_denref(n1->num), mpq_numref(mpq_one)) != 0 
	   || mpz_cmp(mpq_denref(n2->num), mpq_numref(mpq_one)) != 0)
    my_error ("The numbers should be integer when calculation the GCD.\n");
  else
    {
      mpq_set_si(res->delta, 0, 1);
      mpz_lcm(mpq_numref(res->num), mpq_numref(n1->num), mpq_numref(n2->num));
      mpz_set_si(mpq_denref(res->num), 1);
      res->inf = 0;
    }
  
  return res;
}

#endif


#ifdef NUMBER_NATIVE_RATIONAL
#warning "number representation is with rationals defined with native int"

#include <errno.h>
#include <limits.h>
#define OUT_OF_RANGE(n) ((n) > INT_MAX || (n) < INT_MIN)

Tnumber
number_new()
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  return n;
}

Tnumber
number_dup(Tnumber src)
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  n->num = src->num;
  n->delta = src->delta;
  return n;
}

static Tnumber
number_set2(Tnumber dest, const int num, const int delta)
{
  dest->num.numerator = num;
  dest->num.denominator = 1;
  dest->delta = delta;
  return dest;
}

Tnumber
number_cpy(Tnumber dest, const Tnumber src)
{
  dest->num = src->num;
  dest->delta = src->delta;
  
  return dest;
}

void
number_free(Tnumber n)
{
  free(n);
}

#define abs(a) (a > 0 ? a : -a)

static long long
gcd_n(long long a, long long b)
{
  while (b != 0)
    {
      long long t = a;
      a = b;
      b = t%b;
    }
  return a > 0 ? a : 1;
}

static long long
gcd(long long a, long long b)
{
  a = abs(a);
  b = abs(b);
  if (a < b)
    return gcd_n(b, a);
  else
    return gcd_n(a, b);
}

Tnumber
number_add(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long n, d, g;

  n = (long long)n1->num.denominator * (long long)n2->num.numerator + (long long)n2->num.denominator * (long long)n1->num.numerator;
  d = (long long)n1->num.denominator * (long long)n2->num.denominator;
  g = gcd(n, d);
  n /= g;
  d /= g;
  
  if (OUT_OF_RANGE(n))
    my_error("Arithmetic overflow.\n");
  res->num.numerator = (int)n;
  
  if (OUT_OF_RANGE(d))
    my_error("Arithmetic overflow.\n");
  res->num.denominator = (int)d;
  
  n = n1->delta + n2->delta;
  if (OUT_OF_RANGE(n))
    my_error("Arithmetic overflow.\n");
  res->delta = (int)n;

  return res;
}

Tnumber
number_sub(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long n, d, g;

  n = (long long)n2->num.denominator * (long long)n1->num.numerator - (long long)n1->num.denominator * (long long)n2->num.numerator;
  d = (long long)n1->num.denominator * (long long)n2->num.denominator;
  g = gcd(n, d);
  n /= g;
  d /= g;
  
  if (((n) > INT_MAX || (n) < INT_MIN))
    my_error("Arithmetic overflow.\n");
  res->num.numerator = (int) n;
  
  if (OUT_OF_RANGE(d))
    my_error("Arithmetic overflow.\n");
  res->num.denominator = (int) d;
  
  n = n1->delta - n2->delta;
  if (OUT_OF_RANGE(n))
    my_error("Arithmetic overflow.\n");
  res->delta = (int)n;
  
  return res;
}

Tnumber
number_mul(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long n, d, g;

  if (n1->delta != 0 || n2->delta != 0)
    my_error ("Cannot perform multiplication between two non-exact numbers.\n");

  n = (long long) n1->num.numerator * (long long) n2->num.numerator;
  d = (long long) n1->num.denominator * (long long) n2->num.denominator;
  g = gcd(n, d);
  n /= g;
  d /= g;
  
  if (OUT_OF_RANGE(n))
    my_error("Arithmetic overflow.\n");
  res->num.numerator = (int)n;
  
  if (OUT_OF_RANGE(d))
    my_error("Arithmetic overflow.\n");
  res->num.denominator = (int)d;
  res->delta = 0;

  return res;
}

Tnumber
number_div(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long n, d, g;

  if (n2->delta != 0)
    my_error ("Division by a non-exact number.\n");

  /* n1 = n1.num.numerator/n1.num.denominator + D*n1.delta
     n2 = n2.num.numerator/n2.num.denominator
     n1/n2 = n1.num.numerator*n2.num.denominator/n1.num.denominator*n2.num.numerator +
     D* n1.delta*n2.num.denominator/n2.num.numerator */

  n = (long long)n1->num.numerator * (long long)n2->num.denominator;
  d = (long long)n2->num.numerator * (long long)n1->num.denominator;
  g = gcd(n, d);
  n /= g;
  d /= g;
  
  if (OUT_OF_RANGE(n))
    my_error("Arithmetic overflow.\n");
  res->num.numerator = (int)n;
  
  if (OUT_OF_RANGE(d))
    my_error("Arithmetic overflow.\n");
  if (d == 0)
    my_error("Division by zero.\n");
  res->num.denominator = (int)d;
  
  n = (long long) n1->delta * (long long) n2->num.denominator;
  d = n2->num.denominator;
  g = gcd (n, d);
  n /= g;
  d /= g;
  if (d == 0)
    my_error("Division by zero.\n");
  if (n % d !=0)
    my_error ("Loss of precision due to native representation of non-exact number.\n");
  res->delta = n/d;

  return res;
}

Tnumber
number_neg(Tnumber n)
{
  if (n->num.numerator == INT_MIN)
    my_error("Arithmetic overflow.\n");
  if (n->delta == INT_MIN)
    my_error("Arithmetic overflow.\n");
  n->num.numerator *= -1;
  n->delta *= -1;
  
  return n;
}

/* DC Pre-condition: the double is a "int like", i.e., "x.00" */
Tnumber
number_from_double(Tnumber dest, const double d)
{
  if (d >= 0.0)
    dest->num.numerator = (int)(d+0.1);
  else
    dest->num.numerator = (int)(d-0.1);
  dest->num.denominator = 1;
  dest->delta = 0;
  
  return dest;
}

/* DC+DD Pre-condition: the DAG is an integer */
/* DC A number can be a integer or a fraction */
Tnumber
number_from_DAG (Tnumber dest, const TDAG DAG)
{
  long value;
  char *endptr;

#warning "reimplement number_from_DAG (NUMBER_NATIVE_RATIONAL)"  
  if (!DAG_is_number (DAG))
    my_error ("Trying to interpret non-numerical DAG to number \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));

  errno = 0;
  value = strtol (DAG_symb_name(DAG_symb(DAG)), &endptr, 0);
  if (errno == ERANGE)
    my_error ("Overflow when reading value \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));
  if (OUT_OF_RANGE(value))
    my_error ("Arithmetic overflow.\n");
  if (endptr[0] != NULL)
    {
      if (endptr[0] != '/')
	my_error ("Number format invalid \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));
      
      dest->num.numerator = (int) value;
      errno = 0;
      value = strtol (&endptr[1], NULL, 0);
      if (errno == ERANGE)
	my_error ("Overflow when reading value \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));
      if (OUT_OF_RANGE(value))
	my_error ("Arithmetic overflow.\n");
      if (value == 0)
	my_error ("Division by zero.\n");
      dest->num.denominator = (int)value;
    }
  else
    {
      dest->num.numerator = (int) value;
      dest->num.denominator = 1;
    }
  dest->delta = 0;
  
  return dest;
}

TDAG
number_to_DAG (const Tnumber number)
{
  if (number->delta != 0)
    my_error("Error when creating a DAG representation for the number.\n");
  return DAG_new_rational (number->num.numerator, number->num.denominator);
}

int
number_less(const Tnumber n1, const Tnumber n2)
{
  long long a = (long long)n1->num.numerator * (long long)n2->num.denominator;
  long long b = (long long)n2->num.numerator * (long long)n1->num.denominator;
  if (a < b)
    return 1;
  else
    return a == b && n1->delta < n2->delta;
}

int
number_greater(const Tnumber n1, const Tnumber n2)
{
  long long a = (long long)n1->num.numerator * (long long)n2->num.denominator;
  long long b = (long long)n2->num.numerator * (long long)n1->num.denominator;
  if (a > b)
    return 1;
  else
    return a == b && n1->delta > n2->delta;
}

#endif
#ifdef NUMBER_NATIVE_INTEGER
#warning "number representation is with native int"

#include <errno.h>
#include <limits.h>
#define OUT_OF_RANGE(n) ((n) > INT_MAX || (n) < INT_MIN)

Tnumber
number_new()
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  return n;
}

Tnumber
number_dup(Tnumber src)
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  n->num = src->num;
  n->delta = src->delta;
  return n;
}

static Tnumber
number_set2(Tnumber dest, const int num, const int delta)
{
  dest->num = num;
  dest->delta = delta;
  return dest;
}

Tnumber
number_cpy(Tnumber dest, const Tnumber src)
{
  dest->num = src->num;
  dest->delta = src->delta;
  
  return dest;
}

void
number_free(Tnumber n)
{
  free(n);
}

Tnumber
number_add(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long tmp;

  tmp = (long long)n1->num + (long long)n2->num;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow.\n");
  res->num = (int)tmp;
  
  tmp = n1->delta + n2->delta;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow.\n");
  res->delta = (int)tmp;

  return res;
}

Tnumber
number_sub(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long tmp;

  tmp = (long long)n1->num - (long long)n2->num;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow.\n");
  res->num = (int)tmp;
  
  tmp = n1->delta - n2->delta;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow.\n");
  res->delta = (int)tmp;
  
  return res;
}

Tnumber
number_mul(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long num;
  long long delta;

  if (n1->delta != 0 && n2->delta != 0)
    my_error ("Cannot perform multiplication between two non-exact numbers.\n");

  num = (long long)n1->num * (long long)n2->num;

  if (OUT_OF_RANGE(num))
    my_error("Arithmetic overflow.\n");
  
  if (n1->delta == 0)
    delta = n1->num * n2->delta;
  else
    delta = n2->num * n1->delta;
  if (OUT_OF_RANGE(delta))
    my_error("Arithmetic overflow.\n");

  res->num = (int) num;
  res->delta = (int) delta;

  return res;
}

Tnumber
number_div(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long num;

  if (n2->delta != 0)
    my_error ("Division by a non-exact number.\n");

  if (n2->num == 0)
    my_error("Division by zero.\n");
  
  if (n1->num % n2->num != 0) 
    my_error ("The result of a division is not an integer value. Change the number representation for rational.\n");

  num = (long long) n1->num / (long long) n2->num;
  
  if (n2->delta % n1->num !=0)
    my_error ("Loss of precision due to native representation of non-exact number.\n");

  res->delta = n2->delta / n1->num; /* DD do not swap with next line (res and n1 may point to same struct)! */
  res->num = (int) num;

  return res;
}

Tnumber
number_neg(Tnumber n)
{
  if (n->num == INT_MIN)
    my_error("Arithmetic overflow.\n");
  if (n->delta == INT_MIN)
    my_error("Arithmetic overflow.\n");
  n->num *= -1;
  n->delta *= -1;
  
  return n;
}

/* DC Pre-condition: the double is a "int like", i.e., "x.00" */
Tnumber
number_from_double(Tnumber dest, const double d)
{
  if (d >= 0.0)
    dest->num = (int)(d+0.1);
  else
    dest->num = (int)(d-0.1);
  dest->delta = 0;
  
  return dest;
}

/* DC+DD Pre-condition: the DAG is an integer */
Tnumber
number_from_DAG (Tnumber dest, const TDAG DAG)
{
  long value;
  
  if (!DAG_is_integer (DAG))
    my_error ("Trying to interpret non-numerical DAG to number.\n");
  errno = 0;
  value = strtol (DAG_symb_name(DAG_symb(DAG)), NULL, 0);
  if (errno == ERANGE)
    my_error ("Overflow when reading value \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));
  
  if (OUT_OF_RANGE(value))
    my_error ("Arithmetic overflow.\n");
  dest->num = (int) value;
  dest->delta = 0;
  
  return dest;
}

/* */
TDAG
number_to_DAG (const Tnumber number)
{
  if (number->delta != 0)
    my_error("Error when creating a DAG representation for the number.\n");
  return DAG_new_integer ((long) number->num);
}

#endif

#ifdef NUMBER_INTEGER_THEORY
#warning "number representation is with native int for pure integer theories"

#include <errno.h>
#include <limits.h>
#define OUT_OF_RANGE(n) ((n) > INT_MAX || (n) < INT_MIN)

Tnumber
number_new()
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  return n;
}

Tnumber
number_dup(Tnumber src)
{
  Tnumber n;
  MY_MALLOC(n, sizeof(struct TSnumber));
  n->num = src->num;
  return n;
}

static Tnumber
number_set2(Tnumber dest, const int num, const int delta)
{
  dest->num = num;
  return dest;
}

Tnumber
number_cpy(Tnumber dest, const Tnumber src)
{
  dest->num = src->num;
  return dest;
}

void
number_free(Tnumber n)
{
  free(n);
}

Tnumber
number_add(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long tmp;

  tmp = (long long)n1->num + (long long)n2->num;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow\n");
  res->num = (int)tmp;
  
  return res;
}

Tnumber
number_sub(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long tmp;

  tmp = (long long)n1->num - (long long)n2->num;
  if (OUT_OF_RANGE(tmp))
    my_error("Arithmetic overflow\n");
  res->num = (int)tmp;
  
  return res;
}

Tnumber
number_mul(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long num;

  num = (long long)n1->num * (long long)n2->num;
  if (OUT_OF_RANGE(num))
    my_error("Arithmetic overflow.\n");
  res->num = (int) num;

  return res;
}

Tnumber
number_div(Tnumber res, const Tnumber n1, const Tnumber n2)
{
  long long num;

  if (n2->num == 0)
    my_error("Division by zero.\n");
  
  if (n1->num % n2->num != 0) 
    my_error ("The result of a division is not an integer value. Change the number representation for rational.\n");

  num = (long long) n1->num / (long long) n2->num;
  res->num = (int) num;

  return res;
}

Tnumber
number_neg(Tnumber n)
{
  if (n->num == INT_MIN)
    my_error("Arithmetic overflow\n");
  n->num *= -1;
  
  return n;
}

/* DC Pre-condition: the double is a "int like", i.e., "x.00" */
Tnumber
number_from_double(Tnumber dest, const double d)
{
  if (d >= 0.0)
    dest->num = (int)(d+0.1);
  else
    dest->num = (int)(d-0.1);
  
  return dest;
}

Tnumber
number_from_DAG (Tnumber dest, const TDAG DAG)
{
  long value;
  
  if (!DAG_is_integer (DAG))
    my_error ("Trying to interpret non-numerical DAG to number.\n");
  errno = 0;
  value = strtol (DAG_symb_name(DAG_symb(DAG)), NULL, 0);
  if (errno == ERANGE)
    my_error ("Overflow when reading value \"%s\".\n", DAG_symb_name(DAG_symb(DAG)));
  
  if (OUT_OF_RANGE(value))
    my_error ("Arithmetic overflow.\n");
  dest->num = (int) value;
  
  return dest;
}

/* */
TDAG
number_to_DAG (const Tnumber number)
{
  return DAG_new_integer ((long) number->num);
}

#endif


/* DD the following code is *mostly* common to all implementations */

static int number_initialized = 0;

void
number_init()
{
  if (number_initialized)
    return;

  if (sizeof(int)*2 != sizeof(long long))
    my_error ("Fail in the number module due to the way the machine represents integers.\n");
     
#if defined(NUMBER_GMP_RATIONAL) || defined(NUMBER_GMP_RATIONAL_INFINITY)
  mpq_init (mpq_zero);
  mpq_init (mpq_one);
  mpq_set_si (mpq_one, 1, 1);
#endif

  number_zero = number_new();
  number_one = number_new();
  number_not_zero = number_new();
  number_small_neg_int = number_new();
  number_small_neg_real = number_new();
  number_infinity = number_new();
  number_minus_infinity = number_new();

  number_set2(number_zero, 0, 0);
  number_set2(number_one, 1, 0);
  number_set2(number_not_zero, 1, 0);
  number_set2(number_small_neg_int, -1, 0);
  number_set2(number_small_neg_real, 0, -1);
  number_set2(number_infinity, 0, 0);
  number_set2(number_minus_infinity, 0, 0);

#ifdef NUMBER_GMP_RATIONAL_INFINITY
  number_infinity->inf = 1;
  number_minus_infinity->inf = -1;
#endif
  
  number_initialized = 1;
}

void
number_done()
{
  if (!number_initialized) 
    my_error ("Module number already closed.\n");

  number_free(number_zero);
  number_free(number_one);
  number_free(number_not_zero);
  number_free(number_small_neg_int);
  number_free(number_small_neg_real);
  number_free(number_infinity);
  number_free(number_minus_infinity);

#if defined(NUMBER_GMP_RATIONAL) || defined(NUMBER_GMP_RATIONAL_INFINITY)
  mpq_clear (mpq_zero);
  mpq_clear (mpq_one);
#endif

  number_initialized = 0;
}

Tnumber
number_set(Tnumber dest, const int num)
{
  return number_set2(dest, num, 0);  
}

Tnumber 
number_abs(Tnumber n)
{
  if (number_less(n, number_zero))
    number_neg(n);
  return n;
}

