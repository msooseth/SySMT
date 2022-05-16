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
  Functions to deal with numbers
  --------------------------------------------------------------
*/

#include <limits.h>
#include <stdbool.h>
#include <stdio.h>

#include "general.h"

#include "numbers.h"

#define GCD_CACHE

/* PF a bound for a variable v should be understood as
   v >= val + delta \delta, where \delta is an infinitesimal value
   If delta is 0, inequality is non-strict */

bool overflow = false;

/*
  --------------------------------------------------------------
  Helpers
  --------------------------------------------------------------
*/

#ifdef GCD_CACHE
#include "gcd-cache.def"
#endif

/**
   \author Pascal Fontaine
   \brief compute the gcd of two values
   \param a first value
   \param b second value
   \return the gcd of the two values */
unsigned long
gcd(unsigned long a, unsigned long b)
{
  unsigned long d;
  unsigned t = 0;

  if (!a)
    return b;
  /* PF find the common power of two */
  for (t = 0; ((a | b) & 1) == 0; ++t)
    {
      a >>= 1;
      b >>= 1;
    }
  /* PF then eliminate all factors of two */
  while ((a & 1) == 0)
    a >>= 1;
#ifdef GCD_CACHE
 /* DD could test also with: ((a | b) & ~((unsigned long) 0xFF) == 0) */
  while (a >= GCD_CACHE_SZ || b >= GCD_CACHE_SZ) 
    {
      /* PF invariant: a is not divisible by 2 */
      while ((b & 1) == 0)
	b >>= 1;
      if (a < b)
	b -= a;
      else
	{
	  d = a - b;
	  a = b;
	  b = d;
	}
      b >>= 1u;
    }
  return ((unsigned long)GCD_CACHE_ARRAY[a][b] << t);
#else
  /* PF then compute using standard Euclid */
  do
    {
      /* PF invariant: a is not divisible by 2 */
      while ((b & 1) == 0)
	b >>= 1;
      if (a < b)
	b -= a;
      else
	{
	  d = a - b;
	  a = b;
	  b = d;
	}
      b >>= 1u;
    }
  while (b != 0);
  return a << t;
#endif
}

/*
  --------------------------------------------------------------
  Signed
  --------------------------------------------------------------
*/

void
LAsigned_neg(TLAsigned * a)
{
  a->sval = -a->sval;
}

/*--------------------------------------------------------------*/

void
LAsigned_add(TLAsigned * a, TLAsigned * b)
{
  signed long long tmp;
  tmp = a->sval + b->sval;
  overflow |= (tmp > INT_MAX) || (tmp <= INT_MIN);
  if (overflow)
    my_error("overflow\n");
  a->sval = (signed int)tmp;
}

/*--------------------------------------------------------------*/

void
LAsigned_mult(TLAsigned * a, TLAsigned * b)
{
  signed long long tmp1;
  tmp1 = a->sval * b->sval;
  overflow |= (tmp1 > INT_MAX) || (tmp1 <= INT_MIN);
  if (overflow)
    my_error("overflow\n");
  a->sval = (long int) tmp1;
}

/*--------------------------------------------------------------*/

void
LAsigned_com(TLAsigned * a, TLAsigned * b, TLAsigned * c, TLAsigned * d)
{
  signed long long tmp1, tmp2;
  tmp1 = a->sval * c->sval;
  overflow |= (tmp1 > INT_MAX) || (tmp1 <= INT_MIN);
  tmp2 = b->sval * d->sval;
  overflow |= (tmp2 > INT_MAX) || (tmp2 <= INT_MIN);
  tmp1 -= tmp2;
  overflow |= (tmp1 > INT_MAX) || (tmp1 <= INT_MIN);
  if (overflow)
    my_error("overflow\n");
  a->sval = (long int) tmp1;
}

/*--------------------------------------------------------------*/

void
LAsigned_set_zero(TLAsigned * Psigned)
{
  Psigned->sval = 0;
}

/*--------------------------------------------------------------*/

bool
LAsigned_is_zero(TLAsigned * Psigned)
{
  return Psigned->sval == 0;
}

/*--------------------------------------------------------------*/

void
LAsigned_set_one(TLAsigned * Psigned)
{
  Psigned->sval = 1;
}

/*--------------------------------------------------------------*/

bool
LAsigned_sign_diff(TLAsigned * a, TLAsigned * b)
{
  return (bool)(((unsigned long)(a->sval ^ b->sval)) >>
		(sizeof(signed long) * CHAR_BIT - 1));
}

/*
  --------------------------------------------------------------
  Rationals
  --------------------------------------------------------------
*/

void
LArational_set_one(TLArational * Prational)
{
  Prational->sval.num = 1;
  Prational->sval.den = 1;
}

/*--------------------------------------------------------------*/

void
LArational_str(TLArational * Prational, char * str)
{
  unsigned i;
  signed long long num = 0;
  unsigned long long den = 1;
  if (str[0] == 0)
    {
      Prational->sval.num = 0;
      Prational->sval.den = 1;
      return;
    }
  if (str[0] == '#')
    {
      /* binary #b[01]+ */
      if (str[1] == 'b')
	{
	  for (i = 2; str[i]; i++)
	    {
	      num <<= 1;
	      if (str[i] != '0' && str[i] != '1')
		{
		  my_error("strange number\n");
		  return;
		}
	      num += str[i] == '1';
	      overflow |= num > INT_MAX;
	      if (overflow)
		my_error("overflow\n");
	    }
	  Prational->sval.num = (signed int) num;
	  Prational->sval.den = (unsigned int) den;
	  return;
	}
      /* binary #x[0-9A-Fa-f]+ */
      if (str[1] == 'x')
	{
	  for (i = 2; str[i]; i++)
	    {
	      num <<= 4;
	      if ((str[i] < '0' || str[i] > '9') &&
		  (str[i] < 'A' || str[i] > 'F'))
		{
		  my_error("strange number\n");
		  return;
		}
	      if (str[i] >= '0' && str[i] <= '9')
		num += str[i] - '0';
	      else
		num += str[i] - 'A' + 10;
	      overflow |= num > INT_MAX;
	      if (overflow)
		my_error("overflow\n");
	    }
	  Prational->sval.num = (signed int) num;
	  Prational->sval.den = (unsigned int) den;
	  return;
	}
      my_error("strange number\n");
      return;
    }
  /* Numeral [\-]?(0|[1-9][0-9]*)
     Rational [\-]?[1-9][0-9]* / [0-9]+[1-9]
     Decimal [\-]?(0|[1-9][0-9]*)\.[0-9]+ */
  i = 0;
  if (str[i] == '-')
    i++;
  while (str[i] >= '0' && str[i] <= '9')
    {
      num *= 10;
      num += str[i] - '0';
      overflow |= num > INT_MAX;
      if (overflow)
	my_error("overflow\n");
    }
  if (str[i] == '.')
    {
      i++;
      while (str[i] >= '0' && str[i] <= '9')
	{
	  num *= 10;
	  den *= 10;
	  num += str[i] - '0';
	  overflow |= num > INT_MAX;
	  overflow |= den > INT_MAX;
	  if (overflow)
	    my_error("overflow\n");
	}
    }
  else if (str[i] == '/')
    {
      i++;
      den = 0;
      while (str[i] >= '0' && str[i] <= '9')
	{
	  den *= 10;
	  den += (unsigned)(str[i] - '0');
	  overflow |= den > INT_MAX;
	  if (overflow)
	    my_error("overflow\n");
	}
    }
  if (str[i])
    {
      my_error("strange number\n");
      return;
    }
  if (str[0] == '-')
    num *= -1;
  Prational->sval.num = (signed int) num;
  Prational->sval.den = (unsigned int) den;
}

/*--------------------------------------------------------------*/

void
LArational_normalize(TLArational * Prational)
{
  int mask = Prational->sval.num >> (sizeof(int) * CHAR_BIT - 1);
  /* PF all this should not overflow, num is never INT_MIN */
  unsigned int c = (unsigned int)
    gcd((unsigned long)((Prational->sval.num + mask) ^ mask),
	Prational->sval.den);
  Prational->sval.num /= (signed int) c;
  Prational->sval.den /= c;
}

/*--------------------------------------------------------------*/

void
LArational_neg(TLArational * Prational)
{
  /* PF all this should not overflow */
  Prational->sval.num *= -1;
}

/*--------------------------------------------------------------*/

void
LArational_add(TLArational * Prational1, TLArational * Prational2)
{
  unsigned int g = (unsigned int)
    gcd(Prational1->sval.den, Prational2->sval.den);
  signed long long a, b;
  unsigned long long c;
  a = Prational2->sval.den / g;
  a *= Prational1->sval.num;
  overflow |= (a > INT_MAX || a <= INT_MIN);
  b = Prational1->sval.den / g;
  b *= Prational2->sval.num;
  overflow |= (b > INT_MAX || b <= INT_MIN);
  a += b;
  overflow |= (a > INT_MAX || a <= INT_MIN);
  Prational1->sval.num = (signed int) a;
  c = Prational1->sval.den;
  c /= g;
  c *= Prational2->sval.den;
  overflow |= (c > UINT_MAX);
  Prational1->sval.den = (unsigned int) c;
  if (overflow)
    my_error("overflow\n");
  LArational_normalize(Prational1);
}

/*--------------------------------------------------------------*/

void
LArational_mult(TLArational * Prational1, TLArational * Prational2)
{
  signed long long a;
  unsigned long long b;
  /* PF all this should not overflow
     Several functions use the same construction.
     Make sure all are patched if this one is found buggy
     PF2DD please review */
  a = Prational1->sval.num * Prational2->sval.num;
  b = Prational1->sval.den * Prational2->sval.den;
  overflow |= (a > INT_MAX) || (a <= INT_MIN) || (b > UINT_MAX);
  if (overflow)
    my_error("overflow\n");
  Prational1->sval.num = (int) a;
  Prational1->sval.den = (unsigned) b;
  /* IMPROVE: overflow should be only after normalization */
  LArational_normalize(Prational1);
}

/*--------------------------------------------------------------*/

void
LArational_div(TLArational * Prational1, TLArational * Prational2)
{
  signed int mask;
  signed long long a;
  unsigned long long b;
  mask = Prational2->sval.num >> (sizeof(signed int) * CHAR_BIT - 1);
  a = ((Prational1->sval.num + mask) ^ mask) * (int) Prational2->sval.den;
  b = Prational1->sval.den * (unsigned)((Prational2->sval.num + mask) ^ mask);
  overflow |= (a > INT_MAX) || (a <= INT_MIN) || (b > UINT_MAX);
  if (overflow)
    my_error("overflow\n");
  Prational1->sval.num = (int) a;
  Prational1->sval.den = (unsigned) b;
  /* IMPROVE: overflow should be only after normalization */
  LArational_normalize(Prational1);
}

/*--------------------------------------------------------------*/

bool
LArational_eq(TLArational * Prational1, TLArational * Prational2)
{
  signed long long a, b;
  /* PF all this should not overflow */
  a = Prational1->sval.num;
  b = Prational2->sval.num;
  a *= Prational2->sval.den;
  b *= Prational1->sval.den;
  return (a == b);
}

/*--------------------------------------------------------------*/

bool
LArational_leq(TLArational * Prational1, TLArational * Prational2)
{
  signed long long a, b;
  /* PF all this should not overflow
     Several functions use the same construction.
     Make sure all are patched if this one is found buggy
     PF2DD please review */
  a = Prational1->sval.num;
  b = Prational2->sval.num;
  a *= (signed long long) Prational2->sval.den;
  b *= (signed long long) Prational1->sval.den;
  return (a <= b);
}

/*--------------------------------------------------------------*/

bool
LArational_less(TLArational * Prational1, TLArational * Prational2)
{
  signed long long a, b;
  /* PF all this should not overflow */
  a = Prational1->sval.num;
  b = Prational2->sval.num;
  a *= (signed long long) Prational2->sval.den;
  b *= (signed long long) Prational1->sval.den;
  return (a < b);
}

/*--------------------------------------------------------------*/

void
LArational_ppcm(TLAsigned * Pppcm, TLArational * Prational)
{
  unsigned long long a;
  a = (unsigned long) Pppcm->sval;
  a /= gcd((unsigned long) a, Prational->sval.den);
  a *= Prational->sval.den;
  overflow |= (a > INT_MAX);
  if (overflow)
    my_error("overflow\n");
  Pppcm->sval = (signed long) a;
}

/*--------------------------------------------------------------*/

void
LArational_mult_to_signed(TLAsigned * Psigned, TLArational * Prational)
{
  signed long long a;
  a = Psigned->sval;
  a /= (signed long) Prational->sval.den;
  a *= Prational->sval.num;
  overflow |= (a > INT_MAX || a <= UINT_MAX);
  if (overflow)
    my_error("overflow\n");
  Psigned->sval = (signed long) a;
}

/*
  --------------------------------------------------------------
  Delta numbers
  --------------------------------------------------------------
*/

void
LAdelta_set_zero(TLAdelta * delta)
{
  delta->val.sval.num = 0;
  delta->val.sval.den = 1;
  delta->delta.sval.num = 0;
  delta->delta.sval.den = 1;
}

/*--------------------------------------------------------------*/

void
LAdelta_set_one(TLAdelta * delta)
{
  delta->val.sval.num = 1;
  delta->val.sval.den = 1;
  delta->delta.sval.num = 0;
  delta->delta.sval.den = 1;
}

/*--------------------------------------------------------------*/

bool
LAdelta_is_zero(TLAdelta * delta)
{
  return delta->val.sval.num == 0 && delta->delta.sval.num == 0;
}

/*--------------------------------------------------------------*/

void
LAdelta_int(TLAdelta * delta, int val)
{
  delta->val.sval.num = val;
  delta->val.sval.den = 1;
  delta->delta.sval.num = 0;
  delta->delta.sval.den = 1;
}

/*--------------------------------------------------------------*/

void
LAdelta_rat(TLAdelta * delta, int num, unsigned den)
{
  delta->val.sval.num = num;
  delta->val.sval.den = den;
  delta->delta.sval.num = 0;
  delta->delta.sval.den = 1;
}

/*--------------------------------------------------------------*/

void
LAdelta_rat_delta(TLAdelta * delta, int num, unsigned den, int eps)
{
  delta->val.sval.num = num;
  delta->val.sval.den = den;
  delta->delta.sval.num = eps;
  delta->delta.sval.den = 1;
}

/*--------------------------------------------------------------*/

bool
LAdelta_eq(TLAdelta * delta1, TLAdelta * delta2)
{
  return LArational_eq(&delta1->val, &delta2->val) ||
    LArational_eq(&delta1->delta, &delta2->delta);
}

/*--------------------------------------------------------------*/

bool
LAdelta_leq(TLAdelta * delta1, TLAdelta * delta2)
{
  signed long long a, b;
  /* PF all this should not overflow */
  a = delta1->val.sval.num;
  b = delta2->val.sval.num;
  a *= delta2->val.sval.den;
  b *= delta1->val.sval.den;
  return a < b || ((a == b) && LArational_leq(&delta1->delta, &delta2->delta));
}

/*--------------------------------------------------------------*/

bool
LAdelta_less(TLAdelta * delta1, TLAdelta * delta2)
{
  signed long long a, b;
  /* PF all this should not overflow */
  a = delta1->val.sval.num;
  b = delta2->val.sval.num;
  a *= delta2->val.sval.den;
  b *= delta1->val.sval.den;
  return a < b || ((a == b) && LArational_less(&delta1->delta, &delta2->delta));
}

/*--------------------------------------------------------------*/

#if 0
void
LAdelta_mult(TLAdelta * delta0, TLAdelta * delta1)
{
  signed long long num2;
  unsigned long long den2;
  num2 = delta0->val.sval.num * (signed int) delta1->val.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.num = (signed int) num2;
  num2 = delta1->val.sval.num * (signed int) delta0->val.sval.den; 
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 *= a->sval;



  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 += delta0->val.sval.num;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.num = (signed int) num2;  
  den2 = delta0->val.sval.den * delta1->val.sval.den;
  overflow |= (den2 > INT_MAX);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.den = (unsigned int) den2;
}
#endif

/*--------------------------------------------------------------*/

void
LAdelta_addmult(TLAdelta * delta0, TLAdelta * delta1, TLAsigned * a)
{
  signed long long num2;
  unsigned long long den2;
  num2 = delta0->val.sval.num * (signed int) delta1->val.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.num = (signed int) num2;
  num2 = delta1->val.sval.num * (signed int) delta0->val.sval.den; 
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 *= a->sval;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 += delta0->val.sval.num;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.num = (signed int) num2;  
  den2 = delta0->val.sval.den * delta1->val.sval.den;
  overflow |= (den2 > INT_MAX);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.den = (unsigned int) den2;
}

/*--------------------------------------------------------------*/

void
LAdelta_minus(TLAdelta * delta0, TLAdelta * delta1, TLAdelta * delta2)
{
  signed long long num2;
  unsigned long long den2;
  den2 = delta1->val.sval.den * delta2->val.sval.den;
  overflow |= (den2 > INT_MAX);
  delta0->val.sval.den = (unsigned int) den2;
  num2 = delta1->val.sval.num * (signed int) delta2->val.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  delta0->val.sval.num = (signed int) num2;
  num2 = delta2->val.sval.num * (signed int) delta1->val.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 = delta0->val.sval.num - num2;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->val.sval.num = (signed int) num2;
  den2 = delta1->delta.sval.den * delta2->delta.sval.den;
  overflow |= (den2 > INT_MAX);
  delta0->delta.sval.den = (unsigned int) den2;
  num2 = delta1->delta.sval.num * (signed int) delta2->delta.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->delta.sval.num = (signed int) num2;
  num2 = delta2->delta.sval.num * (signed int) delta1->delta.sval.den;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  num2 = delta0->delta.sval.num - num2;
  overflow |= (num2 > INT_MAX) || (num2 <= INT_MIN);
  if (overflow)
    my_error("LA overflow\n");
  delta0->delta.sval.num = (signed int) num2;
}

/*--------------------------------------------------------------*/

void
LAdelta_div_opp(TLAdelta * delta0, TLAsigned * a)
{
  signed long mask = a->sval >> (sizeof(signed long) * CHAR_BIT - 1);
  /* PF all this should not overflow, num is never INT_MIN */
  unsigned long long den2;
  den2 = delta0->val.sval.den * (unsigned int) ((a->sval + mask) ^ mask);
  overflow |= (den2 > INT_MAX);
  delta0->val.sval.den = (unsigned int) den2;
  delta0->val.sval.num =  (a->sval < 0)?delta0->val.sval.num:-delta0->val.sval.num;
  if (overflow)
    my_error("overflow\n");
}

/*--------------------------------------------------------------*/

void
LAdelta_print(TLAdelta * delta)
{
  
  printf("%d", delta->val.sval.num);
  if (delta->val.sval.den != 1)
    printf("/%d", delta->val.sval.den);
  if (delta->delta.sval.num)
    {
      printf("+ %d", delta->delta.sval.num);
      if (delta->delta.sval.den != 1)
	printf("/%d", delta->delta.sval.den);
      printf(" d");
    }
}
