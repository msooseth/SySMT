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

#ifndef __NUMBERS_H
#define __NUMBERS_H

#ifndef HAS_GMP
#define mpz_t char
#define mpq_t char
#endif

/**
   \author Pascal Fontaine
   \brief records if any overflow has taken place */
extern bool overflow;

/**
   \author Pascal Fontaine
   \typedef TLAsigned
   \brief signed number
   \remark C native signed long, but arbitrary size are available if needed
   \remark max signed long is 2^31-1 on 32 bits, 2^63-1 on 64 bits
   \remark min signed long is -2^31+1 on 32 bits, -2^63+1 on 64 bits
   \remark in principle, min unsigned long could be one less, but for
   simplicity in overflow detection, we will loose the LONG_MIN value
   \remark we use long to detect overflow and compute gcd afterwards
   However, in this module, we will never let a stable value be larger
   than 32 bits */
typedef union TLAsigned
{
  signed long sval;
  mpz_t lval;
} TLAsigned;

/**
   \author Pascal Fontaine
   \typedef TLArational
   \brief rational number
   \remark pair of C native int, but arbitrary size are available if needed
   \remark INT_MIN is counted as overflow in num */
typedef union TLArational
{
  struct {
    signed int num;
    unsigned int den;
  } sval;
  mpq_t lval;
} TLArational;

/**
   \author Pascal Fontaine
   \typedef TLAdelta
   \brief number with delta */
typedef struct TLAdelta
{
  TLArational val;
  TLArational delta;
} TLAdelta;

/*
  --------------------------------------------------------------
  Utils
  --------------------------------------------------------------
*/

unsigned long gcd(unsigned long a, unsigned long b);

/*
  --------------------------------------------------------------
  Signed
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief execture the following operation a = -a
   \param a pointer to a LAsigned */
void LAsigned_neg(TLAsigned * a);

/**
   \author Pascal Fontaine
   \brief check if a and b have different sign
   \param a pointer to a signed
   \param b pointer to a signed
   \return 1 if signs differ, 0 otherwise */
void LAsigned_add(TLAsigned * a, TLAsigned * b);

/**
   \author Pascal Fontaine
   \brief execture the following operation a = a * c
   \param a pointer to a LAsigned
   \param b pointer to a LAsigned
   \return 1 if numbers become large and it is time to think about normalization
 */
void LAsigned_mult(TLAsigned * a, TLAsigned * b);

/**
   \author Pascal Fontaine
   \brief execute the following operation a = a * c - b * d
   \param a pointer to a LAsigned
   \param b pointer to a LAsigned
   \param c pointer to a LAsigned
   \param d pointer to a LAsigned
   \return 1 if numbers become large and it is time to think about normalization */
void LAsigned_com(TLAsigned * a, TLAsigned * b, TLAsigned * c, TLAsigned * d);

/**
   \author Pascal Fontaine
   \brief set a signed value to 0
   \param Psigned pointer to a signed */
void LAsigned_set_zero(TLAsigned * Psigned);

/**
   \author Pascal Fontaine
   \brief check if a signed value is 0
   \param Psigned pointer to a signed
   \return 1 if *Psigned is zero */
bool LAsigned_is_zero(TLAsigned * Psigned);

/**
   \author Pascal Fontaine
   \brief set a signed value to 1
   \param Psigned pointer to a signed */
void LAsigned_set_one(TLAsigned * Psigned);

/**
   \author Pascal Fontaine
   \brief check if a and b have different sign
   \param a pointer to a signed
   \param b pointer to a signed
   \return 1 if signs differ, 0 otherwise */
bool LAsigned_sign_diff(TLAsigned * a, TLAsigned * b);

/*
  --------------------------------------------------------------
  Rationals
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief set a rational value to 1
   \param Prational a pointer to a rational value */
void LArational_set_one(TLArational * Prational);

/**
   \author Pascal Fontaine
   \brief sets rational to be the number represented by str
   \param Prational a pointer to a rational value
   \param str a string */
void LArational_str(TLArational * Prational, char * str);

/**
   \author Pascal Fontaine
   \brief normalize the value, i.e. divides num and den by their gcd
   \param Prational a pointer to a rational value */
void LArational_normalize(TLArational * Prational);

/**
   \author Pascal Fontaine
   \brief changes sign of rational
   \param Prational1 a pointer to a rational value */
void LArational_neg(TLArational * Prational);

/**
   \author Pascal Fontaine
   \brief add two rationals and puts result in first argument
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \remark normalizes */
void LArational_add(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief multiplies two rationals and puts result in first argument
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \remark normalizes */
void LArational_mult(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief divides two rationals and puts result in first argument
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \remark normalizes */
void LArational_div(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief compare two rationals
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \return 1 iff a is equal to b, 0 otherwise */
bool LArational_eq(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief compare two rationals
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \return 1 iff a is smaller than or equal to b, 0 otherwise */
bool LArational_leq(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief compare two rationals
   \param Prational1 a pointer to a first rational value
   \param Prational2 a pointer to a second rational value
   \return 1 iff a is strictly smaller than b, 0 otherwise */
bool LArational_less(TLArational * Prational1, TLArational * Prational2);

/**
   \author Pascal Fontaine
   \brief gets the ppcm of the denominator of *Prational and *Pppcm
   \param Pppcm a pointer to a signed value
   \param Prational a pointer to a rational value
   \remark stores the result in *Pppcm */
void LArational_ppcm(TLAsigned * Pppcm, TLArational * Prational);

/**
   \author Pascal Fontaine
   \brief multiplies signed by rational
   \param Psigned a pointer to a signed value
   \param Prational a pointer to a rational value
   \remark stores the result in *Psigned
   \remak the result should be integer */
void LArational_mult_to_signed(TLAsigned * asigned, TLArational * Prational);

/*
  --------------------------------------------------------------
  Delta numbers
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief set delta value to 0
   \param delta value */
void LAdelta_set_zero(TLAdelta * delta);

/**
   \author Pascal Fontaine
   \brief set delta value to 1
   \param delta value */
void LAdelta_set_one(TLAdelta * delta);

/**
   \author Pascal Fontaine
   \brief check if delta is 0
   \param delta value
   \return 1 iff 0 otherwise 0 */
bool LAdelta_is_zero(TLAdelta * delta);

/**
   \author Pascal Fontaine
   \brief set value of delta according to int
   \param delta
   \param val its value */
void LAdelta_int(TLAdelta * delta, int val);

/**
   \author Pascal Fontaine
   \brief set value of delta according to arguments
   \param delta
   \param valnum numerator for its value 
   \param valden denominator for its value */
void LAdelta_rat(TLAdelta * delta, int num, unsigned den);

/**
   \author Pascal Fontaine
   \brief set value of delta according to arguments
   \param delta
   \param valnum numerator for its value
   \param valden denominator for its value
   \param eps coefficient of delta value */
void LAdelta_rat_delta(TLAdelta * delta, int num, unsigned den, int eps);

/**
   \author Pascal Fontaine
   \brief check if two delta value are equal
   \param delta1 value
   \param delta2 value
   \return 1 if delta1 == delta2 */
bool LAdelta_eq(TLAdelta * delta1, TLAdelta * delta2);

/**
   \author Pascal Fontaine
   \brief check if a delta value is less than or equal to another
   \param delta1 value
   \param delta2 value
   \return 1 if delta1 <= delta2 */
bool LAdelta_leq(TLAdelta * delta1, TLAdelta * delta2);

/**
   \author Pascal Fontaine
   \brief check if a delta value is less than another
   \param delta1 value
   \param delta2 value
   \return 1 if delta1 < delta2 */
bool LAdelta_less(TLAdelta * delta1, TLAdelta * delta2);

/**
   \author Pascal Fontaine
   \brief check if two delta value are not equal
   \param delta1 value
   \param delta2 value
   \return 1 if delta1 < delta2 */
bool LAdelta_neq(TLAdelta * delta1, TLAdelta * delta2);

#if 0
/**
   \author Pascal Fontaine
   \brief compute delta0 = delta0 + delta1 * a
   \param delta0 value
   \param delta1 value
   \param a value */
void LAdelta_mult(TLAdelta * delta0, TLAdelta * delta1);
#endif

/**
   \author Pascal Fontaine
   \brief compute delta0 = delta0 + delta1 * a
   \param delta0 value
   \param delta1 value
   \param a value */
void LAdelta_addmult(TLAdelta * delta0, TLAdelta * delta1, TLAsigned * a);

/**
   \author Pascal Fontaine
   \brief compute delta0 = delta1 - delta2
   \param delta0 value
   \param delta1 value
   \param delta2 value */
void LAdelta_minus(TLAdelta * delta0, TLAdelta * delta1, TLAdelta * delta2);

/**
   \author Pascal Fontaine
   \brief compute delta0 = - delta0 / a
   \param delta0 value
   \param delta1 value
   \param a value */
void LAdelta_div_opp(TLAdelta * delta0, TLAsigned * a);

/**
   \author Pascal Fontaine
   \brief print value of delta
   \param delta */
void LAdelta_print(TLAdelta * delta);

#endif
