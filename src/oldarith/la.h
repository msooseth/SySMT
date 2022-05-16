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
  \file la.h

  \author Diego Caminha

  \brief Interface to the linear arithmetic decision procedure.

  Implementation of a linear arithmetic decision procedure based on a variation of the simplex method.

*/

#ifndef __LA_H_
#define __LA_H_
#include <stdio.h>
#include <stdint.h>

#include "number.h"
#include "veriT-status.h"

/** \brief Kinds of variable allowed by the module. */
typedef enum
{
  /** \brief Integer */
  LA_INT,

  /** \brief Rational */
  LA_RATIONAL
}Tvar_kind;

/**
  \brief Signed int type used to variable identifications.

  \remarks Can be safely cast to and from a pointer type.
*/
typedef intptr_t Tvar_id;

/*-----------------------------------------------------------------------*/
/* DC List of the functions                                              */
/*-----------------------------------------------------------------------*/

/**
   \brief Initializes the module.
   \remarks Must be called before any other function of the module.
*/
void     la_init (void);

/**
  \brief Closes down the module.
  \remarks Frees all the memory allocated by module functions.
*/
void     la_reset (void);

/**
   \brief Restarts the module.
*/
void     la_done (void);

/**
  \brief Adds a equation to the problem.

  Adds a equation to the current set of constraints.
  Each position in the array corresponds to a monomial.
  The right side of the equation is always zero and
  the constant term is identified by var_id zero.

  \param[in] coef[] The coefficients of the monomials.
  \param[in] var_id[] The variables identifications for the monomials.
  \param[in] var_type[] The types of the variables.
  \param[in] size The number of monomials.
  \return The number that identifies this constraint in the module.

  Example:
  \code
  // 1 x + 2 y - 3 z + 7 = 0
  la_push_equation({1, 2, -3, 7}, {1, 2, 3, 0}, 4)
  \endcode
*/
int      la_push_equation (Tnumber coef[], Tvar_id var_id[], Tvar_kind var_type[], Tunsigned size);

/**
  \brief Adds a inequality to the problem.

  Adds an inequality to the current set of constraints.
  Each position in the array corresponds to a monomial.
  The right side of the inequality is always zero and
  the constant term is identified by var_id zero.

  \param[in] coef[] The coefficients of the monomials.
  \param[in] var_id[] The variables identifications for the monomials.
  \param[in] var_type[] The types of the variables.
  \param[in] size The number of monomials.
  \return The number that identifies this constraint in the module.

  Example:
  \code
  // 1 x + 3 z - 4 w - 5 <= 0
  la_push_inequality({1, 3, -4, -5}, {1, 3, 4, 0}, 4)
  \endcode
*/
int      la_push_inequality (Tnumber coef[], Tvar_id var_id[], Tvar_kind var_type[], Tunsigned size);

/**
  \brief Adds a disequality between two variables to the problem.

  Adds a disequality between two variables to the current set of constraints.

  \param[in] var_id1 The identification of the first variable.
  \param[in] var_id2 The identification of the second variable.
  \param[in] var_type1 The type of the first variable.
  \param[in] var_type2 The type of the second variable.
  \return The number that identifies this constraint in the module.

  Example:
  \code
  // x != z
  la_push_disequality(1, 3, LA_INT, LA_INT)
  \endcode
*/
int      la_push_disequality (Tvar_id var_id1, Tvar_id var_id2, Tvar_kind var_type1, Tvar_kind var_type2);

/**
   \brief Removes the last added constraint.
*/
void     la_pop (void);

/**
   \brief Runs the decision procedure to verify the satisfiability of the set of given clues.
   \return The status of satisfiability after the check.
   \remarks In the current implementation, the consistency check is done incrementally during the pushes, so this function returns the current status in constant time.
*/
Tstatus  la_solve (void);

/**
  \brief Looks up for current the satisfiability of the set of given clues.
  \return The current status of satisfiability.
*/
Tstatus  la_status (void);

/**
  \brief Constructs the list containing the identifications of the constraints that led to a contradiction.
  \pre la_check() should return \e false.
  \return The list with the identifications of the conflicting constraints.
  \remarks The constraints identifications numbers are the numbers returned by the functions la_push_equation(), la_push_inequality() and la_push_disequality().
*/
Tlist    la_conflict (void);

/**
  \brief Verifies if the module has an equality to return.
  \return \e true if it has not an equality to return, \e false otherwise.
  \remarks The current implementation does not generate equalities.
*/
bool     la_eq_queue_empty (void);

/**
  \brief Returns a equality deduced by the module.
  \pre la_eq_queue_empty() yields \e false.
  \param[out] var_id1 The Tvar_id of the left side of the equality.
  \param[out] var_id2 The Tvar_id of the right side of the equality.
  \param[out] premisses List of the constraints identifications numbers that produced the equality.
  \remarks The constraints identifications numbers are the numbers returned by the functions la_push_equation(), la_push_inequality() and la_push_disequality().
*/
void     la_eq_queue_pop (Tvar_id * id1, Tvar_id * id2, Tlist *premisses);

/**
  \brief Verifies if the module has an model equality to return.
  \remarks Model equalities can be generated after la_solve() is called.
*/
bool     la_model_eq_queue_empty (void);

/**
  \brief Returns a model equality deduced by the module.
  \pre la_model_eq_queue_empty() yields \e false.
  \param[out] id1 The Tvar_id of the left side of the model equality.
  \param[out] id2 The Tvar_id of the right side of the model equality.
  \remarks Each model equality is returned only once.
*/
void     la_model_eq_queue_pop (Tvar_id * id1, Tvar_id * id2);

/**
  \brief Verifies if there is a conflict between the current model and a disequality.
  \return \e true if there is a conflict between the current model and a disequality, \e false otherwise.
*/
bool     la_model_has_conflict (void);

/**
  \brief Returns one disequality that is conflicting with the current model.
  \pre la_model_has_conflict() yields \e true.
  \return The identification number of the disequality.
*/
int      la_model_conflict_pop (void);

#endif /* __LA_H_*/
