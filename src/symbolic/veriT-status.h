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
  \file veriT-status.h
  \author David Deharbe and Pascal Fontaine

  \brief Proof status in libveriT.

  This file only contains the definition of the type of the proof
  status in the solver. This is in a separate file as the same status
  is also used in different internal proof engines.
*/

#ifndef __VERIT_STATUS_H
#define __VERIT_STATUS_H

/** \brief Enumeration of the different possible proof status in veriT. */
enum Estatus {
  /** \brief satisfiable */
  SAT, 

  /** \brief unsatisfiable */
  UNSAT,

  /** \brief undefined 

      The proof obligation is not within the theories for which the
      solver is complete, and the solver was not able to show
      unsatisfiability. */

  /** \todo PF: should we call these UNKNOWN ?? */
  UNDEF,

  /** \brief not verified yet

      Run veriT_solve to (semi)decide */
  OPEN

};

/** \brief Type of proof status in libveriT. */
typedef enum Estatus Tstatus;

#endif /* __VERIT_STATUS_H */
