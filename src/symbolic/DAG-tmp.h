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

#ifndef DAG_TMP_H
#define DAG_TMP_H

/*
  --------------------------------------------------------------
  DAG_tmp functions
  --------------------------------------------------------------
*/

extern char * DAG_tmp;

#define DAG_tmp_bool ((unsigned char *) DAG_tmp)
#define DAG_tmp_unsigned ((unsigned *) DAG_tmp)
#define DAG_tmp_int ((int *) DAG_tmp)
#define DAG_tmp_DAG ((TDAG *) DAG_tmp)
#define DAG_tmp_stack_DAG ((Tstack_DAG *) DAG_tmp)

#ifdef DEBUG
extern void DAG_tmp_reserve(void);
extern void DAG_tmp_release(void);
#else
#define DAG_tmp_reserve()
#define DAG_tmp_release()
#endif

extern void DAG_tmp_reset_bool(TDAG DAG);
extern void DAG_tmp_reset_unsigned(TDAG DAG);
extern void DAG_tmp_reset_int(TDAG DAG);
extern void DAG_tmp_reset_DAG(TDAG DAG);

extern void DAG_tmp_free_DAG(TDAG DAG);

/*
  --------------------------------------------------------------
  DAG_symb_tmp functions
  --------------------------------------------------------------
*/

extern char * DAG_symb_tmp;

#define DAG_symb_tmp_DAG ((TDAG *) DAG_symb_tmp)

#define DAG_symb_tmp_bool ((unsigned char *) DAG_symb_tmp)
#define DAG_symb_tmp_unsigned ((unsigned *) DAG_symb_tmp)
#define DAG_symb_tmp_int ((int *) DAG_symb_tmp)
#define DAG_symb_tmp_DAG ((TDAG *) DAG_symb_tmp)

#ifdef DEBUG
extern void DAG_symb_tmp_reserve(void);
extern void DAG_symb_tmp_release(void);
#else
#define DAG_symb_tmp_reserve()
#define DAG_symb_tmp_release()
#endif

/*
  --------------------------------------------------------------
  Initialization-release functions
  --------------------------------------------------------------
*/

extern void DAG_tmp_init(void);
extern void DAG_tmp_done(void);

#endif
