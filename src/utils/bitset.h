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

typedef struct TSbs_mgr * Tbs_mgr;
typedef unsigned char * Tbs;

extern Tbs_mgr  bitset_new_manager(unsigned size, unsigned (*f) (void *));
extern void     bitset_free_manager(Tbs_mgr * mgr);
extern Tbs      bitset_new(Tbs_mgr mgr);
extern void     bitset_free(Tbs_mgr mgr, Tbs set);
extern void     bitset_insert(Tbs_mgr mgr, Tbs set, void * val);
extern void     bitset_remove(Tbs_mgr mgr, Tbs set, void * val);
extern void     bitset_union(Tbs_mgr, Tbs res, Tbs set1, Tbs set2);
extern void     bitset_diff(Tbs_mgr, Tbs res, Tbs set1, Tbs set2);
extern int      bitset_empty(Tbs_mgr, Tbs set);
extern int      bitset_equal(Tbs_mgr, Tbs set1, Tbs set2);
extern int      bitset_subseteq(Tbs_mgr, Tbs set1, Tbs set2);
extern int      bitset_in(Tbs_mgr, Tbs set, void * val);
extern unsigned bitset_card(Tbs_mgr, Tbs set);
#ifdef DEBUG
extern void     bitset_fprint(FILE * file, Tbs_mgr mgr, Tbs set);
#endif