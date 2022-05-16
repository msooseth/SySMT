include ../../../Makefile.config
LEX         = flex
LFLAGS      = -P yy2
YACC        = bison
YFLAGS      = -d -p yy2
SRCFILES    = $(filter-out test.c, $(wildcard *.c)) smtsyn.c smtlex.c
OBJFILES    = smtsyn.c smtlex.c ${SRCFILES:.c=.o}

debug: YFLAGS +=--debug -v
#debug: CFLAGS += -DDEBUG_PARSER
debug: LFLAGS +=#-d

all debug pedantic: ${OBJFILES}

%.o:%.c
	${CC} ${CFLAGS} -c $^

smtfun.o: smtfun.c smtfun.h smttypes.h
	${CC} ${CFLAGS} -c smtfun.c

smtlex.o smtsyn.o: %.o : %.c
	${CC} $(filter-out -ansi -Wall,${CFLAGS}) -c $^

smtsyn.c: smtlib.y smtfun.h smttypes.h
	$(YACC) $(YFLAGS) -k -o smtsyn.c smtlib.y

smtlex.c: smtlib.lex smtsyn.c smtfun.h smttypes.h
	$(LEX) $(LFLAGS) -osmtlex.c smtlib.lex

smtlib.y smtlib.lex smttypes.h smtfun.h: % : %.m4
	m4 -D SMTEXT $@.m4 > $@

clean:
	rm -f *~ *.o smtlex.c smtsyn.c smtsyn.h smtsyn.output \
	  ${OBJFILES} test.o test

veryclean: clean
	rm -f smtlib.y smtlib.lex smttypes.h smtfun.h
