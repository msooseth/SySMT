include ../../Makefile.config

LEX         = flex
YACC        = bison

LFLAGS      = -Ptstp_
YFLAGS      = -d --name-prefix=tstp_

PARSEFILES  = tstplex.c tstpsyn.c
SRCFILES    = $(filter-out $(PARSEFILES), $(wildcard *.c)) tstplex.c tstpsyn.c
OBJFILES    = ${PARSEFILES} ${SRCFILES:.c=.o}

# debug: CFLAGS += -DDEBUG_PARSER
# debug: YFLAGS += --debug --verbose

all debug pedantic: ${OBJFILES}

%.o:%.c
	${CC} ${CFLAGS} -c $^

clean veryclean:
	rm -f *~ *.o tstplex.c tstpsyn.c tstpsyn.h tstpsyn.output \
	  ${OBJFILES}

tstplex.o tstpsyn.o: %.o : %.c
	${CC} $(filter-out -ansi -Wall,${CFLAGS}) -c $^

tstpsyn.c: tstp.y
	$(YACC) $(YFLAGS) -k -o tstpsyn.c tstp.y

tstplex.c: tstp.lex tstpsyn.c
	$(LEX) $(LFLAGS) -otstplex.c tstp.lex
