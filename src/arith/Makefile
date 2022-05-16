include ../../Makefile.config
SRCFILES    = $(wildcard *.c)
OBJFILES    = ${SRCFILES:.c=.o}

MODULES    += oldarith bool congruence eprover number symbolic parsers/smtlib2 parsers/dimacs pre proof utils SAT .
LIBDIR     += ${BASEDIR}/extern/gmp/include

BASEDIR = $(subst $(empty) $(empty),*,${PWD}/../..)

CPATH = $(subst *,$(empty) $(empty),.:$(subst $(empty) $(empty),:,$(foreach MOD, ${MODULES},${BASEDIR}/src/${MOD}))):$(subst *,$(empty) $(empty),.:$(subst $(empty) $(empty),:,${LIBDIR}))

export CPATH

all: CFLAGS += -O3 -DNDEBUG -finline-limit=1000000 -fomit-frame-pointer
debug: CFLAGS += -ansi -Wall -O0 -Dinline=""
pedantic: CFLAGS += -DPEDANTIC -Wall -O0 -pedantic -Wextra\
	-Wdeclaration-after-statement -ansi -Wmissing-prototypes \
	-Wconversion -Wno-long-long -Dinline=""

all debug pedantic: ${OBJFILES}

%.o:%.c
	${CC} ${CFLAGS} -c $^

clean veryclean:
	rm -f *~ *.o *.da *.bb *.bbg dependencies
