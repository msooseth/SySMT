include Makefile.config

INSTALL = install

# cf. trick from GNU make manual sec 8.1 2006/04
empty  :=

# substitute space characters in path name to build CPATH
PWD     = $(shell pwd)
OSNAME  = $(shell uname)
BASEDIR = $(subst $(empty) $(empty),*,${PWD})

ifeq ($(NUMBER_REPRESENTATION),NUMBER_GMP_RATIONAL)
  EXTERN += gmp
  LIBDIR += ${BASEDIR}/extern/gmp/lib
  LIBDIR += ${BASEDIR}/extern/gmp/include
  LIB    += gmp
  CFLAGS +=-DNUMBER_GMP_RATIONAL
else ifeq ($(NUMBER_REPRESENTATION),NUMBER_GMP_RATIONAL_INFINITY)
  EXTERN += gmp
  LIBDIR += ${BASEDIR}/extern/gmp/lib
  LIBDIR += ${BASEDIR}/extern/gmp/include
  LIB    += gmp
  CFLAGS +=-DNUMBER_GMP_RATIONAL_INFINITY
else ifeq ($(NUMBER_REPRESENTATION),NUMBER_NATIVE_RATIONAL)
  CFLAGS +=-DNUMBER_NATIVE_RATIONAL
else ifeq ($(NUMBER_REPRESENTATION),NUMBER_NATIVE_INTEGER)
  CFLAGS +=-DNUMBER_NATIVE_INTEGER
else ifeq ($(NUMBER_REPRESENTATION),NUMBER_INTEGER_THEORY)
  CFLAGS +=-DNUMBER_INTEGER_THEORY
endif

ifeq ($(ARITH_DL), YES)
	CFLAGS += -DARITH_DL
endif

ifeq ($(PROOF_PRODUCTION),YES)
  CFLAGS += -DPROOF
endif

#parsers/smtlib2 parsers/dimacs ATP congruence symbolic utils SAT
MODULES    += oldarith bool congruence eprover number symbolic parsers/smtlib2 parsers/dimacs pre proof utils SAT .
LIBDIRFLAGS = $(subst *,\$(empty) $(empty),$(foreach DIR,${LIBDIR},-L${DIR}))
LIBFLAGS    = $(foreach LIB,${LIB},-l${LIB})
LDFLAGS     = ${LIBDIRFLAGS} ${LIBFLAGS}

SUBDIRS     = $(foreach EXT,${EXTERN},extern/${EXT}) \
	      $(foreach MOD,${MODULES},src/${MOD})

CPATH = $(subst *,$(empty) $(empty),.:$(subst $(empty) $(empty),:,$(foreach MOD, ${MODULES},${BASEDIR}/src/${MOD}))):$(subst *,$(empty) $(empty),.:$(subst $(empty) $(empty),:,${LIBDIR}))

export CFLAGS
export CPATH

.DEFAULT_GOAL := all

coverage: CFLAGS += -fprofile-arcs -ftest-coverage
coverage: all

prof : CFLAGS += -pg -g -DNDEBUG
prof : debug

debug_mem : CFLAGS += -DMEM
debug_mem : debug

debug : CFLAGS += -g -g3 -gdwarf-2 -DDEBUG # -Wshorten-64-to-32

all: TOP_RULE = all
debug: TOP_RULE = debug
pedantic: TOP_RULE = pedantic

all: CFLAGS += -O3 -DNDEBUG -finline-limit=1000000 -fomit-frame-pointer
debug: CFLAGS += -ansi -Wall -O0 -Dinline=""
pedantic: CFLAGS += -DPEDANTIC -Wall -O0 -pedantic -Wextra\
	-Wdeclaration-after-statement -ansi -Wmissing-prototypes \
	-Wconversion -Dinline=""

all debug pedantic: ${SUBDIRS} ${PROGRAM}

src/SAT: CFLAGS += -DINSIDE_VERIT

.PHONY: ${SUBDIRS}
${SUBDIRS}:
	${MAKE} -C $@ ${TOP_RULE}

.PHONY: ${PROGRAM}
${PROGRAM}: OBJMODULES = $(foreach MOD,${MODULES},$(wildcard src/${MOD}/*.o))

${PROGRAM}:
	${CC} ${CFLAGS} ${OBJMODULES} ${LDFLAGS} -o ${PROGRAM}

install: all
	${INSTALL} $(PROGRAM) ${PREFIX_BIN}

clean veryclean:
	for I in ${SUBDIRS}; do ${MAKE} -C $$I $@ || exit 1; done
	rm -f *~ $(PROGRAM)

doc:
	mkdir -p doc/user
	doxygen doc/Doxyfile.libveriT.user
	doxygen doc/Doxyfile.veriT.user
	mkdir -p doc/dev
	doxygen doc/Doxyfile.dev

tags:
	for F in `find src -name "*.[ch]" -print`; do etags -a $$F; done

.PHONY: doc tags
