# cf. trick from GNU make manual sec 8.1 2006/04
empty      :=

PROGRAM     = veriT-SAT

CC          = gcc

SRCFILES    = $(wildcard *.c)
OBJFILES    = $(patsubst %.c,%.o,${SRCFILES})

MODULES     = ../src/SAT
SUBDIRS     = ${MODULES}
SRCMODULES  = $(foreach MOD,${MODULES},$(wildcard ${MOD}/*.c))
OBJMODULES  = $(patsubst %.c,%.o,${SRCMODULES})

# substitute space characters in path name to build CPATH
BASEDIR     = $(shell pwd)
BASEDIRSAFE = $(subst $(empty) $(empty),*,${BASEDIR})

CPATH = $(subst *,$(empty) $(empty),.:$(subst $(empty) $(empty),:,$(foreach MOD, ${MODULES},${BASEDIRSAFE}/${MOD})))

export CFLAGS
export CPATH

all: CFLAGS += -Wall -O3 -DNDEBUG -fomit-frame-pointer -finline-limit=1000000 #-ansi 

debug: CFLAGS += -ansi -Wall ${DEBUG_OPT} -O0 -g -g3 -gdwarf-2

pedantic: CFLAGS += -ansi -Wall -O0 -pedantic -Wextra \
  -Wdeclaration-after-statement -Wmissing-prototypes -Wpadded 
#  -Wsign-conversion -Wconversion is untracktable with bit fields and so

prof: CFLAGS += -Wall -O3 -DNDEBUG -DSTATS_LEVEL=0 -finline-limit=1000000 -pg -g

all debug pedantic: ${OBJFILES}
	for I in ${SUBDIRS}; do ${MAKE} -C $$I $@ || exit 1; done
	${CC} ${CFLAGS} ${OBJFILES} ${OBJMODULES} ${LDFLAGS} -o ${PROGRAM}

prof: ${OBJFILES}
	for I in ${SUBDIRS}; do ${MAKE} -C $$I all || exit 1; done
	${CC} ${CFLAGS} ${OBJFILES} ${OBJMODULES} ${LDFLAGS} -o ${PROGRAM}

%.o:%.c
	echo ${CPATH}
	${CC} ${CFLAGS} -c $^

clean veryclean:
	for I in ${SUBDIRS}; do ${MAKE} -C $$I $@ || exit 1; done
	rm -f *~ ${PROGRAM} ${OBJFILES} *.da *.bb *.bbg dependencies

doc:
	mkdir -p doc
	doxygen Doxyfile.dev
