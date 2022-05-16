include ../../../Makefile.config
SRCFILES    = $(wildcard *.c)
OBJFILES    = ${SRCFILES:.c=.o}

all debug pedantic: ${OBJFILES}

%.o:%.c
	${CC} ${CFLAGS} -c $^

clean veryclean:
	rm -f *~ *.o *.da *.bb *.bbg dependencies
