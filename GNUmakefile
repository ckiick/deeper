
GITPATH=/pkg/local/bin:/usr/bin
# todo: customize for linux vs solaris. eg: -lrt.

REV := $(shell PATH=$(GITPATH) git rev-list HEAD --count)
#REV=41


all:	dict gdexp deeper

deeper:	nondebug
	cp deeper-nd deeper

debug:	deeper-dbg
	cp deeper-dbg deeper

nondebug:	deeper-nd
	cp deeper-nd deeper

clean:
	rm -rf deeper gdexp mkbitset

clobber:	clean
	rm -rf ENABLE.* input

deeper-nd:	deeper.c deeper.h
	gcc -O4 -DREV=$(REV) -o deeper-nd deeper.c -lrt

deeper-dbg:	deeper.c deeper.h
	gcc -g -DREV=$(REV) -DDEBUG -o deeper-dbg deeper.c -lrt

gdexp:	gdexp.c
	gcc -DREV=$(REV) -o gdexp gdexp.c

dict:	ENABLE.gaddag  ENABLE.bitset

ENABLE.TXT:	Lexicon.txt
	dos2unix Lexicon.txt | tr '[a-z]' '[A-Z]' | grep -v '.\{16\}' > ENABLE.TXT
	wc -l ENABLE.TXT

ENABLE.SEP.TXT:	gaddagize ENABLE.TXT
	cp ENABLE.TXT input
	./gaddagize | sort > ENABLE.SEP.TXT
	wc -l ENABLE.SEP.TXT

ENABLE.gaddag:	makegaddag.py ENABLE.SEP.TXT
	./makegaddag.py ENABLE.SEP.TXT ENABLE.gaddag

ENABLE.bitset:	mkbitset ENABLE.gaddag
	./mkbitset

mkbitset:	mkbitset.c
	gcc -o mkbitset mkbitset.c

