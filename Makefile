

# todo: customize for linux vs solaris. eg: -lrt.

deeper:	deeper.c deeper.h
	gcc -o deeper deeper.c -lrt

debug:	deeper.c deeper.h
	gcc -g -DDEBUG -o deeper deeper.c -lrt

gdexp:	gdexp.c
	gcc -o gdexp gdexp.c

dict:	ENABLE.gaddag  ENABLE.bitset

ENABLE.TXT:	Lexicon.txt
	tr '[a-z]' '[A-Z]' < Lexicon.txt > ENABLE.TXT

ENABLE.SEP.TXT:	gaddagize ENABLE.TXT
	cp ENABLE.TXT input
	./gaddagize | sort > ENABLE.SEP.TXT
	wc -l ENABLE.SEP.TXT

ENABLE.gaddag:	makegaddag.py ENABLE.SEP.TXT
	./makegaddag.py ENABLE.SEP.TXT ENABLE.gaddag

ENABLE.bitset:	mkbitset ENABLE.gaddag
	mkbitset

mkbitset:	mkbitset.c
	gcc -o mkbitset mkbitset.c
