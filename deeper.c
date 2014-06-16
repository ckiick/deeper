
/*
 * deep scrabble solitaire searcher.
 * principles:
 *	- gaddag for dictionary data, mmapped read-only (align, largepage)
	- fast movegen RE Steven A. Gordon + Appel et al.
	- keep board state instead of recomputing stuff
	- fast C coded bit ops with macros and inline functions
	- use packed structs instead of objects, low mem, fast access, cache
	- multi-threading, per thread cached data, low contention
	- lots and lots of stats
	- high optimization level
	- checkpoint/restart, save/restore state to disk
	- CLI instead of GUI, no display overhead.
	- exhaustive search if possible, heuristics if needed.
*/

#include <stdio.h>
#include <string.h>	// strdup
#include <stdlib.h>	// rand, malloc, and much much more
#include <sys/mman.h>	// mmap
#include <sys/stat.h>	// fstat
#include <fcntl.h>	// open, etc
#include <strings.h>	// str*
#include <unistd.h>	// getopt
#include <ctype.h>	// isupper, etc

#if defined(__sun)
#include <sys/types.h>
#include <sys/time.h>
#else	/* sun */
#include <inttypes.h>
#include <linux/types.h>
#include <time.h>
#include <stdint.h>
#endif	/* sun */


#include "deeper.h"

/* Globals. */

/* dictionary */
gn_t *gaddag = NULL;		// dictionary data (mmapped buffer) RDONLY
bs_t *bitset = NULL;		// bitset data (mmapped) RDONLY
int dfd = -1;			// dictionary file desc
int bsfd = -1;			// bitset filed desc
char *dfn = NULL;		// dictionary file name
unsigned long g_cnt = 0;	// how big is gaddag (in entries)

/* bag */
bag_t globalbag = NULL;		// we only do 1 bag at a time
bagstr_t bagstr = NULL;		// printable/readable bag contents
char bagtag = '_';		// A-Z character naming bag/problem set
char *bagname = NULL;		// name bag as string
int baglen = 100;		// strlen(bagstr)

/* rack */
char *rackstr = NULL;

/* starting stuff */
static const rack_t emptyrack = { {0,0,0,0,0,0,0,0 } };		// all nulls
static const move_t emptymove = { 0, 0, 0, 0, 0, 0, { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}};
board_t emptyboard;		// no tiles played
board_t startboard;		// legal start moves marked
position_t startp;

/* diag, debug and stats */
int verbose = 0;		// level of info output
int dflags = 0;			// for DBG statements
int stats = 0;			// report stats while running
char *gcgfn = NULL;		// save result here
gstats_t globalstats;		// global statistics

/* other options */
int doscore = 0;

/* job/process control */
int globaldone = 0;		// set to stop all threads.


/* fast inline functions. */


void
usage(char *me)
{
	VERB(VNORM, "usage: %s [-DALSMvqs][-d dict][-b bag][-B letters][-o name] moves...", me) {
		printf(
	"\t-L: lookup args in dictionary\n"
	"\t-A: print all anagrams of args\n"
	"\t-S: score arg as if played on empty board\n"
	"\t-M: make the starting move with args, display results\n"
	"\t-D: turn on all debug flags (for now)\n"
	"\t-R letters: use (up to 7) letters as initial rack\n"
	"\t-G: generate list of moves using args\n"
	"\t-d name: use name.gaddag as dictionary. [default=ENABLE]\n"
	"\t-v: increase verbosity level\n"
	"\t-q: no messages, only return values. Cancels -v.\n"
	"\t-b [?]A-Z|name: Set bag name. A-Z are built-in, ?=randomize.\n"
	"\t-B tiles: set bag to string of tiles (A-Z or ? for blank.)\n"
	"\t-o name: save best move to name.gcg\n"
	"\t-s: collect and report statistics. Use twice for more.\n"
	"\t args = rc:word or cr:word, r=1-15, c=A-O, word is 1-7 letters.\n"
	"\t        If rc is omitted, uses starting position of 7H.\n"
	"\t        Put row first for horizontal moves. Do not include tiles\n"
	"\t        Already on board. Use lowercase letter for blank played.\n"
		);
	}
}

/* utility funcs. */

inline bs_t
lstr2bs(letter_t *lstr)
{
	int i;
	bs_t bs = 0;

	while (lstr[i] != '\0') {
		setbit(bs, lstr[i]-1);
		i++;
	}
	return bs;
}

inline int
c2lstr(char *cstr, char *lstr, int played)
{
	int inv = 0;
	int i = 0;

	if (lstr == NULL) return -1;
	if (cstr == NULL) return 0;
	while (cstr[i] != '\0') {
		lstr[i] = c2l(cstr[i]);
		if (!played)
			if (!is_rvalid(lstr[i])) inv++;
		else
			if (!is_bvalid(lstr[i])) inv++;
		i++;
	}
	lstr[i] = '\0';
	return inv;
}


/* force chars to upper case. must be UNPLAYED */
inline int
casec2lstr(char *cstr, char *lstr)
{
	int inv = 0;
	int i = 0;

	if (lstr == NULL) return -1;
	if (cstr == NULL) return 0;
	while (cstr[i] != '\0') {
		lstr[i] = c2l(toupper(cstr[i]));
		if (!is_rvalid(lstr[i])) inv++;
		i++;
	}
	return inv;
}

inline int
l2cstr(char *lstr, char *cstr)
{
	int inv = 0;
	int i = 0;

	if (cstr == NULL) return -1;
	if (lstr == NULL) return 0;
	while (lstr[i] != '\0') {
		cstr[i] = l2c(lstr[i]);
		if (!is_bvalid(lstr[i])) inv++;
		i++;
	}
	cstr[i] = '\0';
	return inv;
}

/* letter to char reverse string */
inline int
l2crstr(char *lstr, char *cstr)
{
	int inv = 0;
	int i = 0, j = 0;

	if (cstr == NULL) return -1;
	if (lstr == NULL) return 0;
	i = strlen(lstr) -1;
	while (i >= 0) {
		cstr[j] = l2c(lstr[i]);
		if (!is_bvalid(lstr[i])) inv++;
		i--; j++;
	}
	return inv;
}

/* reverse the first n chars of a string in place. */
inline void
revnstr(char *str, int n)
{
	char *end = str + n - 1;
	while (str < end)
	{
		*str ^= *end; *end ^= *str; *str ^= *end;
		str++; end--;
	}
}

/* reverse a string in place. */
inline void
revstr(char *str)
{
	char *end = str + strlen(str) - 1;
	while (str < end)
	{
		*str ^= *end; *end ^= *str; *str ^= *end;
		str++; end--;
	}
}

/*
 * linux systems DON'T HAVE gethrtime. So we have to "fake" it with
 * a less efficient equivalent.
 */
#ifndef HRTIME
hrtime_t gethrtime()
{
	struct timespec ts;
	uint64_t ns;
	(void)clock_gettime(CLOCK_MONOTONIC, &ts);
	ns = ts.tv_sec * 1000000000 + ts.tv_nsec;
	return ns;
}
#endif

int
getdict(char *name)
{
	char *fullname;
	int rv;
	struct stat st;
	size_t len;

	ASSERT(strlen(DFNEND) >= strlen(BSNEND));
	if (name == NULL) {
		name = DDFN;
	}
	fullname = malloc(strlen(name) + strlen(DFNEND) + 1);
	if (fullname == NULL) {
		VERB(VNORM, "failed to alloc %d bytes for filename\n", strlen(name) + strlen(DFNEND) + 1) {
			perror("malloc");
		}
		return -5;
	}
	strcpy(fullname, name);
	strcat(fullname, DFNEND);

	dfd = open(fullname, O_RDONLY);
	if (dfd < 0) {
		VERB(VNORM, "gaddag file %s failed to open\n", fullname) {
			perror("open");
		}
		return -1;
	}
	rv = fstat(dfd, &st);
	if (rv < 0) {
		VERB(VNORM, "cannot fstat open file %s\n", fullname) {
			perror("fstat");
		}
		return -2;
	}
	len = st.st_size;
	if (len % sizeof(gn_t)) {
		vprintf(VNORM, "gaddag data not aligned properly\n");
		return -3;
	}
	g_cnt = len / sizeof(gn_t);
	gaddag = (gn_t *)mmap(0, len, PROT_READ, MAP_SHARED, dfd, 0);
	if (gaddag == MAP_FAILED) {
		VERB(VNORM, "failed to mmap %d bytes of gaddag\n", len) {
			perror("mmap");
		}
		return -4;
	}

	strcpy(fullname, name);
	strcat(fullname, BSNEND);

	bsfd = open(fullname, O_RDONLY);
	if (bsfd < 0) {
		VERB(VNORM, "bitset file %s failed to open\n", fullname) {
			perror("open");
		}
		return -1;
	}
	rv = fstat(bsfd, &st);
	if (rv < 0) {
		VERB(VNORM, "cannot fstat open file %s\n", fullname) {
			perror("fstat");
		}
		return -2;
	}
	len = st.st_size;
	if (len % sizeof(bs_t)) {
		vprintf(VNORM, "bitset data not aligned properly\n");
		return -3;
	}
	if ((len/sizeof(bs_t)) != g_cnt) {
		vprintf(VNORM, "bitset data does not match gaddag size\n");
		return -5;
	}
	bitset = (bs_t *)mmap(0, len, PROT_READ, MAP_SHARED, bsfd, 0);
	if (bitset == MAP_FAILED) {
		VERB(VNORM, "failed to mmap %d bytes of bitset\n", len) {
			perror("mmap");
		}
		return -4;
	}

	return g_cnt;
}

void
printlrstr(letter_t *lstr) {
	char cstr[20] = "";
	int rv;

	rv = l2crstr(lstr, cstr);
	printf("%s", cstr);
}

void
printlstr(letter_t *lstr) {
	char cstr[20] = "";
	int rv;

	rv = l2cstr(lstr, cstr);
	printf("%s", cstr);
}

/* initialize a bunch of things. 0 = success. */
int
initstuff()
{
	int r, c;
	unsigned int random;

	/* seed rng */
	random = (getpid() * time(NULL)) >> 4;
	srand(random);
	random = 0;

	/* bag. Names bags A-Z, or custom. '?' mean randomize */
	bagtag = '\0';
	if (bagname == NULL) {
		if (bagstr == NULL) {
			bagname = "?random";
		} else {
			bagname = "_adhoc";
		}
	}
	ASSERT(bagname != NULL);
	bagtag = bagname[0];
	if (bagtag == '?') {
		random = 1;
		if (bagname[1] != '\0') bagname++;
		bagtag = bagname[0];
	}
	if ((bagstr == NULL) && isupper(bagtag))
		bagstr = bags[bagtag - 'A'];
	if ((bagstr == NULL) && random) {
		bagstr = basebag;
	}
	if (bagstr == NULL) {
		vprintf(VNORM, "No bag contents specified\n");
		return 1;
	}
	ASSERT((bagtag != '\0' ) && (bagname != NULL) && (bagstr != NULL));
	DBG(DBG_BAG, "bag [%c]%s = %s\n", bagtag, bagname, bagstr);
	globalbag = strdup(bagstr);	// to get size allocated
	if (casec2lstr(bagstr, globalbag) != 0) {
		vprintf(VNORM, "bag string has invalid characters.\n"
		    "Use only letters and '?' for blank\n");
		return 1;
	}
	if (random) {
		int shakes;
		int s1, s2, len;
		letter_t tl;

		len = strlen(globalbag);
		shakes = len * len * 2;
		/* shake the bag. */
		while (shakes--) {
			s1 = rand();
			s2 = (s1/len) % len;
			s1 %= len;
			tl = globalbag[s1];
			globalbag[s1] = globalbag[s2];
			globalbag[s2] = tl;
		}
		vprintf(VVERB, "bag %s was shaken.\n", bagname);
	}

	/* set up empty board */
	for (r = 0; r < BOARDY; r++) {
		for (c = 0; c < BOARDX; c++) {
			(emptyboard.spaces[r][c]).all = 0;
			switch (boni[r][c]) {
			case DL:
			case TL:
				emptyboard.spaces[r][c].f.lm = boni[r][c] + 1;
				emptyboard.spaces[r][c].f.wm = 1;
				break;
			case DW:
			case TW:
				emptyboard.spaces[r][c].f.wm = boni[r][c] - 1;
				emptyboard.spaces[r][c].f.lm = 1;
				break;
			default:
				emptyboard.spaces[r][c].f.lm = 1;
				emptyboard.spaces[r][c].f.wm = 1;
			}
		}
	}
	/* mark all legal start moves */
	startboard = emptyboard; 	// does this still work? YES.
	for (r = 1; r <= STARTC; r++) {
		/* there are only 7 unique legal starting positions. */
		startboard.spaces[STARTR][r].f.plays = ALLPHABITS;
	}
	// init stats
	globalstats.evals = 0;
	globalstats.evtime = 0;
	globalstats.maxdepth = 0;
	globalstats.maxwidth = 0;
	globalstats.wordhiscore = 0;
	globalstats.hiscore = 0;

	/* make up our starting position. */
	startp.board = startboard;
	startp.score = 0;
	startp.bagindex = 0;
	startp.rack = emptyrack;
	startp.move = emptymove;
	startp.prev = NULL;
	startp.state = START;

	if (rackstr != NULL) {
		if (strlen(rackstr) > 7) {
			vprintf(VNORM, "rack can only have up to 7 letters.\n");
			return 1;
		}
		if (casec2lstr(rackstr, startp.rack.tiles) != 0) {
			vprintf(VNORM, "rack string has invalid characters.\n"
			    "Use only letters and '?' for blank\n");
			return 1;
		}
		DBG(DBG_RACK, "starting with a rack of:") {
			printlstr(startp.rack.tiles); printf("\n");
		}
	}
	return 0;
}

/* used in call to qsort() */
int
lcmp(const void *l1, const void *l2)
{
	return *(const char *)l1 - *(const char *)l2;
}

void
printnode(char *msg, uint32_t nid)
{
	char l = gl(gaddag[nid]);
	printf("%s: node %d = [%d|%c|%c|%c(%d)]\n", msg, nid, gc(gaddag[nid]),
gs(gaddag[nid])?'$': ' ', gf(gaddag[nid])? '.': ' ',l?l2c(l):' ',l );
}

/*
 * a compare function for a letter versus a gaddag-letter.
 * 0 = a match.
 * <0 = l is past gl (l > gl)
 * >0 = l before gl (l < gl)
 * a blank (played or unplayed) matches any gl except SEP.
 */
inline int
cmplgl(letter_t l, letter_t g)
{
	if (is_blank(l) && (g != SEP)) {
		return 0;
	}
	return (l - g);
}

inline
int findl(char *s, char c)
{
	return (strchr(s,c) - s);
}

/* return the next letter. */
inline letter_t
nextl(bs_t bs, int *curid)
{
	letter_t l;
	int idbs = bitset[*curid];

	l = ffs(bs);
	*curid += popc(idbs<<(32-l));
}

/*
 * bsi: bitset iterator. Does what mi does with bitsets.
 * IN: sorted array of letters. May contain MARK, SEP and blanks.
 * IN: nodeid.
 * IN/OUT: index of letter to be used
 * IN/OUT: current node id
 * OUT: continue or end of matches value (0=no more matches, 1=continue)
 * Initial call: strndx=0 and curid=-1.
 */
int
bsi(letter_t *s, int nodeid, int *i, int *curid)
{
	bs_t rbs;
	bs_t idbs;
	bs_t cbs;
	gn_t curnode;
	letter_t l;

	rbs = lstr2bs(s);
	idbs = bitset[*curid];
	cbs = rbs & idbs;

/* damm blanks. */	

	if (cbs != 0) {
		l = ffs(cbs);
		*i = findl(s, l);
		*curid = popc(idbs<<(32-l));
	} else {
	}

}



/*
 * match iterator: non-recursive iteration function for letters against
 * gaddag edges.  Re-entrant and state savable.
 * IN: sorted array of letters. May contain MARK, SEP and blanks.
 * IN: nodeid.
 * IN/OUT: index of letter to be used
 * IN/OUT: current node id
 * OUT: continue or end of matches value (0=no more matches, 1=continue)
 * Initial call: strndx=0 and curid=-1.
 * ? should we inline this?  It's kinda big...
 * Tweaked for that one corner case.  Or two.
 */
int
mi(letter_t *s, int nodeid, int *i, int *curid)
{
	int reenter = 1;
DBG(DBG_MATCH, "id=%d i=%d, curid=%d s=", nodeid, *i, *curid) {
	printlstr(s);
	if (*curid >= 0)
		printnode(" curid", *curid);
	else
		printf(" curid = -1\n");
}

	if (*curid < 0) {
		reenter = 0;
		*curid = nodeid;
	}

	for (; s[*i] != '\0'; (*i)++) {
		letter_t l = s[*i];
		letter_t nl;
		gn_t curnode;
		int tst;
		int bl;
		if ((l == MARK) || (l == s[(*i)+1])) continue;
		bl = is_pblank(l) || is_ublank(l);
		if (is_ublank(l)) *curid = nodeid;	/* start over */

		do {
			curnode = gaddag[*curid];
			nl = gl(curnode);
			tst=cmplgl(l,nl);
DBG(DBG_MATCH, "inner loop, i=%d, cid=%d, reenter=%d tst=%d (%c - %c)\n", *i, *curid, reenter, tst, l2c(l), l2c(nl));
			if (tst == 0) {
				if (bl) {
					s[*i] = blankgl(nl);
				}
				if (!reenter) {
					return 1;
				} else {
					reenter = 0;
				}
			}
			if ((tst >= 0) && !gs(curnode)) {
				(*curid)++;
			} else {
				break;
			}
		} while (tst >= 0);
		if (bl) s[*i] = UBLANK;
	}
	return 0;
}

/* anagram using match iterator. */
doanagram_d(uint32_t nodeid, letter_t *sofar, int depth, letter_t *rest)
{
	int anas = 0;
	int curid = -1;
	int i = 0;

	DBG(DBG_ANA, "doing anagram lvl %d", depth) {
		printnode(" with", nodeid);
	}

	while (mi(rest, nodeid, &i, &curid)) {
DBG(DBG_ANA, "matched r[%d]=%c from ", i, l2c(rest[i])) {
		printlstr(rest);
		printnode(" using", curid);
}
		sofar[depth] = rest[i];
		rest[i] = MARK;
		if (gf(gaddag[curid])) {
			anas++;
			VERB(VNORM, "") {
				printlrstr(sofar); printf("\n");
			}
		}
		anas += doanagram_d(gc(gaddag[curid]), sofar, depth+1, rest);
		rest[i] = sofar[depth];
	}
DBG(DBG_ANA, "Pop %c at %d back to ", l2c(sofar[depth]), depth) {
	printlstr(rest); printf("\n");
}
	sofar[depth] = '\0';
	return anas;
}

/* try again, and this time THINK! */
int
doanagram_c(uint32_t nodeid, letter_t *sofar, int depth, letter_t *rest)
{
	int i;
	letter_t wordl;
	int bl;
	int tst;
	int curid;
	gn_t curnode;
	letter_t nodel;
	int anas = 0;
	char *printstr;

	curid = nodeid;

	DBG(DBG_ANA, "doing anagram (%d)node %u=0x%x (ls=%d, rs=%d)\n", depth, nodeid, gaddag[nodeid],strlen(sofar), strlen(rest)) {
		printnode("in doanagram", nodeid);
	}

	for (i = 0; rest[i] != '\0'; i++) {
		wordl = rest[i];
		if (wordl == MARK) continue;
		bl = is_ublank(wordl);
		if (!bl && (wordl == rest[i+1])) continue;
		if (bl) curid = nodeid;
		do {
			curnode = gaddag[curid];
			nodel = gl(curnode);
			tst = cmplgl(wordl,nodel);
DBG(DBG_ANA, "looking for a match with %c(%hhx) or %c(%hhx) diff is %d\n", l2c(wordl), wordl, l2c(nodel), nodel, tst);
			if (tst == 0) {
				/* push */
				if (bl) {
					sofar[depth] = blankgl(nodel);
				} else {
					sofar[depth] = wordl;
				}
				rest[i] = MARK;
DBG(DBG_ANA, "push %c(%d) from rest[%d] to sofar[%d]\n", l2c(sofar[depth]), sofar[depth], i, depth);
				if (gf(curnode)) {
					/* print it */
					anas++;
					printstr = strdup(sofar);
					l2crstr(sofar, printstr);
					vprintf(VNORM, "%s\n", printstr);
					free(printstr);
				}
				/* anas += recurse */
				anas += doanagram_c(gc(curnode), sofar, depth+1, rest);
				/* pop */
				rest[i] = wordl;
				sofar[depth] = '\0';
DBG(DBG_ANA, "Pop %c(%d) from sofar[%d] to rest[%d]\n", l2c(rest[i]), rest[i], depth,i);
			}
			if ((tst >= 0) && !gs(curnode)) {
				curid++;
DBG(DBG_ANA, "advance node to %d\n", curid);
			} else {
				break;
			}
		} while (tst >= 0);
	}
	return anas;
}

/* show all words in dictionary that can be made with these letters. */
int
anagramstr(letter_t *letters, int doscore)
{
	char *lset;
	char *sofar;
	int score;

	if ((letters == NULL) || strlen(letters) < 2)
		return 0;
	lset = strdup(letters);
	DBG(DBG_ANA, "sorting...\n");
	qsort(lset, strlen(lset), 1, lcmp);
	/* now have a sorted set of letters to match with */
	sofar = strdup(lset);
	bzero(sofar, strlen(lset));
	DBG(DBG_ANA, "let the recursion begin on\n") {
		printlstr(lset); printf("\n");
	}
	return doanagram_d(0, sofar, 0, lset);
}

/* lookup using match iterator, non-recursive version. */
/* apparently, it's very hard to do non-recurive with blanks. */
/* clue: need to be able to "back up" ie i++.  I think that implies a stack.*/

int
mnr_lookup(int i, letter_t *word, uint32_t nodeid)
{
	letter_t wl;
	letter_t slw[2];
	int nextid = -1;
	int j = 0;
	int matchcount = 0;

	if (i == 0) {
DBG(DBG_LOOK, "Nothing to match\n");
		return 0;
	}

while (i > 0) {
	wl = word[--i];
	slw[0] = wl;
	slw[1] = '\0';

DBG(DBG_LOOK, "i=%d, word[i]=%c, nid=%d\n", i, l2c(slw[1]), nodeid);
	while (mi(slw, nodeid, &j, &nextid)) {
		word[i] = slw[0];
DBG(DBG_LOOK, "matched %c(%d) at %d\n", l2c(slw[j]), slw[j], nextid);
		if ((i == 0) && gf(gaddag[nextid])) {
			matchcount++;
			VERB(VNORM, "") {
				printlstr(word); printf("\n");
			}
		} else {
			matchcount += m_lookup(i, word, gc(gaddag[nextid]));
		}
	}
	word[i] = wl;
}
DBG(DBG_LOOK, "found %d matches\n", matchcount);
	return matchcount;
}

/* lookup using match iterator.
 * first, be recursive.
 */
int
m_lookup(int i, letter_t *word, uint32_t nodeid)
{
	letter_t wl;
	letter_t slw[2];
	int nextid = -1;
	int j = 0;
	int matchcount = 0;

	if (i == 0) {
DBG(DBG_LOOK, "Nothing to match\n");
		return 0;
	}

	wl = word[--i];
	slw[0] = wl;
	slw[1] = '\0';

DBG(DBG_LOOK, "i=%d, word[i]=%c, nid=%d\n", i, l2c(slw[1]), nodeid);
	while (mi(slw, nodeid, &j, &nextid)) {
		word[i] = slw[0];
DBG(DBG_LOOK, "matched %c(%d) at %d\n", l2c(slw[j]), slw[j], nextid);
		if ((i == 0) && gf(gaddag[nextid])) {
			matchcount++;
			VERB(VNORM, "") {
				printlstr(word); printf("\n");
			}
		} else {
			matchcount += m_lookup(i, word, gc(gaddag[nextid]));
		}
	}
	word[i] = wl;
DBG(DBG_LOOK, "found %d matches\n", matchcount);
	return matchcount;
}

/* NEWGADDAG
 * need to re-re-write lookup.
 * When called, look for the next letter in our sibgroup.
 * if found, last letter AND final, count it (print it)
 * returns number of words matched.
 * NOTE: root is not weird. NOTE: still backwards.
 */
int
r_lookup(int i, letter_t *word, uint32_t nodeid)
{
	gn_t curnode;
	letter_t wordl;
	letter_t nodel;
	int matchcount = 0;
	int tst;

	if (i == 0) {
DBG(DBG_LOOK, "Nothing to match\n");
		return 0;
	}

	wordl = word[--i];
DBG(DBG_LOOK, "word[%d]=%c(%d), nid=%u n=%x", i, l2c(wordl), wordl, nodeid, curnode) {
	char *str = strdup(word);
	l2cstr(word, str);
	printf(" word=%s\n", str);
}

	do {
		curnode = gaddag[nodeid];
		nodel = gl(curnode);
		tst = cmplgl(wordl, nodel);
		if (tst == 0) {
DBG(DBG_LOOK, "matched %c(%d) with %c(%d) at %d\n", l2c(wordl), wordl, l2c(nodel), nodel, nodeid);
			if (is_ublank(wordl)) {
				word[i] = blankgl(nodel);
			}
			if (i == 0) {
				if (gf(curnode)) {
					matchcount++;
					VERB(VNORM, "") {
						printlstr(word); printf("\n");
					}
				}
			} else {
				matchcount += r_lookup(i, word, gc(curnode));
			}
			if (is_ublank(wordl)) {
				word[i] = wordl;
			}
		}
		if ((tst >= 0) && !gs(curnode)) {
			nodeid++;
		} else {
			break;
		}
	} while (tst >= 0);

DBG(DBG_LOOK, "found %d matches\n", matchcount);
	return matchcount;
}

/* update values of empty spaces with new cross letter move scores. */
void
updatemls(board_t *b, int dir, int mr, int mc, int val)
{
	int dr = 0, dc = 0;
	int r, c;
	int under;

	if (dir == M_HORIZ) {
		dr = 1;
		under = b->spaces[mr][mc].f.hmls;
	} else {
		dc = 1;
		under = b->spaces[mr][mc].f.vmls;
	}
DBG(DBG_MLS, "update %cmls vals for (%d,%d) with %d+%d\n", dc? 'h':'v', mr, mc, val, under);
	val += under;
	/* you have to have it both ways. */
	r = mr + dr;
	c = mc + dc;
	while (b->spaces[r][c].f.letter  && ((r<BOARDY)&&(c<BOARDX))) {
		r += dr; c += dc;
	}
	if ((r<BOARDY && c<BOARDX)) {
		if (dir == M_HORIZ) {
			b->spaces[r][c].f.hmls = val;
		} else {
			b->spaces[r][c].f.vmls = val;
		}
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
	r = mr - dr;
	c = mc - dc;
	while (b->spaces[r][c].f.letter && ((r>=0)&&(c>=0))) {
		r -= dr; c -= dc;
	}
	if ((r>=0)&&(c>=0)) {
		if (dir == M_HORIZ) {
			b->spaces[r][c].f.hmls = val;
		} else {
			b->spaces[r][c].f.vmls = val;
		}
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
}

/*
 * return the value of placing move m on board b.   If doit is set,
 * actually place the tiles, otherise we are just looking.
 * playthrough is for moves that include tiles already on board.
 */
int
score(move_t *m, board_t *b, int doit, int playthrough)
{
	int ssf = 0, xssf = 0;	// [vertical] score so far
	int ends = 0;		// connected at ends.
	int ps;			// non-bonus sum of tile scores palyed
	int mult = 1;		// word multiplier
	int deltah = 0, deltav = 0;	// incrementers
	int r, c, i = 0;
	int ts;			// plain tile score
	int tts = 0;		// total ts
	int tbs;		// tile bonus score
	int bingo = 0;
	int ortho;
	int total;
	space_t *sp;

DBG(DBG_SCORE,"in score with (%d,%d)->%s %d letters\n", m->row, m->col,  m->dir == M_HORIZ ? "horiz" : "vert", m->lcount);

	if (m->dir == M_HORIZ) {
		ends = b->spaces[m->row][m->col].f.vmls;
DBG(DBG_SCORE, "get H beginning end score %d at (%d, %d)\n", ends, m->row, m->col);
		deltav = 1;
		ortho = M_VERT;
	} else {
		ends = b->spaces[m->row][m->col].f.hmls;
DBG(DBG_SCORE, "get V beginning end score %d at (%d, %d)\n", ends, m->row, m->col);
		deltah = 1;
		ortho = M_HORIZ;
	};
DBG(DBG_SCORE, "moving %d so deltah=%d and deltav=%d\n", m->dir, deltah, deltav);

	if (m->lcount >= RACKSIZE) bingo = BINGOBONUS;

	for (i=0, r=m->row, c=m->col; i < m->lcount; r += deltah, c += deltav) {
		sp = &(b->spaces[r][c]);
		if (sp->f.letter == EMPTY) {
DBG(DBG_SCORE, "placing %dth out of %d %c(%d) at (%d,%d)\n", i, m->lcount, l2c(m->tiles[i]), m->tiles[i], r, c);
DBG(DBG_SCORE, "on space (%d,%d) lm=%d wm=%d\n",r,c, sp->f.lm, sp->f.wm);
			mult *= sp->f.wm;	// word multiplier
			ts = lval(m->tiles[i]);	// ts = tile score
			tts += ts;		// total ts
			tbs = ts * sp->f.lm;	// tile bonus score
			ssf += ts;		// add current tile
			if ((m->dir == M_HORIZ) && sp->f.hmls) {
DBG(DBG_SCORE, "horiz move (%d + %d) * %d \n", sp->f.hmls, tbs, sp->f.wm);
				xssf += (sp->f.hmls + tbs) * sp->f.wm;
			}
			if ((m->dir == M_VERT) && sp->f.vmls) {
DBG(DBG_SCORE, "vert move (%d + %d) * %d \n", sp->f.vmls, tbs, sp->f.wm);
				xssf += (sp->f.vmls + tbs) * sp->f.wm;
			}
DBG(DBG_SCORE, "tile %c scores: ts=%d, tbs=%d, ssf=%d, xssf=%d\n", l2c(m->tiles[i]), ts, tbs, ssf, xssf);
			if (doit) {
				sp->f.letter = m->tiles[i];
				/* update mls stuff. Not easy. */
				updatemls(b, m->dir, r, c, ts);
			}
			i++;	 // next letter please
		} else {
			if (playthrough) {
				if (m->tiles[i] != sp->f.letter) {
vprintf(VNORM, "warning: playthrough %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->f.letter), sp->f.letter);
				}
				i++;	// I'm not sure about this....
			}
			ts = lval(sp->f.letter); // ts = tile score
			tts += ts;		// total ts
			ssf += ts;		// add current tile
		}
	}
	if (m->dir == M_HORIZ) {
		ends += b->spaces[r][c-1].f.vmls;
DBG(DBG_SCORE, "get H ending end score %d at (%d, %d)\n", ends, r, c);
		deltav = 1;
		ortho = M_VERT;
	} else {
		ends += b->spaces[r-1][c].f.hmls;
DBG(DBG_SCORE, "get V ending end score %d at (%d, %d)\n", ends, r, c);
		deltah = 1;
		ortho = M_HORIZ;
	};
	if (doit)
		updatemls(b, ortho, m->row, m->col, tts + ends);	// on ends
	total = bingo + (ssf * mult) + xssf + ends;
DBG(DBG_SCORE, "total score is bingo=%d + sum=%d * mult=%d + xc=%d + ends=%d = %d\n", bingo, ssf, mult, xssf, ends, total);
	return total;
}

/* text display of board, what controls the actual info displayed */
void
showboard(board_t b, int what)
{
	int r, c;
	space_t *sp;
	int bl;

	if ((what <= B_NONE) || (what >= B_BAD))
		return;		/* nope. */

	switch (what) {
	case B_TILES:
		printf("Letters on board\n");
		break;
	case B_HMLS:
		printf("Horizontal nmove letter scores\n");
		break;
	case B_VMLS:
		printf("Vertical nmove letter scores\n");
		break;
	case B_PLAYS:
		printf("Playable bits\n");
		break;
	case B_BONUS:
		printf("Space bonus values\n");
		break;
	default:
		printf("unknown. what?\n");
		break;
	}
	printf("  ");
	for (c = 0; c < BOARDY; c++) {
		printf("  %c ", coltags[c]);
	}
	printf("\n");
	for (r = 0; r < BOARDY; r++) {
		printf("%2d:", r+1);
		for (c = 0; c < BOARDX; c++) {
			sp = &(b.spaces[r][c]);
			switch (what) {
			case B_TILES:
				if (sp->f.letter == EMPTY) {
					printf(" _  ");
				} else {
					printf(" %c  ", l2c(sp->f.letter));
				}
				break;
			case B_VMLS:
				if (sp->f.vmls)
					printf("^%-2d ", sp->f.vmls);
				else if (sp->f.letter != EMPTY)
					printf(" %c  ", l2c(sp->f.letter));
				else
					printf("    ");
				break;
			case B_HMLS:
				if (sp->f.hmls)
					printf(">%-2d ", sp->f.hmls);
				else if (sp->f.letter != EMPTY)
					printf(" %c  ", l2c(sp->f.letter));
				else
					printf("    ");
				break;
			case B_PLAYS:
				if (sp->f.plays == 0) {
					printf("--- ");
				} else if (sp->f.plays == ALLPHABITS) {
					printf(" *  ");
				} else {
					printf(" ?  ");
				}
				break;
			case B_BONUS:
				bl = sp->f.lm -1 ? sp->f.lm-1 : 0;
				bl = sp->f.wm -1 ? sp->f.wm+1 : bl;
				printf(" %s ", bonusnames[bl]);
			}
		}
		printf("\n");
	}
	printf("\n");
}

/* read a move in "std" notation. rv of 0 is success.
 */
int
parsemove(char *str, move_t *m)
{
	char *cp;
	int dd = 0;
	int len, plen;
	char *word;

	if ((str == NULL) || (str[0] == '\0')) {
		return 1;
	}
	if (m == NULL) {
		return 2;
	}
	m->score = 0;
	/*
	 * format: C##:LLLLLLL or ##C:LLLLLLL or LLLLLLL
	 * assume string is trimmed. ## maybe be 1-15 (one or two digits).
	 * C is column tag A-O.  From 1 to 7 Ls.  Lowercase is played blank.
	 * otherwise regular letter. If no position, assumed start (7H)
	 */
	cp = strchr(str, ':');
	if (cp != NULL) {
		*cp ='\0';
		plen = strlen(str);
		*cp =':';
		cp++; // move past :
	} else {
		plen = 0;
		cp = str;	// use whole arg
		m->dir = M_HORIZ;
		m->row = STARTR; m->col=STARTC;
	}
	len = strlen(cp);
DBG(DBG_ARGS, "plen=%d, len=%d, word=%s\n", plen, len, cp);
	if (plen) {
		if ((plen != 2) && (plen != 3)) {
			return 3;
		}
		if (isupper(str[0]) && isdigit(str[1])) {
			m->dir = M_VERT;
			m->col = str[0] - 'A';
			m->row = str[1] - '0';
			if (plen == 3) {
				m->row = m->row*10 + (str[2] - '0');
			}
		} else if (isdigit(str[0]) && isupper(str[plen-1])) {
			m->dir = M_HORIZ;
			m->col = str[plen-1] - 'A';
			m->row = str[0] - '0';
			if (plen == 3) {
				m->row = m->row*10 + (str[1] - '0');
			}
		} else {
			return 3;
		}
		/* our stuff is 0 based. */
		m->row -= 1;
	}

	if ((m->row < 0) || (m->row > BOARDY) ||
	    (m->col < 0) || (m->col > BOARDX)) {
		return 4;
	}

	if ((m->dir == M_HORIZ) && ((len + m->col) > BOARDX)) {
		vprintf(VNORM, "Word of len %d at %d goes off board\n", len, m->col);
		return 4;
	}
	if ((m->dir == M_VERT) && ((len + m->row) > BOARDY)) {
		vprintf(VNORM, "Word of len %d at %d goes off board\n", len, m->row);
		return 4;
	}

	if (len > BOARDSIZE) {
		vprintf(VNORM, "Word %s of len %d too long\n", str, len);
		return 4;
	}
	m->lcount = len;
	/* now the string. */
	if (c2lstr(cp, m->tiles, PLAYED)) {
		vprintf(VNORM, "%s had invalid characters\n", cp, len);
		return 5;
	}
	return 0;
}


void
printmove(move_t *m, int rev)
{
	if (m->dir == M_HORIZ) {
		printf("%d%c:", m->row, coltags[(m->col)-1]);
	} else {
		printf("%c%d:", coltags[(m->col)-1], m->row);
	}
	if (rev == 0) {
		printlrstr(m->tiles);
	} else {
		revnstr(m->tiles, rev);
		printlstr(m->tiles);
		revnstr(m->tiles, rev);
	}
	if (m->score > 0) {
		printf(" scores %d", m->score);
	}
	printf("\n");
}

/* see if l is a sib of nodeid, and if so return which one. -1 if not found*/
int
findin(letter_t l, int nodeid)
{
	gn_t node;

	do {
		node = gaddag[nodeid];
		if (gl(node) == l) return nodeid;
		if (gs(node)) break;
		nodeid++;
	} while (1);
	return -1;
}

/* more utility small funcs */

/* no letter directly horizontal. */
inline int
nldh(board_t *b, int ar, int ac, int pos) {
	if (pos <= 0)
		return ((ac == 0) || (b->spaces[ar][ac-1].f.letter == 0));
	else
		return ((ac == 14) || (b->spaces[ar][ac+1].f.letter == 0));
}

/* no letter directly left */
inline int
nldl(board_t *b, int ar, int ac) {
	return ((ac == 0) || (b->spaces[ar][ac-1].f.letter == 0));
}

/* no letter directly right */
inline int
nldr(board_t *b, int ar, int ac) {
	return ((ac == 14) || (b->spaces[ar][ac+1].f.letter == 0));
}

void inline
appendl(letter_t *w, letter_t l) {
	int i = strlen(w);
	w[i] = l;
	w[i+1]='\0';
}

void inline
apchopl(letter_t *w) {
	int i = strlen(w);
	w[i-1] = '\0';
}

void inline
prependl(letter_t l, letter_t *w) {
	letter_t c;
	int i = strlen(w);
	for (i = strlen(w)+1; i > 0; i--) {
		w[i] = w[i-1];
	}
	w[0] = l;
}

void inline
prechopl(letter_t *w) {
	int i = 1;
	do {
		w[i-1] = w[i];
	} while (w[i++] != '\0');
}


/* GoOn using gen iterator Gi. Still recursive. */
/* initial call with pos=0, nodeid=0, and m->tiles empty. */
/* fix up- directional. */
int
GoOn2(board_t *b, move_t *m, int pos, rack_t *r,  int nodeid)
{
	int movecnt = 0;
	int curid = -1;
	int cid;
	int sepid;
 	letter_t *w = m->tiles;
	int ac = m->col;
	int ar = m->row;
	int i = 0;
	int ndx = 0;
	int prelen;
	int curcol = ac;
	letter_t *lp;

DBG(DBG_GOON, "at %d,%d(%-d) node=%d", ar,ac,pos, nodeid) {
	printf(" - word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	ndx = strlen(w);	/* depth */
	if (pos > 0) {
		prelen = pos;
		curcol += ndx;
	} else {
		prelen = ndx + 1;
	}
	lp = &(w[ndx]); w[ndx+1] = '\0';
	while (Gi(b, m, pos, r, nodeid, &i, &curid, lp)) {
DBG(DBG_GOON, "Gen gave i=%d, id=%d, l=%c and rack ", i, curid, l2c(*lp)) {
	printlstr(r->tiles); printf("\n");
}
		if ((gf(gaddag[curid])) && nldh(b, ar, curcol, pos)) {
			if (doscore) {
				m->score = score(m, b, 0, 1);
			}
			VERB(VNORM, "") {
				printmove(m, pos);
			}
			movecnt++;
		}
		cid = gc(gaddag[curid]);
		if (((pos <= 0) && (curcol > 0))  || ((pos > 0) && (curcol < 14))) {
			/* recurse */
DBG(DBG_GOON, "recurse 1 (%d, %d, %d, word, rack, id=%d)", m->row, m->col, pos, cid) {
	printf(" word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
			if (pos <= 0) m->col--;
			movecnt += GoOn2(b, m, pos, r,  cid);
			if (pos <= 0) m->col++;
		}
		/* have to handle the ^ */
		if (pos <= 0) {
			sepid = findin(SEP, cid);
DBG(DBG_GOON, "sep at %d from %d\n", sepid, cid);
			if ((sepid != -1) && nldl(b, ar, curcol) && (curcol < 14)) {
				cid = gc(gaddag[sepid]);
DBG(DBG_GOON, "recurse 3 (%d, %d, 1, word, rack, id=%d\n", ar, m->col, cid) {
	printf(" - word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
				movecnt += GoOn2(b, m, prelen, r, cid);
			}
		}
	}
	*lp = '\0';
	return movecnt;
}

/* rne: rack not empty. */
int inline
rne(rack_t *r)
{
	int i;
	for (i = 0; r->tiles[i] != '\0'; i++)
	{
		if (r->tiles[i] != MARK)
			return 1;
	}
	return 0;
}


/* with bitsets. should be simpler. maybe. */
int
Gi2(board_t *b, move_t *m, int pos, rack_t *r, int nodeid, int *i, int *curid, letter_t *L, bs_t *bs)
{
	int lid;
	int ac = m->col;
	int ar = m->row;
	letter_t *w = m->tiles;
	letter_t BL;

DBG(DBG_GEN, "at %d,%d(%-d) with bs %x in node %d",  ar,ac,pos, *bs, nodeid) {
	printf(" ~word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	BL = b->spaces[ar][ac+pos].f.letter;
	if (BL) {
DBG(DBG_GEN, "found %c on board at %d, %d\n", l2c(BL), ar, ac,);
		*bs = l2b(BL);
/*
		if ((*i)++ > 0) return 0;
		if (*curid < 0) {
			*curid = nodeid;
		}
		*curid = findin(deblank(BL), *curid);
		if (*curid != -1) {
			*L = BL;
DBG(DBG_GEN, "found match %c node=%d\n", l2c(BL), *curid);
			return 1;
		}
*/
	} else {
		bs_t rbs = lstr2bs(r->tiles);
		if (*curid < 0) {
			*curid = nodeid;
			*bs = rbs & bitset[*curid];
		}
		if (*bs == UBLBIT) {
			*curid = nodeid;
			*bs = rbs & ALLPHABITS;
		}
		*L = nextl(*bs, &curid);
		return 1;
	}
	return 0;

#ifdef BOOHOO
		if (*curid >= 0) {
DBG(DBG_GEN, "(%d)Push %c back on rack\n", *i, l2c(*L));
			r->tiles[*i] = *L;
		} else {
			if (!rne(r)) return 0;
		}
		while (mi(r->tiles, nodeid, i, curid)) {
			*L = r->tiles[*i];
			r->tiles[*i] = MARK;
DBG(DBG_GEN, "matched %c i=%d, node=%d\n", l2c(*L), *i, *curid);
			return 1;
		}
	}
	*L = '\0';
	return 0;
#endif
}

/* turn Gen into an itertator, just like mi. */
/* IN: b - board
 * IN/OUT: m - move
 * IN: pos - offset from anchor
 * IN/OUT: r - rack
 * IN: nodeid - starting nodeid
 * IN/OUT: curid - internal state
 * IN/OUT: i - internal state for match iterator
 * IN/OUT: L - letter matched, \0 if no match found.
 * returns: 1 if letter (L) is found, 0 if all out.
 * i, curid and L must be preserved between calls.
 * initial call: Gi(b, m, pos, r, nodeid, &i(0), &curid(-1), &L(any))
 */
int
Gi(board_t *b, move_t *m, int pos, rack_t *r, int nodeid, int *i, int *curid, letter_t *L)
{
	int lid;
	int ac = m->col;
	int ar = m->row;
	letter_t *w = m->tiles;
	letter_t BL;

DBG(DBG_GEN, "at %d,%d(%-d) with in node %d",  ar,ac,pos, nodeid) {
	printf(" ~word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	BL = b->spaces[ar][ac+pos].f.letter;
	if (BL) {
DBG(DBG_GEN, "found %c on board at %d, %d, i=%d\n", l2c(BL), ar, ac, *i);
		if ((*i)++ > 0) return 0;
		if (*curid < 0) {
			*curid = nodeid;
		}
		*curid = findin(deblank(BL), *curid);
		if (*curid != -1) {
			*L = BL;
DBG(DBG_GEN, "found match %c node=%d\n", l2c(BL), *curid);
			return 1;
		}
	} else {
		if (*curid >= 0) {
DBG(DBG_GEN, "(%d)Push %c back on rack\n", *i, l2c(*L));
			r->tiles[*i] = *L;
		} else {
			if (!rne(r)) return 0;
		}
		while (mi(r->tiles, nodeid, i, curid)) {
			*L = r->tiles[*i];
			r->tiles[*i] = MARK;
DBG(DBG_GEN, "matched %c i=%d, node=%d\n", l2c(*L), *i, *curid);
			return 1;
		}
	}
	*L = '\0';
	return 0;
}

/* do this later... */
#ifdef DEBUG
/* here we indulge in some paranoia. */
void
verify()
{
	/* some test cases for mi. */
	{
		char w[16] = ""; int nid = 0; int cid = -1; int i = 0;
		int rv;

		/* simple match. */
		c2lstr("A", w, 0); nid=0;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('A')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* skip dup letters. */
		c2lstr("XXXXX", w, 0); nid=0;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('X')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* skip mark */
		c2lstr("\\B", w, 0); nid=0;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('B')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* skip multiple marks */
		c2lstr("\\\\\\B\\\\\\", w, 0); nid=0;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('B')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* match ^ */
		c2lstr("^", w, 0); nid=26;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('^')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* match ^ at end */	
		c2lstr("J^", w, 0); nid=26;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('J')));
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('^')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton letter in node set */
		c2lstr("K", w, 0); nid=121;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('K')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton letter, no match */
		c2lstr("JL", w, 0); nid=121;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton, blank. */
		c2lstr("JL?", w, 0); nid=121;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('k')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton ^, match */
		c2lstr("M^", w, 0); nid=52;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
VERB(VNOISY, "verify mi: rv=%d, i=%d, cid=%d  ", rv, i, cid) {
printlstr(w); printf(" %c %d \n", l2c(w[0]), w[0]);  
}
		ASSERT( (rv != 0) && (w[i] == c2l('^')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton ^, no match */
		c2lstr("Z", w, 0); nid=52;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton ^, no match with blank */
		c2lstr("A?", w, 0); nid=52;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* singleton ^, match with blank */
		c2lstr("A?^", w, 0); nid=52;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('^')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* match two. */
		c2lstr("AB", w, 0); nid=0;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('A')));
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('B')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);

		/* match two with gap */
		c2lstr("CH", w, 0); nid=53;cid=-1;i=0;
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('C')));
		rv = mi(w, nid, &i, &cid);
		ASSERT( (rv != 0) && (w[i] == c2l('H')));
		rv = mi(w, nid, &i, &cid);
		ASSERT(rv == 0);
	}

}
#endif /* DEBUG */


#define ACT_LOOKUP	0x001
#define	ACT_ANAGRAM	0x002
#define ACT_SCORE	0x004
#define ACT_MOVE	0x008
#define ACT_PLAYTHRU	0x010
#define ACT_GEN		0x020

int
main(int argc, char **argv)
{
	int i = 0, j = 0;
	int rv;
	char *word = NULL;
	int action = 0;
	int c;		// option letter for getopt
	int errs = 0, anas = 0, moves = 0;
	board_t sb;

        while ((c = getopt(argc, argv, "ALSDMPR:Gd:vqsb:B:o:")) != -1) {
                switch(c) {
		case 'G':
			action |= ACT_GEN;
			break;
		case 'P':
			action |= ACT_PLAYTHRU;
			break;
		case 'M':
			action |= ACT_MOVE;
			break;
		case 'D':
			dflags = DBG_ALL;
			break;
		case 'L':
			action |= ACT_LOOKUP;
			break;
		case 'A':
			action |= ACT_ANAGRAM;
			break;
		case 'S':
			action |= ACT_SCORE;
			break;
                case 'v':
                        verbose++;
                        break;
		case 'q':
			verbose = VSHH;
			break;
		case 's':
                        stats++;
                        break;
		case 'd':
			dfn = optarg;
			break;
		case 'b':
			bagname = optarg;
			break;
		case 'B':
			bagstr = optarg;
			break;
		case 'R':
			rackstr = optarg;
			break;
		case 'o':
			gcgfn = optarg;
			break;
		default:
			usage(argv[0]);
			return 1;
			break;
		}
	}
	/* validate options. */
	/* when we have more. bag and dict option are done below */
	if (getdict(dfn) <= 0) {
		vprintf(VNORM, "Dictionary disaster.\n");
		return 3;
	}

	if (initstuff()) {
		vprintf(VNORM, "Initilization implosion\n");
		return 4;
	}
	DBG(DBG_DBG, "using verbose level %d\n", verbose);
#ifdef DEBUG
	verify();
#endif
	sb = emptyboard;
	/* use the rest of the command line as words. */
	for ( ; optind < argc; optind++) {
		move_t argmove;
		char *w;
		int sc, len;
		len = strlen(argv[optind]);

		argmove = emptymove;
DBG(DBG_MAIN, "actions %d on arg %d=%s\n", action, optind, argv[optind]);
		rv = parsemove(argv[optind], &argmove);

		if (rv != 0) {
			vprintf(VNORM, "skipping non-parsable move %s\n", argv[optind]);
			continue;
		}
		if (action & ACT_LOOKUP) {
			if (action & ACT_SCORE) doscore = 1;
			rv = m_lookup(argmove.lcount, argmove.tiles, 0);
			if (rv > 0) {
				char *filled = strdup(argmove.tiles);
				l2cstr(argmove.tiles, filled);
				vprintf(VNORM, "%s matched %d  words\n", argv[optind], rv);
			} else {
				errs++;
				vprintf(VNORM, "%s not in dictionary\n", argv[optind]);
			}
		}
		if (action & (ACT_SCORE|ACT_MOVE)) {
			sc = score(&argmove, &sb, action&ACT_MOVE, action&ACT_PLAYTHRU);
			vprintf(VNORM, "%s scores %d\n", argv[optind], sc);
			if (action&ACT_MOVE) {
				VERB(VNOISY, "results of move:\n") {
					showboard(sb, B_TILES);
					showboard(sb, B_HMLS);
					showboard(sb, B_VMLS);
				}
			}
		}
		if (action & ACT_GEN) {
			if (action & ACT_SCORE) doscore = 1;
			rack_t r = emptyrack;
			strcpy(r.tiles, argmove.tiles);
			argmove.tiles[0] = '\0';
			qsort(r.tiles, strlen(r.tiles), 1, lcmp);
			vprintf(VNORM, "Possible moves for %s:\n", argv[optind]);
			moves = GoOn2(&sb, &argmove, 0, &r, 0);
			vprintf(VNORM, "created %d starting moves from %s\n", moves, argv[optind]);
		}
		if (!errs && action&ACT_ANAGRAM) {
			if (action & ACT_SCORE) doscore = 1;
			vprintf(VNORM, "anagrams of %s are:\n", argv[optind]);
			anas = anagramstr(argmove.tiles, action&ACT_SCORE);
			vprintf(VNORM, "created %d anagrams of %s\n", anas, argv[optind]);
		}
	}

	if (errs) {
		return -errs;
	} else {
		return anas;
	}

	return 0;	// fall-through catch-all.
}
