
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

/* inline optimized code. Use -O4 or so to get really good perf */
#ifdef _popc
inline int
popc(uint32_t w)
{
        int c;
        _popc(w,c);
        return c;
}
#endif

/* ffb = find first bit. ffs is taken. */
#ifdef _ffs
inline int
ffb(uint32_t w)
{
        int c;
        _ffs(w,c);
        return c;
}
#endif

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
static const scthingy_t newsct = { 0, 0, 1, 0, 0, 0, 0, 0, 1, 0 };

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
	VERB(VNORM, "usage: %s [-DALSMvqs][-d dict][-b bag][-B letters][-R letters][-o name] moves...", me) {
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
	"\t        If rc is omitted, uses starting position of 8H.\n"
	"\t        Put row (number) first for horizontal moves. Use lowercase\n"
	"\t	   letter for blank played.\n"
		);
	}
}

/* utility funcs. */

inline bs_t
lstr2bs(letter_t *lstr)
{
	int i = 0;
	bs_t bs = 0;

	while (lstr[i] != '\0') {
		setbit(bs, lstr[i]-1);
//printf("set bit %d at %d, result %x\n", lstr[i], i, bs);
		i++;
	}
	return bs;
}


/*
 * convert character string cstr to a letter string lstr. detects invalid
 * characters.  Returns number of invalid characters, but does conversion
 * even if there are some.
 * played determines which chars are valid:
 * UNPLAYED: A-Z,?,^ (and null char)
 * PLAYED: A-Z,a-z (and null)
 * JUSTPLAY: valid for either PLAYED or UNPLAYED
 */
inline int
c2lstr(char *cstr, char *lstr, int played)
{
	int inv = 0;
	int i = 0;

	if (lstr == NULL) return -1;
	if (cstr == NULL) return 0;
	while (cstr[i] != '\0') {
		lstr[i] = c2l(cstr[i]);
		if (played == UNPLAYED) {
			if (!is_rvalid(lstr[i])) inv++;
		} else if (played == PLAYED) {
			if (!is_bvalid(lstr[i])) inv++;
		} else if (played == JUSTPLAY) {
			if ((!is_bvalid(lstr[i])) && (!is_rvalid(lstr[i])))
				inv++;
		}
		i++;
	}
	lstr[i] = '\0';
	if (played != JUSTPLAY) {
		return inv;
	} else {
		return 0;
	}
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
			emptyboard.spaces[r][c].b.all = 0;
			emptyboard.spaces[r][c].hmbs = 0;
			emptyboard.spaces[r][c].vmbs = 0;
			switch (boni[r][c]) {
			case DL:
			case TL:
				emptyboard.spaces[r][c].b.f.lm = boni[r][c] + 1;
				emptyboard.spaces[r][c].b.f.wm = 1;
				break;
			case DW:
			case TW:
				emptyboard.spaces[r][c].b.f.wm = boni[r][c] - 1;
				emptyboard.spaces[r][c].b.f.lm = 1;
				break;
			default:
				emptyboard.spaces[r][c].b.f.lm = 1;
				emptyboard.spaces[r][c].b.f.wm = 1;
			}
		}
	}
	/* mark all legal start moves */
	startboard = emptyboard; 	// does this still work? YES.
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

/* given a letter, find corresponding nodeid in nid.
 * we can assume that the bit for l is set.
 * NOTE: can't optimize by assuming uint32_t << 32 == 0.  it's not.
 */
inline int
gotol(letter_t l, int nid)
{
	return nid + popc(bitset[nid] << (32-l)) -1;
}

/* return the next letter, and fix up bs */
inline letter_t
nextl(bs_t *bs, int *curid)
{
	letter_t l;
	int idbs = bitset[*curid];

	l = ffb(*bs);
	if (l==0) return 0;
	*curid += popc(idbs<<(32-l))-1;
	clrbit(*bs, l-1);
	return l;
}

/* 
 * compute final bit set given node id.
 */
bs_t
finals(int nid)
{
	bs_t bs = 0;
	letter_t l;
	bs_t nbs = bitset[nid];
	int newid;

	l = nextl(&nbs, &nid);

	while (l != '\0') {
		if (gf(gaddag[nid])) {
			setbit(bs, l-1);
		}
		l = nextl(&nbs, &nid);
	}
	return bs;
}

/* more utility small funcs */

/* ultimate nld: nldn. No letter directly next to.
 * dir is H(0) or V(1), side is -1(before) or 1(after).
 */
inline int
nldn(board_t *b, int r, int c, int dir, int side)
{
	int dr = dir * side;
	int dc = (1 - dir) * side;
	int ve = (c-7)/7;
	int he = (r-7)/7;

	return (((dr==he)||(dc==ve))||(b->spaces[r+dr][c+dc].b.f.letter == 0));
}

/* no letter directly horizontal. */
inline int
nldh(board_t *b, int ar, int ac, int pos) {
	if (pos <= 0)
		return ((ac == 0) || (b->spaces[ar][ac-1].b.f.letter == 0));
	else
		return ((ac == 14) || (b->spaces[ar][ac+1].b.f.letter == 0));
}

/* no letter directly vertical . */
inline int
nldv(board_t *b, int ar, int ac, int pos) {
	if (pos <= 0)
		return ((ar == 0) || (b->spaces[ar-1][ac].b.f.letter == 0));
	else
		return ((ar == 14) || (b->spaces[ar+1][ac].b.f.letter == 0));
}

/* sun compiler wants all inline functions to have explicit prototypes */
int nlda(board_t *, int, int);

/* no letter directly above */
inline int
nlda(board_t *b, int ar, int ac) {
	return ((ar == 0) || (b->spaces[ar-1][ac].b.f.letter == 0));
}

/* no letter directly below */
inline int
nldb(board_t *b, int ar, int ac) {
	return ((ar == 0) || (b->spaces[ar+1][ac].b.f.letter == 0));
}

/* no letter directly left */
inline int
nldl(board_t *b, int ar, int ac) {
	return ((ac == 0) || (b->spaces[ar][ac-1].b.f.letter == 0));
}

/* no letter directly right */
inline int
nldr(board_t *b, int ar, int ac) {
	return ((ac == 14) || (b->spaces[ar][ac+1].b.f.letter == 0));
}


/* dobridge: in the case where the cross move set falls into a "gap"
 * between played tiles, we have more work to do.  End is -1 for
 * "before" and +1 for "after".  The row,col are the end of the word.
 * We can assume that at least two more squares are past the end.
 * nid corresponds to the letter in the word, NOT the gap.
 */
void
dobridge(board_t *b, int nid, int row, int col, int dir, int end)
{
	int cr=row, cc=col;
	bs_t nbs, cbs, fbs = 0;
	letter_t spl, wl;
	int dc, dr;
	int gid, lid;

	dr = dir * end;
	dc = (1 - dir) * end;

	gid = gc(gaddag[nid]);
	nbs = bitset[gid];
	while ( (spl = nextl(&nbs, &gid)) ) {
		gid = gotol(spl, gid);
		lid = gc(gaddag[gid]);
		cr = row + 2 * dr;
		cc = col + 2 * dc;
		do {
			if (nldn(b, cr, cc, dir, dr+dc) && gf(gaddag[nid])) {
				setbit(fbs, spl-1);
				break;
			}
			wl = b->spaces[cr][cc].b.f.letter;
			if (!(l2b(wl) & bitset[lid])) {
				/* it's not a word. */
				break;
			}
			cr+=dr;cc+=dc;
			lid = gotol(wl,lid);
			lid = gc(gaddag[lid]);
		} while (wl != '\0');
	}
	if (dir == M_HORIZ) {
		b->spaces[row][col].vmbs = fbs;
	} else {
		b->spaces[row][col].hmbs = fbs;
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
int
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


/* update values of empty spaces with new cross letter move scores. */
void
updatemls(board_t *b, int dir, int mr, int mc, int val)
{
	int dr = 0, dc = 0;
	int r, c;
	int under;

	dr = 1 - dir;
	dc = dir;
	if (dir == M_HORIZ) {
		under = b->spaces[mr][mc].b.f.hmls;
	} else {
		under = b->spaces[mr][mc].b.f.vmls;
	}
DBG(DBG_MLS, "update %cmls vals for (%d,%d) with %d+%d\n", dc? 'h':'v', mr, mc, val, under);
	val += under;
	/* you have to have it both ways. */
	r = mr + dr;
	c = mc + dc;
	while (b->spaces[r][c].b.f.letter  && ((r<BOARDY)&&(c<BOARDX))) {
		r += dr; c += dc;
	}
	if ((r<BOARDY && c<BOARDX)) {
		if (dir == M_HORIZ) {
			b->spaces[r][c].b.f.hmls = val;
		} else {
			b->spaces[r][c].b.f.vmls = val;
		}
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
	r = mr - dr;
	c = mc - dc;
	while (b->spaces[r][c].b.f.letter && ((r>=0)&&(c>=0))) {
		r -= dr; c -= dc;
	}
	if ((r>=0)&&(c>=0)) {
		if (dir == M_HORIZ) {
			b->spaces[r][c].b.f.hmls = val;
		} else {
			b->spaces[r][c].b.f.vmls = val;
		}
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
}

/* fold in the last letter used, prepare for new letter */
inline void
updatescore(scthingy_t *sct)
{
DBG(DBG_SCORE, "ttl_ts=%hd ttl_tbs=%hd, ttl_wm=%hd, ttl_xs=%hd, played=%hd, ts=%hd, tbs=%hd, lms=%hd, wm=%hd, play=%hd\n", sct->ttl_ts, sct->ttl_tbs, sct->ttl_wm, sct->ttl_xs, sct->played, sct->ts, sct->tbs, sct->lms, sct->wm, sct->play);
	if (sct->ttl_wm ==0) sct->ttl_wm = 1;
	if (sct->wm == 0) sct->wm = 1;
	sct->ttl_ts += sct->ts;
	sct->ttl_tbs += sct->tbs;
	sct->ttl_wm *= sct->wm;
	if (sct->lms > 0) {
		sct->ttl_xs += sct->wm * (sct->lms + sct->tbs);
	}
	sct->played += sct->play;
	sct->ts = 0; sct->tbs = 0; sct->wm=1; sct->lms = 0; sct->play = 0;
}

/*
 * given a score thingy, tell me what the current score is.
 * called when the final bit is hit.
 */
inline int
finalscore(scthingy_t sct)
{
	int fsc = 0;
	updatescore(&sct);
	/* bingo */
DBG(DBG_SCORE, "ttl_ts=%hd ttl_tbs=%hd, ttl_wm=%hd, ttl_xs=%hd, played=%hd, ts=%hd, tbs=%hd, lms=%hd, wm=%hd, play=%hd\n", sct.ttl_ts, sct.ttl_tbs, sct.ttl_wm, sct.ttl_xs, sct.played, sct.ts, sct.tbs, sct.lms, sct.wm, sct.play);
	if (sct.played >= RACKSIZE) {
		fsc += BINGOBONUS;
	}
	/* cross word scores */
	fsc += sct.ttl_xs;
	/* word score */
	fsc += sct.ttl_tbs * sct.ttl_wm;
	return fsc;
}

/* like makemove, but works BACKWARDS along move. So we can traverse gaddag. */
/* add node tracking. */
int
makemove2(board_t *b, move_t *m, int playthrough)
{
	int cr, cc, dr, dc, ts, i, tts, er, ec;
	space_t *sp;

	dc = 1 - m->dir;
	dr = m->dir;
	er = m->row;
	ec = m->col;
	tts = 0;
	int nid = 0;

	i = strlen(m->tiles);
	if (i == 0) {
		return 0;
	}
	i--;
	if (m->dir == M_HORIZ) {
		ec += i;
	} else {
		er += i;
	}
	cr = er;
	cc = ec;

	/* handle non-playthrough prefix plays */
	if (!playthrough) {
		while ((cr<BOARDY) && (cc<BOARDX)) {
			sp = &(b->spaces[cr][cc]);
			if (sp->b.f.letter != '\0') {
				tts += lval(sp->b.f.letter);
				cr+=dr;cc+=dc;
			} else {
				break;
			}
		}
	}
	for (; ((cr >= m->row)&&(cc >= m->col)); cr-=dr,cc-=dc) {
		ASSERT(((cr>=0)&&(cr<BOARDY)) && ((cc>=0)&&(cc<BOARDX)));
		sp = &(b->spaces[cr][cc]);
		if (sp->b.f.letter != '\0') {
			tts += lval(sp->b.f.letter);
			nid = gotol(sp->b.f.letter, nid);
			nid = gc(gaddag[nid]);
			if (playthrough) {
				if (m->tiles[i] != sp->b.f.letter) {
vprintf(VNORM, "warning: playthrough %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
				}
				i--;
			}
		} else {
			ts = lval(m->tiles[i]);
			tts += ts;
			nid = gotol(m->tiles[i], nid);
			nid = gc(gaddag[nid]);
			updatemls(b, m->dir, cr, cc, ts);
			sp->b.f.letter = m->tiles[i];
			i--;
		}
	}
	/* by now, nid should point to eow in gaddag */
//	ASSERT(gf(gaddag[nid]));  save for later...
	/* do "before" end, if there's a space */
	if (m->dir == M_HORIZ) {
		if (m->col > 0) {
			sp = &(b->spaces[m->row][m->col-1]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under first letter */
			b->spaces[m->row][m->col].b.f.vmls = tts;
			if (!nldl(b, m->row, m->col-1)) {
				/* it's a bridge space */
				dobridge(b, nid, m->row, m->col, m->dir, -1);
				sp->b.f.vmls = tts + b->spaces[m->row][m->col-2].b.f.vmls;
			} else {
				sp->b.f.vmls = tts;
				sp->vmbs = finals(nid);
			}
		}
	} else {
		if (m->row > 0) {
			sp = &(b->spaces[m->row-1][m->col]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under first letter */
			b->spaces[m->row][m->col].b.f.hmls = tts;
			if (!nlda(b, m->row-1, m->col)) {
				/* it's a bridge space */
				dobridge(b, nid, m->row, m->col, m->dir, -1);
				sp->b.f.hmls = tts + b->spaces[m->row-2][m->col].b.f.hmls;
			} else {
				sp->b.f.hmls = tts;
				sp->vmbs = finals(nid);
			}
		}
	}

	/* do "after" end, if there's a space */
	if (m->dir == M_HORIZ) {
		if (ec<MAXC) {
			sp = &(b->spaces[er][ec+1]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under last letter */
			b->spaces[er][ec].b.f.vmls = tts;
			if (!nldr(b, er, ec+1)) {
				/* it's a bridge space */
				dobridge(b, nid, er, ec, m->dir, +1);
				sp->b.f.vmls = tts + b->spaces[er][ec+2].b.f.vmls;
			} else {
				sp->b.f.vmls = tts;
			}
		}
	} else {
		if (er<=MAXR) {
			sp = &(b->spaces[er+1][ec]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under last letter */
			b->spaces[er][ec].b.f.hmls = tts;
			if (!nldb(b, er+1, ec)) {
				/* it's a bridge space */
				dobridge(b, nid, er, ec, m->dir, +1);
				sp->b.f.hmls = tts + b->spaces[er+2][ec].b.f.hmls;
			} else {
				sp->b.f.hmls = tts;
			}
		}
	}
	return 1;
}

/*
 * makemove: place move m on board b. If playthrough then match
 * tiles in move to those already on board.  Calculates mls along the
 * way, but does not do scoring.  Returns number of letters placed,
 * 0 if null move, or < 0 if error.
 */
int
makemove(board_t *b, move_t *m, int playthrough)
{
	int cr, cc, dr, dc, ts, i, tts;
	space_t *sp;

	dc = 1 - m->dir;
	dr = m->dir;
	cr = m->row;
	cc = m->col;
	tts = 0;

	if (strlen(m->tiles) == 0) {
		return 0;
	}
	/* make sure we are really at the start */
	for (i=0; m->tiles[i] != '\0'; cr+=dr,cc+=dc) {
		ASSERT(((cr>=0)&&(cr<BOARDY)) && ((cc>=0)&&(cc<BOARDX)));
		sp = &(b->spaces[cr][cc]);
		if (sp->b.f.letter != '\0') {
			tts += lval(sp->b.f.letter);
			if (playthrough) {
				if (m->tiles[i] != sp->b.f.letter) {
vprintf(VNORM, "warning: playthrough %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
				}
				i++;
			}
		} else {
			ts = lval(m->tiles[i]);
			tts += ts;
			updatemls(b, m->dir, cr, cc, ts);
			sp->b.f.letter = m->tiles[i];
			i++;
		}
	}
	/* handle non-playthrough prefix plays */
	if (!playthrough) {
		while ((cr<BOARDY) && (cc<BOARDX)) {
			sp = &(b->spaces[cr][cc]);
			if (sp->b.f.letter != '\0') {
				tts += lval(sp->b.f.letter);
				cr+=dr;cc+=dc;
			} else {
				break;
			}
		}
	}
	/* do "before" end, if there's a space */
	if (m->dir == M_HORIZ) {
		if (m->col > 0) {
			sp = &(b->spaces[m->row][m->col-1]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under first letter */
			b->spaces[m->row][m->col].b.f.vmls = tts;
			if (!nldl(b, m->row, m->col-1)) {
				/* it's a bridge space */
				sp->b.f.vmls = tts + b->spaces[m->row][m->col-2].b.f.vmls;
			} else {
				sp->b.f.vmls = tts;
			}
		}
	} else {
		if (m->row > 0) {
			sp = &(b->spaces[m->row-1][m->col]);
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under first letter */
			b->spaces[m->row][m->col].b.f.hmls = tts;
			if (!nldb(b, m->row-1, m->col)) {
				/* it's a bridge space */
				sp->b.f.hmls = tts + b->spaces[m->row-2][m->col].b.f.hmls;
			} else {
				sp->b.f.hmls = tts;
			}
		}
	}
	/* do "after" end, if there's a space */
	sp = &(b->spaces[cr][cc]);
	if (m->dir == M_HORIZ) {
		if (cc<=MAXC) {
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under last letter */
			b->spaces[cr][cc-1].b.f.vmls = tts;
			if (!nldr(b, cr, cc)) {
				/* it's a bridge space */
				sp->b.f.vmls = tts + b->spaces[cr][cc+1].b.f.vmls;
			} else {
				sp->b.f.vmls = tts;
			}
		}
	} else {
		if (cr<=MAXR) {
			ASSERT(sp->b.f.letter == '\0');
			/* stash sum under last letter */
			b->spaces[cr-1][cc].b.f.hmls = tts;
			if (!nlda(b, cr, cc)) {
				/* it's a bridge space */
				sp->b.f.hmls = tts + b->spaces[cr+1][cc].b.f.hmls;
			} else {
				sp->b.f.hmls = tts;
			}
		}
	}
}

/*
 * return the value of placing move m on board b.   If doit is set,
 * actually place the tiles, otherise we are just looking.
 * playthrough is for moves that include tiles already on board.
 */
/* I believe this routine misses some cases.
 * yup, it's broken.
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

	deltav = 1 - m->dir;
	deltah = m->dir;
	ortho = 1 - m->dir;
	if (m->dir == M_HORIZ) {
		ends = b->spaces[m->row][m->col].b.f.vmls;
DBG(DBG_SCORE, "get H beginning end score %d at (%d, %d)\n", ends, m->row, m->col);
	} else {
		ends = b->spaces[m->row][m->col].b.f.hmls;
DBG(DBG_SCORE, "get V beginning end score %d at (%d, %d)\n", ends, m->row, m->col);
	};
DBG(DBG_SCORE, "moving %d so deltah=%d and deltav=%d\n", m->dir, deltah, deltav);

	if (m->lcount >= RACKSIZE) bingo = BINGOBONUS;

	for (i=0, r=m->row, c=m->col; i < m->lcount; r += deltah, c += deltav) {
		sp = &(b->spaces[r][c]);
		if (sp->b.f.letter == EMPTY) {
DBG(DBG_SCORE, "placing %dth out of %d %c(%d) at (%d,%d)\n", i, m->lcount, l2c(m->tiles[i]), m->tiles[i], r, c);
DBG(DBG_SCORE, "on space (%d,%d) lm=%d wm=%d\n",r,c, sp->b.f.lm, sp->b.f.wm);
			mult *= sp->b.f.wm;	// word multiplier
			ts = lval(m->tiles[i]);	// ts = tile score
			tts += ts;		// total ts
			tbs = ts * sp->b.f.lm;	// tile bonus score
			ssf += ts;		// add current tile
			if ((m->dir == M_HORIZ) && sp->b.f.hmls) {
DBG(DBG_SCORE, "horiz move (%d + %d) * %d \n", sp->b.f.hmls, tbs, sp->b.f.wm);
				xssf += (sp->b.f.hmls + tbs) * sp->b.f.wm;
			}
			if ((m->dir == M_VERT) && sp->b.f.vmls) {
DBG(DBG_SCORE, "vert move (%d + %d) * %d \n", sp->b.f.vmls, tbs, sp->b.f.wm);
				xssf += (sp->b.f.vmls + tbs) * sp->b.f.wm;
			}
DBG(DBG_SCORE, "tile %c scores: ts=%d, tbs=%d, ssf=%d, xssf=%d\n", l2c(m->tiles[i]), ts, tbs, ssf, xssf);
			if (doit) {
				sp->b.f.letter = m->tiles[i];
				/* update mls stuff. Not easy. */
				updatemls(b, m->dir, r, c, ts);
			}
			i++;	 // next letter please
		} else {
			if (playthrough) {
				if (m->tiles[i] != sp->b.f.letter) {
vprintf(VNORM, "warning: playthrough %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
				}
				i++;	// I'm not sure about this....
			}
			ts = lval(sp->b.f.letter); // ts = tile score
			tts += ts;		// total ts
			ssf += ts;		// add current tile
		}
	}
	if (m->dir == M_HORIZ) {
		ends += b->spaces[r][c-1].b.f.vmls;
DBG(DBG_SCORE, "get H ending end score %d at (%d, %d)\n", ends, r, c);
		deltav = 1;
		ortho = M_VERT;
	} else {
		ends += b->spaces[r-1][c].b.f.hmls;
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
				if (sp->b.f.letter == EMPTY) {
					printf(" _  ");
				} else {
					printf(" %c  ", l2c(sp->b.f.letter));
				}
				break;
			case B_VMLS:
				if (sp->b.f.vmls)
					printf("^%-2d ", sp->b.f.vmls);
				else if (sp->b.f.letter != EMPTY)
					printf(" %c  ", l2c(sp->b.f.letter));
				else
					printf("    ");
				break;
			case B_HMLS:
				if (sp->b.f.hmls)
					printf(">%-2d ", sp->b.f.hmls);
				else if (sp->b.f.letter != EMPTY)
					printf(" %c  ", l2c(sp->b.f.letter));
				else
					printf("    ");
				break;
			case B_BONUS:
				bl = sp->b.f.lm -1 ? sp->b.f.lm-1 : 0;
				bl = sp->b.f.wm -1 ? sp->b.f.wm+1 : bl;
				printf(" %s ", bonusnames[bl]);
			}
		}
		printf("\n");
	}
	printf("\n");
}

/* read a move in "std" notation. rv of 0 is success.
 * Played is passed to c2lstr, see comments there for values.
 */
int
parsemove(char *str, move_t *m, int played)
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
		if (plen == 0) return 3;
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
			m->col = (str[0] - 'A');
			m->row = str[1] - '0';
			if (plen == 3) {
				m->row = m->row*10 + (str[2] - '0');
			}
		} else if (isdigit(str[0]) && isupper(str[plen-1])) {
			m->dir = M_HORIZ;
			m->col = (str[plen-1] - 'A');
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

	if ((m->row < 0) || (m->row >= BOARDY) ||
	    (m->col < 0) || (m->col >= BOARDX)) {
		return 4;
	}

	if ((m->dir == M_HORIZ) && ((len + m->col) > BOARDX)) {
		vprintf(VVERB, "Word of len %d at %d goes off board\n", len, m->col);
		return 4;
	}
	if ((m->dir == M_VERT) && ((len + m->row) > BOARDY)) {
		vprintf(VVERB, "Word of len %d at %d goes off board\n", len, m->row);
		return 4;
	}

	if (len > BOARDSIZE) {
		vprintf(VVERB, "Word %s of len %d too long\n", str, len);
		return 4;
	}
	m->lcount = len;
	/* now the string. */
	if (c2lstr(cp, m->tiles, played)) {
		vprintf(VVERB, "%s had invalid characters\n", cp, len);
		return 5;
	}
	return 0;
}


void
printmove(move_t *m, int rev)
{
	if (m->dir == M_HORIZ) {
		printf("%d%c:", m->row+1, coltags[m->col]);
	} else {
		printf("%c%d:", coltags[m->col], m->row+1);
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
/* GoOn with inline Gen. Still recursive. */
/* initial call with pos=0, nodeid=0, and m->tiles empty. */
/* do vertical moves as well. */
int
GoOn2(board_t *b, move_t *m, int pos, rack_t *r,  int nodeid, scthingy_t sct)
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
	int currow = ar;
	char *rlp = (char *)1;
	bs_t rbs = 0;
	bs_t bl = 0;
	bs_t bs = 0;
	register letter_t pl;
	int room = 0;

DBG(DBG_GOON, "at %d,%d(%-d) node=%d", ar,ac,pos, nodeid) {
	printf(" - word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	updatescore(&sct);
	ndx = strlen(w);	/* depth */
	if (pos > 0) {
		prelen = pos;
		if (m->dir == M_HORIZ) {
			curcol += ndx;
		} else {
			currow += ndx;
		}
	} else {
		prelen = ndx + 1;
	}
	w[ndx+1] = '\0';

	while (rlp != NULL) {
DBG(DBG_GOON, "inline gen rbs=%x, bl=%d, bs=%x, curid=%d, rlp=%p lp=%c\n", rbs, bl,  bs, curid, rlp, l2c(w[ndx])) {

}
		pl = b->spaces[currow][curcol].b.f.letter;
		if (pl != '\0') {
DBG(DBG_GEN, "found %c on board at %d, %d\n", l2c(pl), currow, curcol);
			w[ndx] = pl;
			rlp = NULL;
			curid = gotol(deblank(w[ndx]), nodeid);
//			curid = nodeid + popc(bitset[nodeid] << (32 - deblank(w[ndx])))-1;
			sct.ts = lval(pl);
			sct.tbs = b->spaces[currow][curcol].b.f.lm * sct.ts;
			sct.wm = b->spaces[currow][curcol].b.f.wm;
			sct.play = 0;
			if (m->dir == M_HORIZ) {
				sct.lms = b->spaces[currow][curcol].b.f.hmls;
			} else {
				sct.lms = b->spaces[currow][curcol].b.f.vmls;
			}
		} else {
			if (curid == -1) {
				rbs = lstr2bs(r->tiles);
				if (rbs & UBLBIT) bl = BB;
				curid = nodeid;
				if (bl) bs = ALLPHABITS & bitset[nodeid];
				else bs = rbs & bitset[nodeid];
DBG(DBG_GOON, "first bl=%x, rbs=%x, id=%d, bs=%x\n", bl, rbs, nodeid, bs);
			} else {
				if (bl) *rlp = UBLANK;
				else *rlp = w[ndx];
DBG(DBG_GOON, "Pop %c at %d back to\n", l2c(w[ndx]), ndx);
			}
			if ((bs == 0) && (bl)) {
				bl = 0;
				bs = rbs & bitset[nodeid];
				curid = nodeid;
			}
			if (bs == 0) {
				rlp = NULL;
				w[ndx] = '\0';
				break;
			} else {
				pl = nextl(&bs, &curid);
				ASSERT(pl != 0);
DBG(DBG_GOON,"match %c bl=%x, node %d rack=", l2c(pl),bl, nodeid) {
	printlstr(r->tiles); printf("\n");
}
				if (bl) rlp = strchr(r->tiles, UBLANK);
				else rlp = strchr(r->tiles, pl);
				ASSERT(rlp != NULL);
				*rlp = MARK;
				pl |= bl;
				w[ndx] = pl;
				sct.ts = lval(pl);
				sct.tbs = b->spaces[currow][curcol].b.f.lm * sct.ts;
				sct.wm =  b->spaces[currow][curcol].b.f.wm;
				if (m->dir == M_HORIZ) {
					sct.lms = b->spaces[currow][curcol].b.f.hmls;
				} else {
					sct.lms = b->spaces[currow][curcol].b.f.vmls;
				}
				sct.play = 1;
			}
		}
DBG(DBG_GOON, "Gen gave i=%d, id=%d, l=%c and rack ", i, curid, l2c(w[ndx])) {
	printlstr(r->tiles); printf("\n");
}
		if (gf(gaddag[curid])) {
			if (m->dir == M_HORIZ) {
				room = nldh(b, currow, curcol, pos);
			} else {
				room = nldv(b, currow, curcol, pos);
			}
			if (room) {
				if (doscore) {
					m->score = finalscore(sct);
				}
				VERB(VNORM, "") {
					printmove(m, pos);
				}
				movecnt++;
			}
		}
		cid = gc(gaddag[curid]);
		if (m->dir == M_HORIZ) {
			room = (((pos <= 0) && (curcol > 0))  || ((pos > 0) && (curcol < 14)));
		} else {
			room = (((pos <= 0) && (currow > 0))  || ((pos > 0) && (currow < 14)));
		}
		if (room) {
			/* recurse */
DBG(DBG_GOON, "recurse 1 (%d, %d, %d, word, rack, id=%d)", m->row, m->col, pos, cid) {
	printf(" word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
			if (pos <= 0) {
				m->col -= 1 - m->dir;
				m->row -= m->dir;
			}
			movecnt += GoOn2(b, m, pos, r,  cid, sct);
			if (pos <= 0) {
				m->col += 1 - m->dir;
				m->row += m->dir;
			}
		}
		/* have to handle the ^ */
		if ((pos <= 0) && (SEPBIT & bitset[cid])) {
			if (m->dir == M_HORIZ) {
				room = nldl(b, currow, curcol) && (curcol < 14);
			} else {
				room = nlda(b, currow, curcol) && (currow < 14);
			}
			if (room) {
				sepid = gotol(SEP, cid);
//				sepid = cid + popc(bitset[cid] << (32 - SEP))-1;
DBG(DBG_GOON, "sep at %d from %d\n", sepid, cid);
				cid = gc(gaddag[sepid]);
DBG(DBG_GOON, "recurse 3 (%d, %d, 1, word, rack, id=%d", m->row, m->col, cid) {
	printf(" - word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
				movecnt += GoOn2(b, m, prelen, r, cid, sct);
			}
		}
	}

	DBG(DBG_GOON, "made %d moves at level %d\n", movecnt, ndx);
	return movecnt;
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
	/* test parsemove */
	{
		move_t tm; int rv; char s[28]="";

		strcpy(s, "H8:ABCDEFG"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0) && (tm.dir == M_VERT) && (tm.col == 7) && (tm.row == 7));
		strcpy(s, "8H:ABCDEFG"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0) && (tm.dir == M_HORIZ) && (tm.col == 7) && (tm.row == 7));
		strcpy(s, "1A:ABCDEFG"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0) && (tm.dir == M_HORIZ) && (tm.col == 0) && (tm.row == 0));
		strcpy(s, "O15:A"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0) && (tm.dir == M_VERT) && (tm.col == 14) && (tm.row == 14));
		strcpy(s, "A1:ABCDEFGHIJKLMNOPQRST"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "15O:AB"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "16A:AB"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "0A:AB"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "P1:AB"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "@1:AB"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "H8:ABBB?C?"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0));
		rv = parsemove(s, &tm, 1);

		ASSERT( (rv!=0));
		strcpy(s, "H8:ABBBxC?"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "H8:ABBBCC^"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0));
		strcpy(s, "H8:ABBBCC\\"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "H8:"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv==0));
		strcpy(s, ""); tm=emptymove;
		rv = parsemove(s, &tm, 0);

		ASSERT( (rv!=0));
		strcpy(s, ""); tm=emptymove;
		rv = parsemove(NULL, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, "foobar:&"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
		ASSERT( (rv!=0));
		strcpy(s, ":FUBAR"); tm=emptymove;
		rv = parsemove(s, &tm, 0);
VERB(VNOISY, "verify parsemove: rv=%d, dir=%d, row=%d col=%d lcount=%d tiles=", rv, tm.dir, tm.row, tm.col, tm.lcount) {
printlstr(tm.tiles); printf("\n");
}
		ASSERT( (rv!=0));
	}
	{
		/* finals. */
		int nid; int bs;

		nid =0; bs = 0;
		bs = finals(nid);
vprintf(VNOISY, "finals for node %d are %x\n", nid, bs);
		ASSERT(bs == 0);
		nid =125; bs = 0;
		bs = finals(nid);
vprintf(VNOISY, "finals for node %d are %x\n", nid, bs);
		ASSERT(bs == 1);
	}
	{
		/* nldn */
		board_t tb; int r; int c; int d; int s;
		int rv;
		tb = emptyboard;
		tb.spaces[7][7].b.f.letter = c2l('A');

		r = 7; c = 7; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 7; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 7; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 7; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 0; c = 0; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 0; c = 0; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 0; c = 0; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 0; c = 0; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 14; c = 14; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 14; c = 14; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 14; c = 14; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 14; c = 14; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 6; c = 7; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 6; c = 7; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 6; c = 7; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 6; c = 7; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 8; c = 7; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 8; c = 7; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 8; c = 7; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 8; c = 7; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 7; c = 6; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 6; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 6; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 6; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);

		r = 7; c = 8; d = M_HORIZ; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 8; d = M_VERT; s = 1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 8; d = M_VERT; s = -1;
		rv = nldn(&tb, r, c, d, s);
		ASSERT(rv == 1);
		r = 7; c = 8; d = M_HORIZ; s = -1;
		rv = nldn(&tb, r, c, d, s);
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
		rv = parsemove(argv[optind], &argmove, JUSTPLAY);

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
//			sc = score(&argmove, &sb, action&ACT_MOVE, action&ACT_PLAYTHRU);
			sc = score(&argmove, &sb, 0, action&ACT_PLAYTHRU);
			vprintf(VNORM, "%s scores %d\n", argv[optind], sc);
			if (action&ACT_MOVE) {
makemove2(&sb, &argmove, 1);
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
			moves = GoOn2(&sb, &argmove, 0, &r, 0, newsct);
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

	//return 0;	// fall-through catch-all. not reached
}
