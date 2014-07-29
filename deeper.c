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
#include <unistd.h>	// getopt, seek
#include <ctype.h>	// isupper, etc
#include <limits.h>	// LONG_MAX
#include <errno.h>	// errno

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

void printmove(move_t *m, int rev);
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
gstats_t nullstats = { 0,0,0,0,0,0,0};	// all 0s
position_t startp;
static const scthingy_t newsct = { 0, 0, 1, 0, 0, 0, 0, 0, 1, 0 };

/* diag, debug and stats */
int verbose = 0;		// level of info output
unsigned long dflags = 0;	// for DBG statements
int stats = 0;			// report stats while running
char *gcgfn = NULL;		// save result here
gstats_t globalstats;		// global statistics
unsigned long gmcnt = 0;	// global mv counter.

/* other options */
int doscore = 0;	// report scores as well
int dotimes = 0;	// set if we should time ourselves.
int level = 0;		// degree of strategy strength
char *infile = 0;	// move input file.
int strat = 0;		// move choosing strategy.
int dostats = 0;	// how much stat info to report.

/* job/process control */
int dtrap = 0;			// debugger trap counter
int globaldone = 0;		// set to stop all threads.

void
usage(char *me)
{
	vprintf(VNORM, "%s [-LASMG] [-P] [-I file] [move...]\n", me);

	vprintf(VVERB,
	"\t-L: lookup moves in dictionary\n"
	"\t-A: print all anagrams of moves\n"
	"\t-S: score moves as if played on board\n"
	"\t-M: make each move on board, show results\n"
	"\t-G: generate list of possible moves using move\n"
	"\t-P: set playthru mode for moves\n"
	"\t-I file: read moves from input file\n");

	vprintf(VNORM, "%s -T n [-n lvl] [-b bag] [-B str]\n", me);
	vprintf(VVERB,
	"\t-T n: use strategy number n to play game\n"
	"\t-n lvl: for progressive strats, use level lvl\n"
	"\t-b [?]A-Z|name: Set bag name. A-Z are built-in, ?=randomize.\n"
	"\t-B str: set bag to string of tiles (A-Z or ? for blank.\n");
	vprintf(VNORM, "    [-D bits|word] [-vqts] [-d dict]\n");
	vprintf(VVERB,
	"\t-D bits|word turn on specified debug flags\n"
	"\t-v: increase verbosity level, cumulative\n"
	"\t-q: no messages, only return values. Cancels -v.\n"
	"\t-t: time and report operations\n"
	"\t-s: collect and report statistics. Use twice for more.\n"
	"\t-d name: use name.gaddag as dictionary. [default=ENABLE]\n");
	vprintf(VNORM, "    [-o file] [-R str]\n");
	vprintf(VVERB,
	"\t-o name: save best move to name.gcg\n"
	"\t-R str: set rack to string of tiles (A-Z or ? for blank.)\n");
	vprintf(VVERB,
	"\t move = rc:word or cr:word, r=1-15, c=A-O, word is 1-15 letters.\n"
	"\t        If rc is omitted, uses starting position of 8H.\n"
	"\t        Put row (number) first for horizontal moves. Use lowercase\n"
	"\t        letter for blank played, '?' for unplayed blank.\n");
}

/* TODO: test which one is faster. */
inline bs_t
lstr2bs(letter_t *lstr)
{
	int i = 0;
	bs_t bs = 0;
#ifdef NOTDEF
	while (lstr[i] != '\0') {
		setbit(&bs, lstr[i]-1);
		i++;
	}
#else
	for (i=0; lstr[i] != '\0'; i++) {
		setbit(&bs, lstr[i]-1);
	}
#endif
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
l2cstr(const char *lstr, char *cstr)
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
	(void)clock_gettime(CLOCK_REALTIME, &ts);
	return ((uint64_t)ts.tv_sec * 1000000000LU + (uint64_t)ts.tv_nsec);
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
	ASSERT(len < GDSIZE);
#if defined(__sun)
#define MMFLAGS	MAP_SHARED | MAP_ALIGN
	gaddag = (gn_t *)mmap((void *)GDSIZE, GDSIZE, PROT_READ, MMFLAGS, dfd, 0);
#else
// #define MMFLAGS	MAP_SHARED | MAP_HUGETLB | MAP_LOCKED | MAP_POPULATE
// #define MMFLAGS	MAP_SHARED | MAP_LOCKED | MAP_POPULATE
//#define MMFLAGS	MAP_SHARED | MAP_LOCKED
//#define MMFLAGS	MAP_SHARED | MAP_HUGETLB
#define MMFLAGS	MAP_SHARED
	gaddag = (gn_t *)mmap(0, GDSIZE, PROT_READ, MMFLAGS, dfd, 0);
#endif
	if (gaddag == MAP_FAILED) {
		VERB(VNORM, "failed to mmap %d bytes of gaddag\n", len) {
			perror("mmap");
		}
		return -4;
	}
#if defined(__sun)
	{
		struct memcntl_mha mha;
		int rv;

		mha.mha_cmd = MHA_MAPSIZE_VA;
		mha.mha_flags = 0;
		mha.mha_pagesize = GDSIZE;
		rv = memcntl((caddr_t)gaddag, GDSIZE, MC_HAT_ADVISE, (char *)&mha, 0, 0);
		if (rv != 0) {
			VERB(VVERB, "failed to set gaddag pagesize to %lu\n", GDSIZE){
				perror("memcntl");
			}
		}
	}
#endif	/* __sun */

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
	ASSERT(len < GDSIZE);
#if defined(__sun)
	bitset = (bs_t *)mmap((void *)GDSIZE, GDSIZE, PROT_READ, MMFLAGS, bsfd, 0);
#else
	bitset = (bs_t *)mmap(0, GDSIZE, PROT_READ, MAP_SHARED, bsfd, 0);
#endif
	if (bitset == MAP_FAILED) {
		VERB(VNORM, "failed to mmap %d bytes of bitset\n", len) {
			perror("mmap");
		}
		return -4;
	}
#if defined(__sun)
	{
		struct memcntl_mha mha;
		int rv;

		mha.mha_cmd = MHA_MAPSIZE_VA;
		mha.mha_flags = 0;
		mha.mha_pagesize = GDSIZE;
		rv = memcntl((caddr_t)bitset, GDSIZE, MC_HAT_ADVISE, (char *)&mha, 0, 0);
		if (rv != 0) {
			VERB(VVERB, "failed to set bitset pagesize to %lu\n", GDSIZE){
				perror("memcntl");
			}
		}
	}
#endif

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
printlstr(const letter_t *lstr) {
	char cstr[20] = "";
	int rv;

	rv = l2cstr(lstr, cstr);
	printf("%s", cstr);
}

/*
 * fill rack: take letters from bag and put them in the rack.
 * copy over null and marked slots. Only take up to 7. Don't
 * go past end of bag. Return number of tiles put on rack.
 */
int
fillrack(rack_t *r, bag_t b, int *bagpos)
{
	int i, cnt = 0;
	if (*bagpos >= baglen) {
		return 0;
	}

	for (i=0; i < 7; i++) {
		if ((r->tiles[i] == '\0') || (r->tiles[i] == MARK)) {
			r->tiles[i] = b[*bagpos];
			*bagpos += 1; cnt++;
		}
		if (*bagpos >= baglen) {
			break;
		}
	}
DBG(DBG_RACK, "bag now at %d, filled %d tiles to make ", *bagpos, cnt) {
	printlstr(r->tiles); printf("\n");
}
	return cnt;
}

/*
 * rack handling, combined operation.
 * copy letters from oldr to newr, except for L. re-create rbs
 * along the way.
 * ORDER IS IMPORTANT: assume oldr is sorted, and keep newr the same way.
 */
inline void
rackem(rack_t const *oldr, rack_t *newr, bs_t *rbs, letter_t L)
{
	letter_t const *op = oldr->tiles;
	letter_t *np = newr->tiles;
	*rbs = 0;

	while (*op != '\0') {
		if (*op != L) {
			*np = *op;
			setbit(rbs, *op - 1);
			np++;
		} else {
			L = '\0';		// don't remove it twice
		}
		op++;
	}
	*np = '\0';
}

/* remove a letter from the rack, mainstain bitset. */
char *
pluckrack2(rack_t *r, letter_t l, bs_t *bs)
{
	char *lp;

	if (r == NULL) return NULL;
	if (is_pblank(l)) l = UBLANK;
	lp = strchr(r->tiles, l);
	if (lp != NULL) {
		*lp = MARK;
	} else {
		VERB(VVERB, "Missing letter %c from rack ", l2c(l)) {
			printlstr(r->tiles); printf("\n");
		}
	}
	VERB(VNOISY, "Plucked2 rack now ") {
		printlstr(r->tiles); printf("\n");
	}
	if (strchr(r->tiles, l) == NULL) {
		clrbit(bs, l-1);
	}
	return lp;
}

/* remove a letter from the rack */
char *
pluckrack(rack_t *r, letter_t l)
{
	char *lp;

	if (r == NULL) return NULL;
	if (is_pblank(l)) l = UBLANK;
	lp = strchr(r->tiles, l);
	if (lp != NULL) {
		*lp = MARK;
	} else {
		VERB(VVERB, "Missing letter %c from rack  ", l2c(l)) {
			printlstr(r->tiles); printf("\n");
		}
	}
	VERB(VNOISY, "Plucked rack now ") {
		printlstr(r->tiles); printf("\n");
	}
	return lp;
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
	baglen = strlen(bagstr);
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
			emptyboard.spaces[r][c].mbs[0] = 0;
			emptyboard.spaces[r][c].mbs[1] = 0;
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
	startboard.spaces[STARTR][STARTC].b.f.anchor = 2;
	startboard.spaces[STARTR][STARTC].mbs[M_HORIZ] = ALLPHABITS;
	startboard.spaces[STARTR][STARTC].mbs[M_VERT] = ALLPHABITS;
	// init stats
	globalstats.evals = 0;
	globalstats.evtime = 0;
	globalstats.maxdepth = 0;
	globalstats.maxwidth = 0;
	globalstats.wordhs = 0;
	globalstats.gamehs = 0;

	/* make up our starting position. */
	startp.b = startboard;
	startp.sc = 0;
	startp.bagndx = 0;
	startp.r = emptyrack;
	startp.m = emptymove;
	startp.prev = NULL;
	startp.next = NULL;
	startp.state = START;
	startp.stats = nullstats;
	startp.mvcnt = 0;
	startp.mvndx = -1;

	if (rackstr != NULL) {
		if (strlen(rackstr) > 7) {
			vprintf(VNORM, "rack can only have up to 7 letters.\n");
			return 1;
		}
		if (casec2lstr(rackstr, startp.r.tiles) != 0) {
			vprintf(VNORM, "rack string has invalid characters.\n"
			    "Use only letters and '?' for blank\n");
			return 1;
		}
		DBG(DBG_RACK, "starting with a rack of:") {
			printlstr(startp.r.tiles); printf("\n");
		}
	}
	return 0;
}

/* used in call to qsort() */
inline int
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
 * we can assume that the bit for l is set. (Maybe not).
 * NOTE: can't optimize by assuming uint32_t << 32 == 0.  it's not.
 * BUG: SPARC gcc optimization messes this up.
 */
inline int
gotol(letter_t l, int nid)
{
	uint32_t bits;

	bits = bitset[nid] << (32 -l);
	return nid + popc(bits) - 1;
//	return nid + popc(bitset[nid] << (32-l)) -1;
}

/* return the next letter, and fix up bs */
inline letter_t
nextl(bs_t *bs, int *curid)
{
	letter_t l;
	uint32_t idbs = bitset[*curid];

	l = ffb(*bs);
	if (l==0) return 0;
	*curid += popc( (uint32_t)(idbs<<((uint32_t)(32-l))) )-1;
	clrbit(bs, l-1);
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
	bs_t nbs;
	int newid;

	if (nid < 0) return bs;		/* just in case */
	nbs = bitset[nid];
	l = nextl(&nbs, &nid);
	while (l != '\0') {
		if (gf(gaddag[nid])) {
			setbit(&bs, l-1);
		}
		l = nextl(&nbs, &nid);
	}
	return bs;
}

/* isroom: given dir and side, is there room over there? */
/* don't be too clever. We can assume current r,c are in bounds.*/
inline int
isroom(int r, int c, int dir, int side)
{
// printf("isroom %d,%d, dir=%d, side=%d\n", r, c, dir, side);
	if (dir == M_HORIZ) {
		if (((side < 0) && (c > 0)) || ((side > 0) && (c < 14)))
			return 1;
	} else {
		if (((side < 0) && (r > 0)) || ((side > 0) && (r < 14)))
			return 1;
	}
	return 0;
}

/* ultimate nld: nldn. No letter directly next to.
 * returns 0 iff the NEXT space is NOT a played tile. Could be empty or
 * at the edge of the board.
 * dir is H(0) or V(1), side is -1(before) or 1(after).
 */
inline int
nldn(board_t *b, int r, int c, int dir, int side)
{
	int dr = dir * side;
	int dc = (1 - dir) * side;
	int ve = (c-7)/7;
	int he = (r-7)/7;

	return (( (dr&&(dr==he))  || (dc&&(dc==ve)) )||(b->spaces[r+dr][c+dc].b.f.letter == 0));
}

/* next space empty. returns a 1 IFF the NEXT space is on the board and
 * does not have a tile played on it.
 */
inline int
nse(board_t *b, int r, int c, int dir, int side)
{
	int dr = dir * side;
	int dc = (1 - dir) * side;

	if (isroom(r,c,dir,side)) {
		return (b->spaces[r+dr][c+dc].b.f.letter == 0);
	}
}


/* sublime: next door neighbor. Takes board, position, dir, side,
 * Returns: <0 if off of board
 *	     0 if empty space
 *	     l(>0) if space contains a letter (sp.b.f.letter)
 * clever bits: (x-7)/8 is 0 iff 0<=X<=14. To test the current space,
 * set side to 0.
 */
int
ndn(board_t *b, int r, int c, const int dir, const int side)
{
	r += dir*side; c += (1-dir)*side;

	if (!(((c-7)/8) + ((r-7)/8))) {
		return b->spaces[r][c].b.f.letter;
	}
	return -1;
}

/* goes with mm8. */
bs_t
dobridge2(board_t *b, int nid, int row, int col, int dir, int end)
{
	int cr, cc;
	space_t *sp;
	bs_t gbs = 0;
	bs_t bs;
	letter_t gl;
	letter_t nl;
	int dr, dc;
	int curid = nid;
	int gid, gcid;

	sp = &(b->spaces[cr][cc]);
	ASSERT(sp->b.f.letter == '\0');
	dr = end * dir;
	dc = end * (1 - dir);

	bs = bitset[nid];
	/* prune with other side of gap. */
	bs &= b->spaces[cr + dr][cc+dc].mnid[dir];
	if (bs == 0) return 0;
	while (gl = nextl(&bs, &curid)) {
		gid = gotol(gl, curid);
		gcid = gc(gaddag[gid]);
		while ( (nl = ndn(b, cr, cc, dir, end)) > 0) {
			if (l2b(nl) & bitset[gcid]) {
				gid = gotol(gl, gcid);
				gcid = gc(gaddag[gid]);
				if (gid <= 0) break;
				cr += dr; cc += dc;
			} else {
				break;
			}
		}
		if ((nl == 0) && (gf(gaddag[gid]))) {
			gbs |= l2b(nl);
		}
	}
	return gbs;
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
	bs_t nbs, cbs;
	bs_t fbs = 0;
	letter_t spl, wl;
	int dc, dr;
	int gid, lid;

	ASSERT(b->spaces[cr][cc].b.f.letter != '\0');
	dr = dir * end;
	dc = (1 - dir) * end;

	if (nid <= 0) {
		b->spaces[row+dr][col+dc].mbs[1-dir] = 0;
		return;
	}
//	gid = gc(gaddag[nid]);
	gid = nid;
	nbs = bitset[gid];
	while (spl = nextl(&nbs, &gid)) {
		gid = gotol(spl, gid);
		lid = gc(gaddag[gid]);
		if (lid <= 0)  {
			continue;
		}
		cr = row + 2* dr;
		cc = col + 2* dc;
		while ((wl = b->spaces[cr][cc].b.f.letter) != '\0') {
			ASSERT(wl != '\0');
			if ((!(l2b(wl) & bitset[lid])) || (lid <= 0)) {
				/* it's not a word. */
				break;
			}
			if (nldn(b, cr, cc, dir, dr+dc) && gf(gaddag[gid])) {
				setbit(&fbs, spl - 1);
				break;
			}
			cr+=dr;cc+=dc;
			lid = gotol(wl,lid);
			lid = gc(gaddag[lid]);
		}
	}
	b->spaces[row+dr][col+dc].mbs[1-dir] = fbs;
}

/* anagram using bitset. */
int
doanagram_e(uint32_t nodeid, letter_t *sofar, int depth, letter_t *rest)
{
	int anas = 0;
	int curid = -1;
	bs_t bs = 0;
	bs_t lbs;
	letter_t l;
	letter_t *lp;

	DBG(DBG_ANA, "doing anagram lvl %d", depth) {
		printnode(" with", nodeid);
	}
	lbs = lstr2bs(rest);

	curid = nodeid;
	bs = bitset[nodeid] & lbs;
	while (l = nextl(&bs, &curid)) {
DBG(DBG_ANA, "matched %c from ", l2c(l)) {
		printlstr(rest);
		printnode(" using", curid);
}
		sofar[depth] = l;
		/* remove l from rest. */
		lp = strchr(rest, l);
		*lp = MARK;
		if (gf(gaddag[curid])) {
			anas++;
			VERB(VNORM, " ") {
				printlrstr(sofar); printf("\n");
			}
		}
		anas += doanagram_e(gc(gaddag[curid]), sofar, depth+1, rest);
		*lp = l;
	}
	/* if there is a '?', do another round. */
	if (lbs & UBLBIT) {
		curid = nodeid;
		bs = ALLPHABITS & bitset[nodeid];
		lp = strchr(rest, UBLANK);
		*lp = MARK;
		while (l = nextl(&bs, &curid)) {
DBG(DBG_ANA, "blank %c from ", l2c(l|BB)) {
		printlstr(rest);
		printnode(" using", curid);
}
			sofar[depth] = l|BB;
			if (gf(gaddag[curid])) {
				anas++;
				VERB(VNORM, " ") {
					printlrstr(sofar); printf("\n");
				}
			}
			anas += doanagram_e(gc(gaddag[curid]), sofar, depth+1, rest);
		}
		*lp = UBLANK;
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
	return doanagram_e(1, sofar, 0, lset);
}


/* lookup using bitset.  */
int
bs_lookup(int i, letter_t *word, uint32_t nodeid)
{
	letter_t l;
	bs_t b;
	int matchcount = 0;

	ASSERT(i > 0);

	for (i-=1; i >= 0; i--) {
		l = word[i];
DBG(DBG_LOOK, "i=%d, word[i]=%c, nid=%d\n", i, l2c(l), nodeid);

		b = l2b(l);
		if (l == UBLANK) {
			letter_t bl;
			b = bitset[nodeid] & ALLPHABITS;
			while (bl = nextl(&b, &nodeid)) {
				/* recurse on blanks. */
				word[i] = BB | bl;
DBG(DBG_LOOK, "i=%d, blank=%c nid=%d word=",i, l2c(BB|bl), nodeid) {
	printlstr(word); printf("\n");
}
				if ((i <= 0) && ( gf(gaddag[nodeid]))) {
					matchcount++;
					VERB(VNORM, " ") {
						printlstr(word); printf("\n");
					}
				}
				if (i>0)
					matchcount += bs_lookup(i, word, gc(gaddag[nodeid]));
			}
			word[i] = UBLANK;
			break;
		} else if (b & bitset[nodeid]) {
			nodeid = gotol(l, nodeid);
			if ((i == 0) && ( gf(gaddag[nodeid]))) {
				matchcount++;
				VERB(VNORM, " ") {
					printlstr(word); printf("\n");
				}
				break;
			}
			nodeid = gc(gaddag[nodeid]);
		} else {
			break;
		}
	}
DBG(DBG_LOOK, "i=%d found %d matches\n", i, matchcount);
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
	under = b->spaces[mr][mc].b.f.mls[dir];
DBG(DBG_MLS, "update %cmls vals for (%d,%d) with %d+%d\n", dc? 'h':'v', mr, mc, val, under);
	val += under;
	/* you have to have it both ways. */
	r = mr + dr;
	c = mc + dc;
	while (b->spaces[r][c].b.f.letter  && ((r<BOARDY)&&(c<BOARDX))) {
		r += dr; c += dc;
	}
	if ((r<BOARDY && c<BOARDX)) {
		b->spaces[r][c].b.f.mls[dir] = val;
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
	r = mr - dr;
	c = mc - dc;
	while (b->spaces[r][c].b.f.letter && ((r>=0)&&(c>=0))) {
		r -= dr; c -= dc;
	}
	if ((r>=0)&&(c>=0)) {
		b->spaces[r][c].b.f.mls[dir] = val;
DBG(DBG_MLS, "%cmls set to %d at (%d,%d)\n", dc? 'h':'v', val, r, c);
	}
}

/* fold in the last letter used, prepare for new letter */
inline void
updatescore(scthingy_t *sct)
{
DBG(DBG_SCORE, "ttl_ts=%hd ttl_tbs=%hd, ttl_wm=%hd, ttl_xs=%hd, played=%hd, ts=%hd, tbs=%hd, lms=%hd, wm=%hd, play=%hd\n", sct->ttl_ts, sct->ttl_tbs, sct->ttl_wm, sct->ttl_xs, sct->played, sct->ts, sct->tbs, sct->lms, sct->wm, sct->play);
//	if (sct->ttl_wm ==0) sct->ttl_wm = 1;
//	if (sct->wm == 0) sct->wm = 1;
	sct->ttl_ts += sct->ts;
	sct->ttl_tbs += sct->tbs;
	sct->ttl_wm *= sct->wm;
	if (sct->play > 1) {
		sct->ttl_xs += sct->wm * (sct->lms + sct->tbs);
	}
	if (sct->play) sct->played++;
	sct->ts = 0; sct->tbs = 0; sct->wm=1; sct->lms = 0; sct->play = 0;
}

/* handle leftover letters after end of game. */
int
unbonus(rack_t *r, bag_t bag, int bagpos)
{
	int tval = 0;
	int i, j = 0;
	while (bagpos < baglen) {
		tval += lval(bag[bagpos]);
		bagpos += 1;
	}
	for (i = 0; i < 7; i++) {
		if (r->tiles[i] == '\0') break;
		if (r->tiles[i] == MARK) {
			r->tiles[i] = '\0';
			continue;
		}
		tval += lval(r->tiles[i]);
		/* squeeze to end */
		r->tiles[j] = r->tiles[i];
		j++;
	}
	r->tiles[i] = '\0';
	return tval;
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
DBG(DBG_SCORE, "ttl_ts=%hd ttl_tbs=%hd, ttl_wm=%hd, ttl_xs=%hd, played=%hd, ts=%hd, tbs=%hd, lms=%hd, wm=%hd, play=%hd\n", sct.ttl_ts, sct.ttl_tbs, sct.ttl_wm, sct.ttl_xs, sct.played, sct.ts, sct.tbs, sct.lms, sct.wm, sct.play);
	/* bingo */
	if (sct.played >= RACKSIZE) {
		fsc += BINGOBONUS;
	}
	/* cross word scores */
	fsc += sct.ttl_xs;
	/* word score */
	fsc += sct.ttl_tbs * sct.ttl_wm;
	return fsc;
}

int updatembs(board_t *b, int dir,  int r, int c, letter_t L);

/* mm7: add mnids to space data.
 */
int
makemove7(board_t *b, move_t *m, int playthru, int umbs, rack_t *r)
{
	int cr, cc, dr, dc, ts, i, tts, er, ec;
	space_t *sp;
	letter_t l;
	bs_t fbs;
	int side;
	int len = 0;

	dr = m->dir;
	dc = 1 - m->dir;
	tts = 0;
	int nid = 1;
	int wlen = 0;

	/* start at the end of the word. */
	i = strlen(m->tiles);
	if (i == 0) { return 0; }	// an empty play. (not legal)
	if (playthru) {
		wlen = i;
	} else {
		wlen = m->lcount;
	}
	cr = m->row;
	cc = m->col;
	if (m->dir == M_HORIZ) {
		cc += wlen;
	} else {
		cr += wlen;
	}
	i--;		// cc/cr actualy points 1 past.
	er = cr - dr;
	ec = cc - dc;

	/* part A: going "backwards" */
	do {
		cr-=dr; cc-=dc;
		sp = &(b->spaces[cr][cc]);
		if (sp->b.f.letter == '\0') {
			int rv;
			/* place tile */
			ASSERT(i >= 0);
			l = m->tiles[i];
			if (! umbs) updatemls(b, m->dir, cr, cc, lval(l));
			if (! umbs) updatembs(b, m->dir, cr, cc, l);
			if (! umbs) pluckrack(r, l);
			sp->b.f.letter = m->tiles[i];
			sp->b.f.anchor = 0;
			i--;
		} else {
			l = sp->b.f.letter;
			if (playthru) {
				if (m->tiles[i] != sp->b.f.letter) {
					if (m->tiles[i] != DOT) {
vprintf(VVERB, "warning[A]: playthru %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
					}
					m->tiles[i] = sp->b.f.letter;
				}
				i--;
			}
		}
		ts = lval(l);
		tts += ts;
DBG(DBG_MOVE, "moving from %d to %d via %c\n", nid, gc(gaddag[gotol(l,nid)]), l2c(l));
		nid = gotol(l, nid);
		nid = gc(gaddag[nid]);
	} while ( (cr > m->row) || (cc > m->col));

	/* we are at first letter in word. nid is with us. */
	/* either at edge of board, or there's a space before this one */
	/* sp should still point to first letter */
	/* we should also be out of tiles in the move */
	ASSERT(nldn(b, cr, cc, m->dir, -1));
	ASSERT((cr == m->row) && (cc == m->col));
	ASSERT(i < 0);
	ASSERT(sp->b.f.letter != '\0');
	for (side = -1; side <= 1; side +=2) {
		if (side == 1) {
			dc *= -side; dr *= -side;
			cr = er; cc = ec;
			sp = &(b->spaces[er][ec]);
			/* cross the SEP. If no SEP, the mbs is empty. */
			if (SEPBIT & bitset[nid]) {
				nid = gotol(SEP, nid);
				nid = gc(gaddag[nid]);
			} else {
				nid = -1;
			}
		}
		if (isroom(cr, cc, m->dir, side)) {
			/* stash sum under first letter */
			sp->b.f.mls[1-m->dir] = tts;
			/* save nid. */
			if (side == -1) sp->mnid[m->dir] = nid;
			cr -= dr; cc -= dc;
			sp = &(b->spaces[cr][cc]);
			ASSERT(sp->b.f.letter == '\0');
			sp->b.f.anchor |= (1-m->dir)+1;
			if (nldn(b, cr, cc, m->dir, side)) {
				/* an unplayed space */
				sp->b.f.mls[1-m->dir] = tts;
				sp->mbs[1-m->dir] = finals(nid);
				if (side == 1) sp->mnid[m->dir] = nid;
DBG(DBG_MOVE,"at %d,%d dir=%d, mls=%d, mbs=%x (from nid=%d)\n", cr, cc, m->dir, tts, finals(nid), nid);
			} else {
				/* it's a bridge space */
				dobridge(b, nid, cr+dr, cc+dc, m->dir, side);
				sp->b.f.mls[1-m->dir] = tts + b->spaces[cr-dr][cc-dc].b.f.mls[1-m->dir];
			}
		}
	}
	return 1;
}

/* rewrite. use ndn. ASSERT much. try to stay simple
 * assume playthru. Set mnids.
 */
int
makemove8(board_t *b, move_t *m, int playthru, int umbs, rack_t *r)
{
	int ewr, ewc;
	int curid = 1;
	int dr = m->dir;
	int dc = (1 - m->dir);
	space_t *sp;
	letter_t pl;
	int i = strlen(m->tiles) - 1;
	int cr, cc;
	letter_t npl, nnpl;
	int ts = 0;
	int tts = 0;

	ewr = m->row + (dr * i);
	ewc = m->col + (dc * i);
	ASSERT(playthru);

	for (/* i already set */; i >=0; i--)
	{
		cr = m->row + (dr * i);
		cc = m->col + (dc * i);
		sp = &(b->spaces[cr][cc]);
		pl = m->tiles[i];
		if ((curid <= 0) || (!(l2b(pl) & bitset[curid]))) {
			VERB(VNORM, "not a valid move ") {
				printmove(m, -1);
				return -1;
			}
		}
		if (sp != '\0') {
			if (sp->b.f.letter != pl) {
vprintf(VVERB, "warning[C]: move[%d] %c doesn't match board %c at %d,%d\n", i, l2c(m->tiles[i]), l2c(sp->b.f.letter), cr, cc);
				pl = sp->b.f.letter;
			}
		} else {
			updatemls(b, m->dir, cr, cc, lval(pl));
			//updatembs2(b, m->dir, cr, cc, pl);
			pluckrack(r, pl);
			sp->b.f.letter = pl;
			sp->b.f.anchor = 0;
		}
		ts = lval(pl);
		tts += ts;
		curid = gotol(pl, curid);
		curid = gc(gaddag[curid]);
	}
	ASSERT((cr == m->row) && (cc == m->col));
	npl = ndn(b, m->row, m->col, m->dir, -1);
	ASSERT(npl <= 0);
	if (npl == 0) {
		/* a space. */
		nnpl = ndn(b, cr - dr, cc - dc, m->dir, -1);
		if (nnpl <= 0) {
			sp->b.f.mls[1-m->dir] = tts;
			sp->mnid[m->dir] = curid;
			sp = &(b->spaces[cr-dr][cc-dc]);
			ASSERT(sp->b.f.letter == '\0');
			sp->b.f.anchor |= (1-m->dir)+1;
			sp->b.f.mls[1-m->dir] = tts;
			sp->mbs[1-m->dir] = finals(curid);
		} else {
//			dobridge2(...  );
			sp->b.f.mls[1-m->dir] = tts + b->spaces[cr-dr][cc-dc].b.f.mls[1-m->dir];
		}
	}
	/* now do the other end. */
	npl = ndn(b, ewr, ewc, m->dir, 1);
	if (npl == 0) {
		if ((curid <= 0) || (!(SEPBIT & bitset[curid]))) {
			VERB(VNORM, "not a valid move ") {
				printmove(m, -1);
				return -1;
			}
		}
		curid = gotol(SEP, curid);
		curid = gc(gaddag[curid]);
		ASSERT(curid > 0);
		nnpl = ndn(b, cr + dr, cc + dc, m->dir, 1);
		if (nnpl <= 0) {
			sp->b.f.mls[1-m->dir] = tts;
			sp->mnid[m->dir] = curid;
			sp = &(b->spaces[cr+dr][cc+dc]);
			ASSERT(sp->b.f.letter == '\0');
			sp->b.f.anchor |= (1-m->dir)+1;
			sp->b.f.mls[1-m->dir] = tts;
			sp->mbs[1-m->dir] = finals(curid);
		} else {
//			dobridge2(...  );
			sp->b.f.mls[1-m->dir] = tts + b->spaces[cr+dr][cc+dc].b.f.mls[1-m->dir];
		}
	}
	return 1;
}

/* mm6: while making move, remove letters from rack.
 */
int
makemove6(board_t *b, move_t *m, int playthru, int umbs, rack_t *r)
{
	int cr, cc, dr, dc, ts, i, tts, er, ec;
	space_t *sp;
	letter_t l;
	bs_t fbs;
	int side;
	int len = 0;

	dr = m->dir;
	dc = 1 - m->dir;
	tts = 0;
	int nid = 1;
	int wlen = 0;

	/* start at the end of the word. */
	i = strlen(m->tiles);
DBG(DBG_MOVE, "making move ") {
	printmove(m, -1); printf("with rack "); printlstr(r->tiles); printf("\n");
}
	if (i == 0) { return 0; }	// an empty play. (not legal)
	if (playthru) {
		wlen = i;
	} else {
		wlen = m->lcount;
	}
	cr = m->row;
	cc = m->col;
	if (m->dir == M_HORIZ) {
		cc += wlen;
	} else {
		cr += wlen;
	}
	i--;		// cc/cr actualy points 1 past.
	er = cr - dr;
	ec = cc - dc;

	/* part A: going "backwards" */
	do {
		cr-=dr; cc-=dc;
		sp = &(b->spaces[cr][cc]);
		if (sp->b.f.letter == '\0') {
			int rv;
			/* place tile */
			ASSERT(i >= 0);
			l = m->tiles[i];
			if (! umbs) updatemls(b, m->dir, cr, cc, lval(l));
			if (! umbs) updatembs(b, m->dir, cr, cc, l);
			if (! umbs) pluckrack(r, l);
			sp->b.f.letter = m->tiles[i];
			sp->b.f.anchor = 0;
			i--;
		} else {
			l = sp->b.f.letter;
			if (playthru) {
				if (m->tiles[i] != sp->b.f.letter) {
					if (m->tiles[i] != DOT) {
vprintf(VVERB, "warning[B]: playthru %c(%d) doesn't match played %c(%d)\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
					}
					m->tiles[i] = sp->b.f.letter;
				}
				i--;
			}
		}
		ts = lval(l);
		tts += ts;
DBG(DBG_MOVE, "moving from %d to %d via %c\n", nid, gc(gaddag[gotol(l,nid)]), l2c(l));
		nid = gotol(l, nid);
		nid = gc(gaddag[nid]);
	} while ( (cr > m->row) || (cc > m->col));

	/* we are at first letter in word. nid is with us. */
	/* either at edge of board, or there's a space before this one */
	/* sp should still point to first letter */
	/* we should also be out of tiles in the move */
	ASSERT(nldn(b, cr, cc, m->dir, -1));
	ASSERT((cr == m->row) && (cc == m->col));
	ASSERT(i < 0);
	for (side = -1; side <= 1; side +=2) {
		if (side == 1) {
			dc *= -side; dr *= -side;
			cr = er; cc = ec;
			sp = &(b->spaces[er][ec]);
			/* cross the SEP. If no SEP, the mbs is empty. */
			if (SEPBIT & bitset[nid]) {
				nid = gotol(SEP, nid);
				nid = gc(gaddag[nid]);
			} else {
				nid = -1;
			}
		}
		if (isroom(cr, cc, m->dir, side)) {
			/* stash sum under first letter */
			sp->b.f.mls[1-m->dir] = tts;
			cr -= dr; cc -= dc;
			sp = &(b->spaces[cr][cc]);
			ASSERT(sp->b.f.letter == '\0');
			sp->b.f.anchor |= (1-m->dir)+1;
			if (nldn(b, cr, cc, m->dir, side)) {
				/* an unplayed space */
				sp->b.f.mls[1-m->dir] = tts;
				sp->mbs[1-m->dir] = finals(nid);
DBG(DBG_MOVE,"at %d,%d dir=%d, mls=%d, mbs=%x (from nid=%d)\n", cr, cc, m->dir, tts, finals(nid), nid);
			} else {
				/* it's a bridge space */
				dobridge(b, nid, cr+dr, cc+dc, m->dir, side);
				sp->b.f.mls[1-m->dir] = tts + b->spaces[cr-dr][cc-dc].b.f.mls[1-m->dir];
			}
		}
	}
	return 1;
}

/* if we can't trust lcount, scan the board to find the actual length.
 * This function assumes that m->row,col are already correct.
 */
int
movelen(board_t *b, move_t *m, int playthru)
{
	int i = strlen(m->tiles);
	int cr, cc;
	int len = 0;

	cr = m->row; cc=m->col;
	while (i > 0) {
		if (b->spaces[cr][cc].b.f.letter == '\0') {
			i--;
			len++;
		} else {
			if (playthru) i--;
			len++;
		}
		cc += 1 - m->dir;
		cr  += m->dir;
		if ((cr < 0) || (cr >= BOARDY) ||
		    (cc < 0) || (cc >= BOARDX)) {
			return len;
		}
	}
	cc -= 1 - m->dir; cr -= m->dir;
	if (!playthru) {
		while (!nldn(b, cr, cc, m->dir, 1)) {
			len++;
			cc += 1 - m->dir;
			cr  += m->dir;
		}
	}
	return len;
}

/* use info on board to set move row, col and lcount.
 * we can assume we don't have to back over any spaces.
 */
void
fixlen(board_t *b, move_t *m, int playthru)
{
	/* first move "back" over letters. */
	while (!nldn(b, m->row, m->col, m->dir, -1)) {
		m->col -=(1-m->dir); m->row-=m->dir;
	}
	m->lcount = movelen(b, m, playthru);
}

/* use mm, so we are slightly recursive.
 * returns 1 IFF there are actually any cross tiles.
 */
int
updatembs(board_t *b, int dir,  int r, int c, letter_t L)
{
	move_t um;
	int dr, dc;

DBG(DBG_MBS, "at %d,%d dir=%d, for %c\n", r, c, dir, l2c(L));
	dr = 1 - dir; dc = dir;
	um.tiles[0] = L; um.tiles[1] = '\0';
	um.row = r; um.col = c; um.lcount = 0; um.dir = 1 - dir;

//	while ( ! nldn(b, um.row, um.col, um.dir, 1)) {
//		um.col += dc; um.row += dr;
//	}
//	um.lcount = (um.col - c) + (um.row - r) + 1;
	um.lcount = 0;

DBG(DBG_MBS, "calling mm with move %d,%d, dir=%d, lcount=%d\n", um.row, um.col, um.dir, um.lcount);
	b->spaces[r][c].b.f.letter = '\0';
	fixlen(b, &um, 0);
	makemove6(b, &um, 0, 1, NULL);
	b->spaces[r][c].b.f.letter = L;
	return (um.lcount);
}

/* old score was borken. Re-write to use current funcs and structs.
 * remove doit(done). use scthingy(done). use new funcs(done).
 * If lcount is wrong, fix it(done). Don't assume word length is known(done).
 * row,col ALWAYS points at first letter in word, despite playthru.
 * Can assume that the word fits on the board (parsemove).
 */
int
score2(move_t *m, board_t *b, int playthru)
{
	scthingy_t sct = newsct;	// pre-initialized!!!
	int cr, cc, i = 0;
	space_t *sp;
	int dc, dr;
	int sc = 0;
	int pcnt;			// for lcount.

DBG(DBG_SCORE,"in score with (%d,%d)->%s lcount=%d strlen=%d, playthru=%d\n", m->row, m->col,  m->dir == M_HORIZ ? "horiz" : "vert", m->lcount, strlen(m->tiles), playthru);

	if (m->tiles[0] == '\0') return 0;// empty move scores nothing.
	cr = m->row; cc = m->col;
	dc = 1 - m->dir; dr = m->dir;
	sp = &(b->spaces[cr][cc]);

	for (;/*EVER*/;) {
		if (sp->b.f.letter != '\0') {
			/* on a previously played tile */
			if (playthru) {
				if (m->tiles[i] != sp->b.f.letter) {
					if (m->tiles[i] != DOT) {
vprintf(VVERB, "warning: playthru %c(%d) doesn't match played %c(%d), replacing\n", l2c(m->tiles[i]), m->tiles[i], l2c(sp->b.f.letter), sp->b.f.letter);
					}
					m->tiles[i] = sp->b.f.letter;
				}
				i++;
			}
			sct.ts = lval(sp->b.f.letter);
			sct.tbs = sct.ts;
			sct.play = 0;
			sct.wm = 1;
			sct.lms = 0;
		} else {
			sct.ts = lval(m->tiles[i]);
			sct.tbs = sct.ts * sp->b.f.lm;
			sct.wm = sp->b.f.wm;
			sct.lms = sp->b.f.mls[m->dir];
			sct.play = 1;
			if (sp->b.f.anchor & (m->dir + 1)) {
				sct.play += 1;
			}
			i++;
		}
		updatescore(&sct);
		/* are we done yet? */
		if (m->tiles[i] == '\0') {
			/* no tiles left... */
			if (playthru || nldn(b, cr, cc, m->dir, 1)) {
				break;
			}
		}
		/* next space. remember we assume the word fits. */
		cr += dr; cc += dc;
		sp = &(b->spaces[cr][cc]);
	}

	/* some sanity checks. We could be messed up. */
	if (m->tiles[i] != '\0') {
		VERB(VNORM, "warning: %d leftover tiles=\n", strlen(&(m->tiles[i]))) {
			printlstr( &(m->tiles[i]));
			printf("\n");
		}
	}
	if (! nldn(b, cr, cc, m->dir, 1)) {
		vprintf(VNORM, "warning: letters on eow at %d, %d\n", cr, cc);
	}
	
	sc = finalscore(sct);
	updatescore(&sct);

	/* correct lcount if it is off. use new playthru rules. */
	if (playthru) {
		pcnt = sct.played;
	} else {
		pcnt = (cr - m->row) + (cc - m->col) + 1;
	}

	if (m->lcount != pcnt) {
		vprintf(VVERB, "correcting move lcount from %d to %d\n", m->lcount, pcnt);
		m->lcount = pcnt;
	}
	return sc;
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
		printf("Horizontal move letter scores\n");
		break;
	case B_VMLS:
		printf("Vertical nmove letter scores\n");
		break;
	case B_PLAYS:
		return;
		// break;
	case B_BONUS:
		printf("Space bonus values\n");
		break;
	case B_HMBS:
		printf("Horizontal move bitsets\n");
		break;
	case B_VMBS:
		printf("Vertical move bitsets\n");
		break;
	case B_HMNID:
		printf("Horizontal move node id\n");
		break;
	case B_VMNID:
		printf("Vertical move node id\n");
		break;
	case B_ANCHOR:
		printf("anchor squares\n");
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
				if (sp->b.f.mls[M_VERT])
					printf("^%-2d ", sp->b.f.mls[M_VERT]);
				else if (sp->b.f.letter != EMPTY)
					printf(" %c  ", l2c(sp->b.f.letter));
				else
					printf("    ");
				break;
			case B_HMLS:
				if (sp->b.f.mls[M_HORIZ])
					printf(">%-2d ", sp->b.f.mls[M_HORIZ]);
				else if (sp->b.f.letter != EMPTY)
					printf(" %c  ", l2c(sp->b.f.letter));
				else
					printf("    ");
				break;
			case B_HMBS:
				if (sp->b.f.letter != EMPTY) {
					printf(" %c  ", l2c(sp->b.f.letter));
				} else {
					printf("%x ", sp->mbs[M_HORIZ]);
				}
				break;
			case B_VMBS:
				if (sp->b.f.letter != EMPTY) {
					printf(" %c  ", l2c(sp->b.f.letter));
				} else {
					printf("%x ", sp->mbs[M_VERT]);
				}
				break;
			case B_VMNID:
				printf("%d ", sp->mnid[M_VERT]);
				break;
			case B_HMNID:
				printf("%d ", sp->mnid[M_HORIZ]);
				break;
			case B_ANCHOR:
				if (sp->b.f.anchor) {
					printf(" &%d ", sp->b.f.anchor);
				} else {
					if (sp->b.f.letter == EMPTY) {
						printf(" _  ");
					} else {
						printf(" %c  ", l2c(sp->b.f.letter));
					}
				}
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
	char *cp, *dp;
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
	while ((dp = strchr(cp, '.')) != NULL) {
		*dp = CDOT;
	}
	if (c2lstr(cp, m->tiles, played)) {
		vprintf(VVERB, "%s had invalid characters\n", cp);
		return 5;
	}
	while ((dp = strchr(cp, CDOT)) != NULL) {
		*dp = '.';
	}
	return 0;
}

void
fixmove(move_t *m, int rev)
{
	if (rev == 0) {
		revstr(m->tiles);
	} else {
		revnstr(m->tiles, rev);
	}
}

void
printmove(move_t *m, int rev)
{
	if (m->dir == M_HORIZ) {
		printf("%d%c:", m->row+1, coltags[m->col]);
	} else {
		printf("%c%d:", coltags[m->col], m->row+1);
	}
	if (rev < 0) {
		printlstr(m->tiles);
	} else if (rev == 0) {
		printlrstr(m->tiles);
	} else {
		revnstr(m->tiles, rev);
		printlstr(m->tiles);
		revnstr(m->tiles, rev);
	}
	if (m->score > 0) {
		printf(" %d", m->score);
	}
	printf("\n");
}


/*
 * print out a full position. Use VERB levels.
 * depth, move, score, rack, (bag, bagpos), board
 * stats
 */
void
printpos(position_t P)
{
if (dtrap == 0) {
	dtrap = 1;
} 
	vprintf(VNORM, "position[%d]=%d",  P.depth, P.sc);
	VERB(VNORM, " move %d of %d ", P.mvndx, P.mvcnt) {
		printmove(&(P.m), -1);
	}
	VERB(VVERB, "rack=") {
		printlstr(P.r.tiles);
		printf(" bag=%c[%d] ",bagtag, P.bagndx);
		printf("\n");
	}
	stprintf(STMED, "%llu moves in %llu nsec: %llu nsec/mv\n", P.stats.moves, P.stats.evtime, P.stats.evtime/P.stats.moves);
	stprintf(STMED, "max: depth=%d width=%d word score=%d game score=%d\n", P.stats.maxdepth, P.stats.maxwidth, P.stats.wordhs, P.stats.gamehs);
	VERB(VVERB, "-") {
		showboard(P.b, B_TILES);
	}
	VERB(VNOISY, "-") {
		showboard(P.b, B_ANCHOR);
		showboard(P.b, B_HMLS);
		showboard(P.b, B_VMLS);
		showboard(P.b, B_HMBS);
		showboard(P.b, B_VMBS);
	}
}

/*
 * genall: this move generator has no strategy. Given board, rack,
 * and move position/dir it finds ALL the moves.  Since the number of
 * args is large, we use a custom struct that holds needed info. The
 * other few items are stack items.
 */

#define MAXMVS	(16*1024)/* mvs array. expand as needed. */


inline void
addsct(scthingy_t *sct, letter_t l, int dir, space_t sp)
{
	sct->ts = lval(l);
	sct->tbs = sp.b.f.lm * sct->ts;
	sct->wm =  sp.b.f.wm;
	sct->lms = sp.b.f.mls[dir];
	sct->play = 1;
	if ( sp.b.f.anchor & (dir + 1)) {
		sct->play += 1;
	}
}

/* genat data struct. */
typedef struct _gat_d {
	move_t m;		// move to add to mvs
	rack_t r;		// current rack.
	int side;		// which way
	scthingy_t sct;		// scoring
	int nodeid;		// for this square
	bs_t rbs;		// matches r
	int ndx;		// strlen move.tiles
	int played;		// from rack.
	int swr, swc;		// start word space
	int ewr, ewc;		// end word space
	int presep;		// special: 1 if anchored to left.
} gatd_t;

/*
 * another re-write. reduce recursion with pregen.
 * this is too hard: simplify. ASSERT and block stuff. Make it clear
 * what is needed where.
 * calling convention: the gat is const (input only). Things in gat
 * are only ever passed DOWN, never up, via a new gat struct.
 * the only thing that comes back up is the mvs array and the movecnt
 * (return value).
 * a special case to handle is the "empty" move, on first call.
 * we can detect that in a number of ways: sw == ew, m.tiles is empty,
 * played is 0, nodeid is 1...
 */
int
genallat_d(position_t *P, move_t *mvs, int *mvsndx, const gatd_t gat)
{
	board_t *b = &(P->b);
	gatd_t newgat = gat;

	int movecnt = 0;
	letter_t pl, npl;
	int *cr; int *cc;
	scthingy_t sct;

	int curid;
	int saveid;
	int cid;
	int sepid;
	bs_t bs;
	bs_t bbs;
	letter_t bl = 0;

	/* sanity checks. add more later. */
	ASSERT(gat.nodeid > 0);
	ASSERT((gat.ewc >= gat.swc) && (gat.ewr >= gat.ewr));

DBG(DBG_GEN, "[%d] at %d,%d/%d to %d,%d (%d) node=%d rbs=%x played=%d", gat.ndx, gat.swr, gat.swc, gat.m.dir, gat.ewr, gat.ewc, gat.side, gat.nodeid, gat.rbs, gat.played) {
	printf(" - word=\"");
	printlstr(gat.m.tiles);
	printf("\", rack=\"");
	printlstr(gat.r.tiles);
	printf("\"\n");
}

	/* handle the start condition. */
	if (gat.side < 0) {
		cr = &newgat.swr;
		cc = &newgat.swc;
	} else {
		cr = &newgat.ewr;
		cc = &newgat.ewc;
	}
	pl = ndn(b, *cr, *cc, gat.m.dir, gat.ndx == 0 ? 0 : gat.side);
	if (pl < 0) return  movecnt;
	if (gat.ndx > 0) {
		*cc += (1 - gat.m.dir) * gat.side;
		*cr += (gat.m.dir) * gat.side;
	}

	if (pl > 0) {
		letter_t npl;
		int change = 0;
		while (pl > 0) {
			if (!(bitset[newgat.nodeid] & l2b(pl))) {
				return movecnt;
			}
			newgat.nodeid = gotol(pl, newgat.nodeid);
			if (pl != SEP) {
				newgat.m.tiles[newgat.ndx++] = pl;
				newgat.sct.ttl_ts += lval(pl);
			} else {
				revnstr(newgat.m.tiles, newgat.ndx);
			}
			/* got the letter, see if we are at end of word */
			npl = ndn(b, *cr, *cc, gat.m.dir, newgat.side);
			if ((npl < 0) && (newgat.side < 0)) {
				npl = ndn(b, newgat.ewr, newgat.ewc, newgat.m.dir, 1);
				if (npl < 0) break;
				pl = SEP;
				cr = &newgat.ewr; cc = &newgat.ewc;
				newgat.side = 1;
			} else {
				if (npl <= 0) break;
				pl = npl;
			}
			newgat.nodeid = gc(gaddag[newgat.nodeid]);
			if (pl != SEP) {
				*cc += (1 - newgat.m.dir) * newgat.side;
				*cr += (newgat.m.dir) * newgat.side;
			}
		}
		newgat.sct.ttl_tbs = newgat.sct.ttl_ts;
		ASSERT((((pl > 0) && (newgat.nodeid > 0))));
		if (gf(gaddag[newgat.nodeid]) && (newgat.played > 0)) {
			newgat.m.score = finalscore(newgat.sct);
			newgat.m.row = newgat.swr; newgat.m.col = newgat.swc;
			VERB(VNOISY, "at_d:") {
				printmove(&(newgat.m), -1);
			}
			/* record play */
			ASSERT(*mvsndx < MAXMVS);
			mvs[*mvsndx] = newgat.m;
			if (newgat.side < 0) {
				revstr(mvs[*mvsndx].tiles);
			}
			*mvsndx += 1; movecnt++; gmcnt++;
		}
		pl = npl;
		/* another special case: we hit the wall. */
		if (pl < 0) {
			newgat.side = 1;
		}
		newgat.nodeid = gc(gaddag[newgat.nodeid]);
		*cc += (1 - newgat.m.dir) * newgat.side;;
		*cr += (newgat.m.dir) * newgat.side;
		if ((pl < 0) || (newgat.nodeid <= 0)) {
			/* no more room, no more gaddag */
			return movecnt;
		}
	}
	ASSERT((pl == 0) && (newgat.nodeid > 0));
	/* prune */
	if ((gat.side < 0) && (gat.played > 0) &&
	    b->spaces[*cr][*cc].b.f.anchor) {
		return movecnt;
	}
	/* iterate over playable tiles */
	saveid = newgat.nodeid;
	curid = newgat.nodeid;
	bbs = bitset[curid];
	sct = newgat.sct;
	sct.play = 1;
	sct.wm = b->spaces[*cr][*cc].b.f.wm;
	sct.tbs = b->spaces[*cr][*cc].b.f.lm;	/* setup for below */
	sct.lms = b->spaces[*cr][*cc].b.f.mls[newgat.m.dir];
	if (b->spaces[*cr][*cc].b.f.anchor & (1+newgat.m.dir)) {
		bbs &= b->spaces[*cr][*cc].mbs[newgat.m.dir];
		sct.play += 1;
	}
	bs = gat.rbs;
	/* special case. If pregen moved us one space left, then when we
	 * hit the end of the played tiles, the only thing we can do
	 * is reverse direction, because this must be another anchor.
	 */
	if ((newgat.side < 0) && (newgat.played <= 0) && (newgat.presep)) {
		ASSERT(b->spaces[*cr][*cc].b.f.anchor);
		newgat.presep = 0;
		goto seponly;
	}
	newgat.m.tiles[newgat.ndx+1] = '\0';
	npl = ndn(b, *cr, *cc, newgat.m.dir, newgat.side);
onceagain:
	bs &= bbs;
	while ((pl = nextl(&bs, &curid)) != '\0') {
		/* could be either direction. */
		newgat.played = gat.played+1;
		newgat.m.tiles[newgat.ndx] = pl | bl;
		newgat.sct = sct;
		newgat.sct.ts = lval(pl);
		newgat.sct.tbs *= newgat.sct.ts;/* saved multiplier */
		updatescore(&(newgat.sct));
		if (gf(gaddag[curid]) && (npl <= 0)) {
			newgat.m.score = finalscore(newgat.sct);
			newgat.m.row = newgat.swr; newgat.m.col = newgat.swc;
			VERB(VNOISY, "at_d: ") {
				printmove(&(newgat.m), newgat.side < 0 ? 0 : -1);
			}
			ASSERT(*mvsndx < MAXMVS);
			mvs[*mvsndx] = newgat.m;
			if (newgat.side < 0) {
				revstr(mvs[*mvsndx].tiles);
			}
			*mvsndx += 1; movecnt++; gmcnt++;
		}
		if (!bl) rackem(&(gat.r), &(newgat.r), &(newgat.rbs), pl);
		newgat.nodeid = gc(gaddag[curid]);
		if (newgat.nodeid > 0) {
			newgat.ndx++;

DBG(DBG_GEN, "[%d] recurse at %d,%d/%d to %d,%d (%d) node=%d rbs=%x played=%d\n", newgat.ndx, newgat.swr, newgat.swc, newgat.m.dir, newgat.ewr, newgat.ewc, newgat.side, newgat.nodeid, newgat.rbs, newgat.played);
			movecnt += genallat_d(P, mvs, mvsndx, newgat);
			newgat.ndx--;
		}
	}
	/* handle blank */
	if (newgat.rbs & UBLBIT) {
		if (!bl) {
			newgat.r = gat.r;
		}
		curid = saveid;
		rackem(&(newgat.r), &(newgat.r), &(newgat.rbs), UBLANK);
		bs = ALLPHABITS;
		bl = BB;
		goto onceagain;
	}
seponly:
	/* and do SEP if needed */
	if ((newgat.side < 0) && (bbs & SEPBIT) && (newgat.played > 0)) {
		npl = ndn(b, newgat.ewr, newgat.ewc, newgat.m.dir, 1);
		if (npl >= 0) {
			newgat.sct = sct;
			newgat.m.tiles[newgat.ndx] = 0;
			newgat.played--;
			newgat.r = gat.r;
			newgat.rbs = gat.rbs;
			newgat.swr += newgat.m.dir;
			newgat.swc += (1 - newgat.m.dir);
			newgat.side = 1;
//			newgat.ewr += newgat.m.dir;
//			newgat.ewc += (1 - newgat.m.dir);
			curid = gotol(SEP, saveid);
			newgat.nodeid = gc(gaddag[curid]);
			revstr(newgat.m.tiles);
			ASSERT(newgat.nodeid > 0);

DBG(DBG_GEN, "[%d] recurse B at %d,%d/%d to %d,%d (%d) node=%d rbs=%x played=%d\n", newgat.ndx, newgat.swr, newgat.swc, newgat.m.dir, newgat.ewr, newgat.ewc, newgat.side, newgat.nodeid, newgat.rbs, newgat.played);
			movecnt += genallat_d(P, mvs, mvsndx, newgat);
		}
	}

DBG(DBG_GEN, "[%d] pop %d moves\n", newgat.ndx, movecnt);
	return movecnt;
}

int
pregen_d(position_t *P, move_t *mvs, int *mvsndx)
{
	board_t *b = &(P->b);
	move_t *m = &(P->m);
	rack_t *r = &(P->r);
	gatd_t gogat;

	letter_t pl;
	int mvcnt = 0;
	int ar = m->row;
	int ac = m->col;
	int nodeid = 1;
	int cid;
	bs_t rbs;

DBG(DBG_GEN, "at %d,%d dir=%d", ar,ac, m->dir) {
	printf(" rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}

	/* simplify a little: weigh anchor but let at_d roll it home. */
	gogat.rbs = lstr2bs(P->r.tiles);
	gogat.m = *m;
	gogat.r = *r;
	gogat.sct = newsct;
	gogat.ndx = 0;
	gogat.nodeid = 1;
	gogat.played = 0;		// from rack.
	gogat.swr = P->m.row;
	gogat.swc = P->m.col;
	gogat.ewr = P->m.row;
	gogat.ewc = P->m.col;
	gogat.presep = 0;
	gogat.side = -1;
	/* we are first, so lets look around. */
	pl = ndn(b, gogat.swr, gogat.swc, gogat.m.dir, -1);
	if (pl > 0) {
		/* move over 1. */
		gogat.swr -= gogat.m.dir; gogat.swc -= (1-gogat.m.dir);
		gogat.ewr = gogat.swr; gogat.ewc = gogat.swc;
		gogat.presep = 1;
	} else if (pl = ndn(b, gogat.ewr, gogat.ewc, gogat.m.dir, 1) > 0) {
		gogat.side = -1;
		while (pl > 0) {
			/* in this case, goto the end. */
			gogat.ewr += gogat.m.dir; gogat.ewc += (1-gogat.m.dir);
			pl = ndn(b, gogat.ewr, gogat.ewc, gogat.m.dir, 1);
		}
		gogat.swr = gogat.ewr; gogat.swc = gogat.ewc;
	}
	return genallat_d(P, mvs, mvsndx, gogat);
}


int
genall_d(position_t *P, move_t **mvs, int *mvsndx)
{
	int r, c, dir, moves = 0;
	bs_t rbs;

	if (*mvs == NULL) {
		*mvs = (move_t *)malloc( sizeof(move_t) * MAXMVS);
		if (*mvs == NULL) {
			vprintf(VNORM, "ERROR: failed allocate moves array\n");
			return 0;
		}
	}
	bzero(*mvs, sizeof(move_t)*MAXMVS);
	*mvsndx = 0;
	rbs = lstr2bs(P->r.tiles);

	if (P->sc == -1) {
		P->sc = 0;
		P->m.row = STARTR; P->m.col = STARTC; P->m.dir = M_HORIZ;
		moves = pregen_d(P, *mvs, mvsndx);
DBG(DBG_GEN, "genall made %d start moves\n", moves);
		return moves;
	}

	P->m = emptymove;	

	for (dir = 0; dir < 2; dir++) {
		for (r = 0; r < BOARDY; r++) {
			for (c = 0; c < BOARDX; c++) {
				if (P->b.spaces[r][c].b.f.anchor) {
					P->m.row = r; P->m.col = c;
					P->m.dir = dir;
					moves += pregen_d(P, *mvs, mvsndx);
				}
			}
		}
	}
	ASSERT(moves == *mvsndx);
DBG(DBG_GEN, "genall made %d total moves (%d mvs)\n", moves, *mvsndx);
	return moves;
}



/* try pre handler function again. move anchor in some cases. */
/* try using _b. */
/* non-recursive part.  take care of played tiles first */
int
genallat_c(position_t *P, move_t *mvs, int *mvsndx)
{
	board_t *b = &(P->b);
	move_t *m = &(P->m);
	rack_t *r = &(P->r);

	letter_t pl;
	scthingy_t sct = newsct;
	int mvcnt = 0;
	int ar = m->row;
	int ac = m->col;
	int nodeid = 1;
	int cid;
	bs_t rbs;

DBG(DBG_GEN, "new genallat %d,%d dir=%d", ar,ac, m->dir) {
	printf(" rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}

	rbs = lstr2bs(P->r.tiles);
	/* we are first, so lets look around. */
	if (!nldn(b, m->row, m->col, m->dir, -1)) {
		int i = 0;
		/* played tile on left. use it as prefix. */
		while (!nldn(b, m->row, m->col, m->dir, -1)) {
			m->row -= m->dir; m->col -= (1-m->dir);
			pl = b->spaces[m->row][m->col].b.f.letter;
			m->tiles[i] = pl; i++;
			nodeid = gotol(deblank(pl), nodeid);
			nodeid = gc(gaddag[nodeid]);
			sct.ttl_ts += lval(pl);
		}
		sct.ttl_tbs = sct.ttl_ts;
		/* in this case, we have to change direction. */
		if (bitset[nodeid] & SEPBIT) {
			nodeid = gotol(SEP, nodeid);
			nodeid = gc(gaddag[nodeid]);
		} else {
			/* no valid move here. */
			for (; i>=0;i--) m->tiles[i]='\0';
			return 0;
		}
		/* now call our recursive part. */
DBG(DBG_GEN, "rcall A pos=%d depth=%d rbs=%x\n", i, i, rbs);
		mvcnt = genallat_b(P, mvs, mvsndx, i, nodeid, sct, i, rbs);
		for (; i>=0;i--) m->tiles[i]='\0';
	} else if (!nldn(b, m->row, m->col, m->dir, 1)) {
		/* look on the other side. */
		int i = 0, j= 0; int cr = m->row; int cc = m->col;
		cid = nodeid;
		/* find the 'end' of the played tiles */
		while (!nldn(b, cr, cc, m->dir, 1)) {
			cr += m->dir; cc+= (1-m->dir);
			j++;
		}
		/* now traverse gaddag back to original spot.*/
		for (; j > 0; j--) {
			pl = b->spaces[cr][cc].b.f.letter;
			m->tiles[i] = pl; i++;
			nodeid = gotol(deblank(pl), cid);
			cid = gc(gaddag[nodeid]);
			sct.ttl_ts += lval(pl);
			cr -= m->dir; cc-= (1-m->dir);
		}
		sct.ttl_tbs = sct.ttl_ts;
DBG(DBG_GEN, "rcall C pos=%d depth=%d rbs=%x, mxy=%d,%d cxy=%d,%d nid=%d\n", 0, i, rbs, m->row, m->col, cr, cc, nodeid);
		mvcnt = genallat_b(P, mvs, mvsndx, 0, cid, sct, i, rbs);
		for (; i>=0;i--) m->tiles[i]='\0';
	} else {
		/* pass-thru */
DBG(DBG_GEN, "rcall B pos=%d depth=%d rbs=%x\n", 0, 0, rbs);
		mvcnt = genallat_b(P, mvs, mvsndx, 0, nodeid, sct, 0, rbs);
	}
	return mvcnt;
}


/* mod to use position_t. This is the most used in lah. */
int
genallat_b(position_t *P, move_t *mvs, int *mvsndx, int pos, int nodeid, scthingy_t sct, int depth, bs_t rbs)
{
	board_t *b = &(P->b);
	move_t *m = &(P->m);
	rack_t *r = &(P->r);

	int movecnt = 0;
	int curid = -1;
	int cid;
	int sepid;
 	letter_t *w = m->tiles;
	int ndx = depth;
	int prelen;
	int curcol = m->col;
	int currow = m->row;
	char *rlp = (char *)1;
//	bs_t rbs = 0;
	bs_t bl = 0;
	bs_t bs = 0;
	register letter_t pl;
	int side;
	int dr = m->dir;
	int dc = 1 - m->dir;

DBG(DBG_GEN, "[%d] at %d,%d(%-d) node=%d", strlen(w), currow,curcol,pos, nodeid) {
	printf(" - word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	ASSERT(strlen(w) == depth);
//	ndx = strlen(w);	/* depth */
	if (pos > 0) {
		side = 1;
		prelen = pos;
		currow += ndx * m->dir;
		curcol += ndx * (1 - m->dir);
	} else {
		side = -1;
		prelen = ndx + 1;
	}
	/* if NOT first, don't redo anchors */
//	if ((sct.played > 0) && b->spaces[currow][curcol].b.f.anchor) 
	if ((side < 0) && (ndx > 0) && (sct.played > 0) && b->spaces[currow][curcol].b.f.anchor){
DBG(DBG_GEN, "[%d]time to prune, anchor=%d\n", ndx, b->spaces[currow][curcol].b.f.anchor);
		return movecnt;
	}
	w[ndx+1] = '\0';

	updatescore(&sct);
	while (rlp != NULL) {

DBG(DBG_GEN, "[%d]inline gen rbs=%x, bl=%d, bs=%x, curid=%d, rlp=%p lp=%c\n", ndx, rbs, bl,  bs, curid, rlp, l2c(w[ndx])) {

}
		pl = b->spaces[currow][curcol].b.f.letter;
		if (pl != '\0') {
DBG(DBG_GEN, "[%d]found %c on board at %d, %d\n", ndx, l2c(pl), currow, curcol);
			/* make sure we are still on the path */
			if (bitset[nodeid] & l2b(pl)) {
				w[ndx] = pl;
				rlp = NULL;
				curid = gotol(deblank(w[ndx]), nodeid);
				sct.ts = lval(pl);
				sct.tbs = sct.ts;
				sct.wm = 1;
				sct.play = 0;
				sct.lms = 1;
			} else {
				break;
			}
		} else {
			if (curid == -1) {
//				rbs = lstr2bs(r->tiles);
				if (rbs & UBLBIT) bl = BB;
				curid = nodeid;
				if (bl) bs = ALLPHABITS & bitset[nodeid];
				else bs = rbs & bitset[nodeid];
				if (b->spaces[currow][curcol].b.f.anchor & (1+m->dir)) {
					bs &= b->spaces[currow][curcol].mbs[m->dir];
				}
DBG(DBG_GEN, "[%d]first (%d,%d)/%d bl=%x, rbs=%x, id=%d, bitset=%x mbs=%x bs=%x\n", ndx, currow, curcol, m->dir, bl, rbs, nodeid, bitset[nodeid], b->spaces[currow][curcol].mbs[m->dir], bs);
			} else {
				if (bl) {
					setbit(&rbs, UBLANK-1);
					*rlp = UBLANK;
				} else {
					setbit(&rbs, w[ndx]-1);
					*rlp = w[ndx];
				}
DBG(DBG_GEN, "[%d] Pop %c back to rack\n", ndx,  l2c(w[ndx]));
			}
			if ((bs == 0) && (bl)) {
				bl = 0;
				bs = rbs & bitset[nodeid];
				if (b->spaces[currow][curcol].b.f.anchor & (1+m->dir)) {
					bs &= b->spaces[currow][curcol].mbs[m->dir];
				}
				curid = nodeid;
			}
			if (bs == 0) {
				rlp = NULL;
				w[ndx] = '\0';
				break;
			} else {
				pl = nextl(&bs, &curid);
				ASSERT(pl != 0);
DBG(DBG_GEN,"[%d]match %c bl=%x, node %d rack=", ndx, l2c(pl),bl, nodeid) {
	printlstr(r->tiles); printf("\n");
}
				if (bl) {
					rlp = pluckrack2(r, UBLANK, &rbs);
				} else  {
					rlp = pluckrack2(r, pl, &rbs);
				}
				*rlp = MARK;
				ASSERT(rlp != NULL);
				pl |= bl;
				w[ndx] = pl;
				sct.ts = lval(pl);
				sct.tbs = b->spaces[currow][curcol].b.f.lm * sct.ts;
				sct.wm =  b->spaces[currow][curcol].b.f.wm;
				sct.lms = b->spaces[currow][curcol].b.f.mls[m->dir];
				sct.play = 1;
				if ( b->spaces[currow][curcol].b.f.anchor & (m->dir + 1)) {
					sct.play += 1;
				}
			}
		}
DBG(DBG_GEN, "[%d]Gen gave id=%d, l=%c and rack ", ndx, curid, l2c(w[ndx])) {
	printlstr(r->tiles); printf("\n");
}
		if (gf(gaddag[curid])) {
			if (nldn(b, currow, curcol, m->dir, side)) {
/* here is where we have trouble. Check the other end. */
			    if ((pos > 0) || (nldn(b, currow + ndx * m->dir, curcol + ndx * (1 - m->dir), m->dir, 1))) {
				m->score = finalscore(sct);
				VERB(VNOISY, "at_b:") {
					printmove(m, pos);
				}
				/* record play */
				ASSERT(*mvsndx < MAXMVS);
				mvs[*mvsndx] = *m;
				fixmove( &(mvs[*mvsndx]), pos);
				*mvsndx += 1;
				movecnt++;
gmcnt++;
			    }
			}
		}
		cid = gc(gaddag[curid]);
		if (isroom(currow, curcol, m->dir, side)) {
			/* recurse */
DBG(DBG_GEN, "recurse 1 (%d, %d,%d, word, rack, id=%d)", m->row, m->col, pos, cid) {
	printf(" word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
			if (pos <= 0) {
				m->col -= (1 - m->dir);
				m->row -= m->dir;
			}
			movecnt += genallat_b(P, mvs, mvsndx, pos, cid, sct, depth+1, rbs);
			if (pos <= 0) {
				m->col += (1 - m->dir);
				m->row += m->dir;
			}
		} else {
}
		/* have to handle the ^ */
		if ((pos <= 0) && (SEPBIT & bitset[cid])) {
//		if ((pos <= 0) && (SEPBIT & bitset[curid]) && (sct.played > 0)) 
			if (nldn(b, currow, curcol, m->dir, -1) &&
				isroom(currow + dr*(prelen-1) , curcol + dc*(prelen-1), m->dir, 1)) {
				sepid = gotol(SEP, cid);
//				sepid = gotol(SEP, curid);
DBG(DBG_GEN, "sep at %d from %d with rack= ", sepid, cid) {
	printlstr(r->tiles); printf(" word= "); printlstr(w); printf("\n");
}
				cid = gc(gaddag[sepid]);
				if (cid == 0) continue;
DBG(DBG_GEN, "recurse 3 (%d, %d, 1, word, rack, id=%d", m->row, m->col, cid) {
	printf(" - word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
				movecnt += genallat_b(P, mvs, mvsndx, prelen, cid, sct, depth+1, rbs);
			} else {
DBG(DBG_GEN, "no room! no room! at %d %d (prelen=%d)dir=%d\n", currow, curcol, prelen, m->dir);
			}
		} else {
DBG(DBG_GEN, "no SEP at nid %d\n", cid);
		}
	}
	w[ndx] = '\0';
DBG(DBG_GEN, "[%d] genallat for %d,%d/%d returning %d moves\n", ndx, m->row, m->col, m->dir, movecnt);
	return movecnt;
}

/* iterates genallat over board. Allocates mvs for us.*/
int
genall_c(position_t *P, move_t **mvs, int *mvsndx)
{
	int r, c, dir, moves = 0;
	bs_t rbs;

	if (*mvs == NULL) {
		*mvs = (move_t *)malloc( sizeof(move_t) * MAXMVS);
		if (*mvs == NULL) {
			vprintf(VNORM, "ERROR: failed allocate moves array\n");
			return 0;
		}
	}
	bzero(*mvs, sizeof(move_t)*MAXMVS);
	*mvsndx = 0;
	rbs = lstr2bs(P->r.tiles);

	if (P->sc == -1) {
		P->sc = 0;
//		P->m = emptymove;
		P->m.row = STARTR; P->m.col = STARTC; P->m.dir = M_HORIZ;
		moves = genallat_c(P, *mvs, mvsndx);
//		moves = genallat_b(P, *mvs, mvsndx, 0, 1, newsct, 0, rbs);
DBG(DBG_GEN, "genall made %d start moves\n", moves);
		return moves;
	}

	P->m = emptymove;	

	for (dir = 0; dir < 2; dir++) {
		for (r = 0; r < BOARDY; r++) {
			for (c = 0; c < BOARDX; c++) {
				if (P->b.spaces[r][c].b.f.anchor) {
					P->m.row = r; P->m.col = c;
					P->m.dir = dir;

					moves += genallat_c(P, *mvs, mvsndx);
//					moves += genallat_b(P, *mvs, mvsndx, 0, 1, newsct, 0, rbs);
				}
			}
		}
	}
	ASSERT(moves == *mvsndx);
DBG(DBG_GEN, "genall made %d total moves (%d mvs)\n", moves, *mvsndx);
	return moves;
}

/* iterates genallat over board. Allocates mvs for us.*/
int
genall_b(position_t *P, move_t **mvs, int *mvsndx)
{
	int r, c, dir, moves = 0;
	bs_t rbs;

	if (*mvs == NULL) {
		*mvs = (move_t *)malloc( sizeof(move_t) * MAXMVS);
		if (*mvs == NULL) {
			vprintf(VNORM, "ERROR: failed allocate moves array\n");
			return 0;
		}
	}
	bzero(*mvs, sizeof(move_t)*MAXMVS);
	*mvsndx = 0;
	rbs = lstr2bs(P->r.tiles);

	if (P->sc == -1) {
		P->sc = 0;
		P->m.row = STARTR; P->m.col = STARTC; P->m.dir = M_HORIZ;
		moves = genallat_b(P, *mvs, mvsndx, 0, 1, newsct, 0, rbs);
DBG(DBG_GEN, "genall made %d start moves\n", moves);
		return moves;
	}

	P->m = emptymove;	

	for (dir = 0; dir < 2; dir++) {
		for (r = 0; r < BOARDY; r++) {
			for (c = 0; c < BOARDX; c++) {
				if (P->b.spaces[r][c].b.f.anchor) {
					P->m.row = r; P->m.col = c;
					P->m.dir = dir;
					
					moves += genallat_b(P, *mvs, mvsndx, 0, 1, newsct, 0, rbs);
				}
			}
		}
	}

DBG(DBG_GEN, "genall made %d total moves\n", moves);
	return moves;
}

/* greedy strategy move generator: returns the highest scoring move
 * made immediately from rack at given position.
 */
move_t
greedy(board_t *b, move_t *m, int pos, rack_t *r,  int nodeid, scthingy_t sct)
{
	move_t maxm = emptymove;
	move_t subm;
	int movecnt = 0;
	int curid = -1;
	int cid;
	int sepid;
 	letter_t *w = m->tiles;
	int ac = m->col;
	int ar = m->row;
	int ndx = 0;
	int prelen;
	int curcol = ac;
	int currow = ar;
	char *rlp = (char *)1;
	bs_t rbs = 0;
	bs_t bl = 0;
	bs_t bs = 0;
	register letter_t pl;
	int side;
	int dr = m->dir;
	int dc = 1 - m->dir;
	int ve = (ac-7)/7;
	int he = (ar-7)/7;

DBG(DBG_GREED, "at %d,%d(%-d) node=%d", ar,ac,pos, nodeid) {
	printf(" - word=\"");
	printlstr(w);
	printf("\", rack=\"");
	printlstr(r->tiles);
	printf("\"\n");
}
	updatescore(&sct);
	ndx = strlen(w);	/* depth */
	if (pos > 0) {
		side = 1;
		prelen = pos;
		currow += ndx * m->dir;
		curcol += ndx * (1 - m->dir);
	} else {
		side = -1;
		prelen = ndx + 1;
	}
	/* if NOT first, don't redo anchors */
DBG(DBG_GREED, "time to prune, ndx =%d anchor=%d\n", ndx, b->spaces[currow][curcol].b.f.anchor);
	if ((ndx > 0) && b->spaces[currow][curcol].b.f.anchor) {
		return maxm;
	}

	w[ndx+1] = '\0';

	while (rlp != NULL) {
DBG(DBG_GREED, "inline gen rbs=%x, bl=%d, bs=%x, curid=%d, rlp=%p lp=%c\n", rbs, bl,  bs, curid, rlp, l2c(w[ndx])) {

}
		pl = b->spaces[currow][curcol].b.f.letter;
		if (pl != '\0') {
DBG(DBG_GREED, "found %c on board at %d, %d\n", l2c(pl), currow, curcol);
			/* make sure we are still on the path */
			if (bitset[nodeid] & l2b(pl)) {
				w[ndx] = pl;
				rlp = NULL;
				curid = gotol(deblank(w[ndx]), nodeid);
				sct.ts = lval(pl);
				sct.tbs = sct.ts;
				sct.wm = 1;
				sct.play = 0;
				sct.lms = 1;
			} else {
				break;
			}
		} else {
			if (curid == -1) {
				rbs = lstr2bs(r->tiles);
				if (rbs & UBLBIT) bl = BB;
				curid = nodeid;
				if (bl) bs = ALLPHABITS & bitset[nodeid];
				else bs = rbs & bitset[nodeid];
				if (b->spaces[currow][curcol].b.f.anchor & (1+m->dir)) {
					bs &= b->spaces[currow][curcol].mbs[m->dir];
				}
DBG(DBG_GREED, "first (%d,%d)/%d bl=%x, rbs=%x, id=%d, bitset=%x mbs=%x bs=%x\n", currow, curcol, m->dir, bl, rbs, nodeid, bitset[nodeid], b->spaces[currow][curcol].mbs[m->dir], bs);
			} else {
				if (bl) *rlp = UBLANK;
				else *rlp = w[ndx];
DBG(DBG_GREED, "Pop %c at %d back to rack\n", l2c(w[ndx]), ndx);
			}
			if ((bs == 0) && (bl)) {
				bl = 0;
				bs = rbs & bitset[nodeid];
				if (b->spaces[currow][curcol].b.f.anchor & (1+m->dir)) {
					bs &= b->spaces[currow][curcol].mbs[m->dir];
				}
				curid = nodeid;
			}
			if (bs == 0) {
				rlp = NULL;
				w[ndx] = '\0';
				break;
			} else {
				pl = nextl(&bs, &curid);
				ASSERT(pl != 0);
DBG(DBG_GREED,"match %c bl=%x, node %d curid=%d rack=", l2c(pl),bl, nodeid, curid) {
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
				sct.lms = b->spaces[currow][curcol].b.f.mls[m->dir];
				sct.play = 1;
				if ( b->spaces[currow][curcol].b.f.anchor & (m->dir + 1)) {
					sct.play += 1;
				}
			}
		}
DBG(DBG_GREED, "Gen gave n=%d, id=%d, l=%c and rack ", ndx, curid, l2c(w[ndx])) {
	printlstr(r->tiles); printf("\n");
}
		if (gf(gaddag[curid])) {
			if (nldn(b, currow, curcol, m->dir, side)) {
/* here is where we have trouble. Check the other end. */
if ((pos > 0) || (nldn(b, currow + ndx * m->dir, curcol + ndx * (1 - m->dir), m->dir, 1))) {
				m->score = finalscore(sct);
				VERB(VVERB, " ") {
					printmove(m, pos);
				}
				if (m->score > maxm.score) {
					maxm = *m;
					fixmove(&maxm, pos);
				}
}
			}
		}
		cid = gc(gaddag[curid]);
		if (isroom(currow, curcol, m->dir, side)) {
			/* recurse */
DBG(DBG_GREED, "recurse 1 (%d, %d, %d, word, rack, id=%d)", m->row, m->col, pos, cid) {
	printf(" word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
			if (pos <= 0) {
				m->col -= 1 - m->dir;
				m->row -= m->dir;
			}
			subm = greedy(b, m, pos, r,  cid, sct);
			if (pos <= 0) {
				m->col += 1 - m->dir;
				m->row += m->dir;
			}
			if (subm.score > maxm.score) {
				maxm = subm;
			}
		}
		/* have to handle the ^ */
		if ((pos <= 0) && (SEPBIT & bitset[cid])) {
			if (nldn(b, currow, curcol, m->dir, -1) &&
				isroom(currow + dr*(prelen-1), curcol + dc*(prelen-1), m->dir, 1)) {
				sepid = gotol(SEP, cid);
DBG(DBG_GREED, "sep at %d from %d\n", sepid, cid);
				cid = gc(gaddag[sepid]);
				if (cid == 0) continue;
DBG(DBG_GREED, "recurse 3 (%d, %d, 1, word, rack, id=%d", m->row, m->col, cid) {
	printf(" - word=\""); printlstr(w);
	printf("\", rack=\""); printlstr(r->tiles);
	printf("\"\n");
}
				subm = greedy(b, m, prelen, r, cid, sct);
				if (subm.score > maxm.score) {
					maxm = subm;
				}
			} else {
DBG(DBG_GREED, "no room! no room! at %d %d dir=%d\n", currow, curcol, m->dir);
			}
		} else {
DBG(DBG_GREED, "no SEP at nid %d\n", cid);
		}
	}
	w[ndx] = '\0';

	DBG(DBG_GREED, "max move at level %d is ", ndx) {
		printmove(&maxm, pos);
	}
	return maxm;
}

/* mod to use genall_b */
/* like all ceo's the real work is delegated to others. */
int
veep_b(position_t *P, move_t *mvs, int mvcnt)
{
	int i;
	int bigm = 0;
	int maxsc = 0;

	for (i = 0; i < mvcnt; i++) {
		if (mvs[i].score > maxsc) {
			bigm = i;
			maxsc = mvs[i].score;
		}
	}
	makemove6(&(P->b), &(mvs[bigm]), 1, 0, &(P->r));
	P->m = mvs[bigm];
	P->stats.evals += mvcnt;
	P->mvndx = bigm;
	return maxsc;
}

/* 
 * genall_b variant.
 */
int
ceo2_b(board_t *gb)
{
	int totalscore = 0;
	int subscore;
	int bagpos = 0;
	int mvcnt;
	int mvsndx = 0;
	move_t *mvs = NULL;
	position_t P = startp;
	bs_t rbs;

	mvs = (move_t *)malloc( sizeof(move_t) * MAXMVS);
	if (mvs == NULL) {
		vprintf(VNORM, "ERROR: failed allocate moves array\n");
		return 0;
	}
	bzero(mvs, sizeof(move_t)*MAXMVS);

	P.m.row = STARTR; P.m.col = STARTC;
	fillrack(&(P.r), globalbag, &(P.bagndx));
	qsort(P.r.tiles, strlen(P.r.tiles), 1, lcmp);
	/* use genallat for start position. */

DBG(DBG_GREED, "genning all at %d, %d with rack ", P.m.row, P.m.col) {
	printlstr(P.r.tiles); printf("\n");
}
	rbs = lstr2bs(P.r.tiles);
	mvcnt = genallat_b(&P, mvs, &mvsndx, 0, 1, newsct, 0, rbs);

	while (mvcnt > 0) {
		totalscore += veep_b(&P, mvs, mvcnt);
		P.sc = totalscore;
		VERB(VNORM, "ceo2b score is %d for ", P.sc) {
			printmove(&(P.m), -1);
		}
		VERB(VVERB,"ceo2b ") {
			showboard(P.b, B_TILES);
		}
		VERB(VNOISY, "ceo2b ") {
			showboard(P.b, B_ANCHOR);
			showboard(P.b, B_HMLS);
			showboard(P.b, B_VMLS);
			showboard(P.b, B_HMBS);
			showboard(P.b, B_VMBS);
		}
		fillrack(&(P.r), globalbag, &(P.bagndx));
		qsort(P.r.tiles, strlen(P.r.tiles), 1, lcmp);
		mvsndx = 0;
		bzero(mvs, sizeof(move_t)*MAXMVS);
//		mvcnt = genall_b(&P, &mvs, &mvsndx);
//		mvcnt = genall_c(&P, &mvs, &mvsndx);
		mvcnt = genall_d(&P, &mvs, &mvsndx);
	}
	/* correct for leftover letters. */
	subscore = unbonus(&(P.r), globalbag, P.bagndx);
	if (subscore > 0) {
		VERB(VNORM, "LEFT: ") {
			printlstr(P.r.tiles);
			printf(" -%d\n", subscore);
		}
		totalscore -= subscore;
	}

	/* and that's the game, dude. */
	*gb = P.b;
	return totalscore;
}

/* the ceo uses a short-sighted greedy strategy to maximize his score.
 * board contains all moves, return value is final score.
 */
int
ceo(board_t *gb)
{
	int dir, row, col, mcnt = 1;
	int bagpos = 0;
	move_t m = emptymove;
	move_t maxm = emptymove;
	move_t gm = emptymove;
	rack_t r = emptyrack;
	int totalscore = 0;
	int subscore = 0;

	gm.row = STARTR; gm.col = STARTC;
	fillrack(&r, globalbag, &bagpos);
	qsort(r.tiles, strlen(r.tiles), 1, lcmp);
	/* first move is at start position. */
DBG(DBG_GREED, "getting greedy at %d, %d with rack ", gm.row, gm.col) {
	printlstr(r.tiles); printf("\n");
}
	maxm = greedy(gb, &gm, 0, &r, 1, newsct);
	makemove6(gb, &maxm, 1, 0, &r);
	totalscore = maxm.score;

	while (strlen(maxm.tiles) > 0) {
VERB(VNORM, "%d:", mcnt) {
	printmove(&maxm, -1);
}
VERB(VVERB,"ceo ") {
	showboard(*gb, B_TILES);
}
VERB(VVERB, "ceo ") {
	showboard(*gb, B_ANCHOR);
	showboard(*gb, B_HMLS);
	showboard(*gb, B_VMLS);
	showboard(*gb, B_HMBS);
	showboard(*gb, B_VMBS);
	showboard(*gb, B_HMNID);
	showboard(*gb, B_VMNID);
}
		mcnt++;
		maxm = emptymove;
		fillrack(&r, globalbag, &bagpos);
		qsort(r.tiles, strlen(r.tiles), 1, lcmp);
		for (dir = 0; dir < 2; dir++) {
			for (row = 0; row < BOARDY; row++) {
				for (col = 0; col < BOARDX; col++) {
					if (gb->spaces[row][col].b.f.anchor) {
						gm = emptymove; gm.dir=dir;
						gm.row = row; gm.col=col;
	DBG(DBG_GREED, "getting greedy at %d, %d with rack ", gm.row, gm.col) {
		printlstr(r.tiles); printf("\n");
	}
						m = greedy(gb, &gm, 0, &r, 1, newsct);
						if (m.score > maxm.score) {
							maxm = m;
						}
					}
				}
			}
		}
		totalscore += maxm.score;

		makemove6(gb, &maxm, 1, 0, &r);
	}
	/* correct for leftover letters. */
	subscore = unbonus(&r, globalbag, bagpos);
	if (subscore > 0) {
		VERB(VNORM, "LEFT: ") {
			printlstr(r.tiles);
			printf(" -%d", subscore);
		}
		totalscore -= subscore;
	}

	/* and that's the game, dude. */
	return totalscore;
}

/*
 * used lah, but skips levels.
 */
int
jump(position_t *P) {
{
	int mcnt = 0;
	P->sc = -1;

	while (lah(P, 0, level)) {
		position_t *cP = P;
		while (cP != NULL) {
			mcnt++;
			VERB(VNORM, "jumpy score is %d for ", cP->sc) {
				printmove(&(cP->m), -1);
			}
			*P = *cP;
			cP = cP->next;
		}
	}
DBG(DBG_LAH, "jump mv %d score =%d\n",mcnt, P->sc);
	}

	return P->sc;
}

/* creep uses lah, it only does 1 move/iteration.
*/
int
creep(position_t *P)
{
	int mcnt = 0;
	P->sc = -1;
	int rv = 1;
	hrtime_t fore, aft;

	fore = gethrtime();
	rv = lah(P, 0, level);
	aft = gethrtime();
	while (rv) {
mcnt += P->stats.moves;
		P->stats.evtime += aft - fore;
		P->depth++;
		printpos(*P);
DBG(DBG_LAH, "creep chain is:") {
	position_t *cP = P;
	while (cP != NULL) {
		printmove(&(cP->m), -1);
		cP = cP->next;
	}
}
DBG(DBG_LAH, "creep mv %dscore =%d P->next = %p\n", P->depth, P->sc,  P->next);
		fore = gethrtime();
		rv = lah(P, 0, level);
		aft = gethrtime();
	}
vprintf(VVERB, "total moves is %d\n", mcnt);
	return P->sc;
}

/*
 * at last. look-ahead. needs to know limit, depth, position.
 * uses genall.  Greedy when limit is reached.
 * not a strat itself, but used by them (like greedy). 
 * returns 0 when there are no more moves.
 * newP is allocated.
 */
int
lah(position_t *P, int depth, int limit)
{
	move_t *mvs = NULL;
	int mvsndx = 0;
	position_t *newP, maxP, iP;
	int maxsc = -1000000;		// lower than any possible score.
	int i; int rv; int maxrv; int maxi;
	hrtime_t fore, aft;

	fillrack(&(P->r), globalbag, &(P->bagndx));
	qsort(P->r.tiles, strlen(P->r.tiles), 1, lcmp);
DBG(DBG_LAH, "enter depth=%d limit=%d rack=", depth, limit) {
	printlstr(P->r.tiles); printf("\n");
}
	P->m = emptymove;
//	P->mvcnt = genall_b(P, &mvs, &mvsndx);
//	P->mvcnt = genall_c(P, &mvs, &mvsndx);
	P->mvcnt = genall_d(P, &mvs, &mvsndx);
	P->stats.moves += P->mvcnt;
	if (depth > P->stats.maxdepth) P->stats.maxdepth = depth;
	if (P->mvcnt > P->stats.maxwidth) P->stats.maxwidth = P->mvcnt;

DBG(DBG_LAH, "[%d]genall gave %d (%d)moves\n",depth, P->mvcnt, mvsndx);
	if (P->mvcnt == 0) {
		/* there were no more moves. EOG */
		P->sc -= unbonus(&(P->r), globalbag, P->bagndx);
		P->next = NULL;
		free(mvs); mvsndx = 0;
		return 0;
	}
	if (depth >= limit) {
ASSERT(mvsndx == P->mvcnt);
		int score = veep_b(P, mvs, P->mvcnt);
		P->sc += score;
		if (score > P->stats.wordhs) P->stats.wordhs = score;
		P->next = NULL;
		free(mvs); mvsndx = 0;
DBG(DBG_LAH, "[%d]veep found move =", depth) {
	printmove(&(P->m), -1);
}
		return 1;
	}
	/* still looking ahead. recursive part. */
	ASSERT(depth < limit);
	newP = malloc(sizeof(position_t));
	P->next = newP;

	for (i = 0; i < P->mvcnt; i++) {
DBG(DBG_LAH, "[%d]recurse with move %d=", depth,i) {
	printmove(&(mvs[i]), -1);
}
		iP = *P;
		makemove6(&(iP.b), &(mvs[i]), 1, 0, &(iP.r));
		iP.m = mvs[i];
		iP.mvndx = i;
		iP.sc += iP.m.score;
		if (iP.m.score > iP.stats.wordhs) iP.stats.wordhs = iP.m.score;
		*newP = iP; newP->next = NULL;
		newP->stats.moves = 0;
		fore = gethrtime();
		rv = lah(newP, depth+1, limit);
		aft = gethrtime();
		newP->stats.evtime = aft - fore;
//		P->stats.moves += newP->mvcnt;
		P->stats.moves += newP->stats.moves;
		
		P->stats.evtime += newP->stats.evtime;
		if (newP->stats.maxdepth > P->stats.maxdepth)
			P->stats.maxdepth = newP->stats.maxdepth;
		if (newP->sc > maxsc) {
			maxP = iP;
			maxsc = newP->sc;
			maxrv = rv;
			maxP.mvndx = i;
		}
	}
	// in the case where next move is no move, free maxP.
	if (maxrv == 0) {
		P->next = NULL;
		free(newP);
	}
	*P = maxP;
//	P->m = mvs[maxi];
DBG(DBG_LAH, "[%d]returning with move=", depth) {
	printmove( &(maxP.m), -1);
	showboard(P->b, B_TILES);
}
	free(mvs); mvsndx = 0;
	return 2;
}

/* do this later... */
#ifdef DEBUG
/* here we indulge in some paranoia. */
void
verify()
{
	int savev = verbose;
	/* normally verify is quiet. */
	if (verbose <= VNOISY) {
		verbose = VSHH;
	}
	{
		/* ffb and popc */
		uint32_t v; int rv; int i;

		v = 0x0; rv = ffb(v); ASSERT(rv == 0);
		v = 0x1; rv = ffb(v); ASSERT(rv == 1);
		v = 0xFFFFFFFF; rv = ffb(v); ASSERT(rv == 1);
		v = 0xFFFF0000; rv = ffb(v); ASSERT(rv == 17);
		v = 0xF0F0F0F0; rv = ffb(v); ASSERT(rv == 5);
		v = 0x55555555; rv = ffb(v); ASSERT(rv == 1);
		v = 0xAAAAAAAA; rv = ffb(v); ASSERT(rv == 2);
		for (i=0; i < 32; i++) {
			v = 0x01 << i;
			rv = ffb(v);
			ASSERT(rv == (i+1));
		}
		v = 0x0; rv = popc(v); ASSERT(rv == 0);
		v = 0x1; rv = popc(v); ASSERT(rv == 1);
		v = 0xFFFFFFFF; rv = popc(v);
		ASSERT(rv == 32);
		v = 0xFFFF0000; rv = popc(v); ASSERT(rv == 16);
		v = 0xF0F0F0F0; rv = popc(v); ASSERT(rv == 16);
		v = 0x55555555; rv = popc(v); ASSERT(rv == 16);
		v = 0xAAAAAAAA; rv = popc(v); ASSERT(rv == 16);
		for (i=0; i < 32; i++) {
			v = 0x01 << i;
			rv = popc(v);
			ASSERT(rv == 1);
		}
		rv = popc (ALLPHABITS << 31);
		ASSERT(rv == 1);
		v = ALLPHABITS;
		rv = popc (v << 31);
		ASSERT(rv == 1);
		v = bitset[1]; i = 1;
		rv = popc (v << (32-1));
		ASSERT(rv == 1);
		rv = popc (v << (32-i));
		ASSERT(rv == 1);
	}
	{
		/* test ffs */
		bs_t ts; int rv; int i;
		bs_t *tbs;

		for (i = 0; i < 32; i++) {
			ts = 0x01 << i;
			rv = ffs(ts);
			ASSERT(rv == i+1);
		}
		for (i = 0; i < 32; i++) {
			ts = 0xFFFFFFFF << i;
			rv = ffs(ts);
			ASSERT(rv == i+1);
		}
		ts = 0xFF0000FF;
		tbs = &ts;
		rv = ffs(*tbs);
		ASSERT(rv == 1);
	}
	{
		/* test nextl */
		bs_t ts; int tid; letter_t rv; int i;
		ts = 0xFFFFFFFF; tid = 1;
		rv = nextl(&ts, &tid);
		ASSERT(rv == 1);
		ASSERT(ts == 0xFFFFFFFE);
		ASSERT(tid == 1);
		ts = (0x01 << 13);
		rv = nextl(&ts, &tid);
		ASSERT(rv == 14);
	}
	/* basic struct tests */
	{
		space_t tsp;
		move_t tmv;

		ASSERT(sizeof(space_t) == (5 * sizeof(uint32_t)));
		tsp.b.all = 0xFFFFFFFF;
		ASSERT(tsp.b.f.mls[0] == 0xFF);
		ASSERT(tsp.b.f.mls[1] == 0xFF);
		ASSERT(tsp.b.f.lm == 3);
		ASSERT(tsp.b.f.wm == 3);
		ASSERT(tsp.b.f.anchor == 3);
		ASSERT(tsp.b.f.pad == 3);
		ASSERT(sizeof(move_t) == 20);
	}
	/* test emptyboard. assure symmetry */
	{
		int i,j;
		int sumwm = 0, sumlm = 0;
		board_t tb = emptyboard;

		for (i=0;i<BOARDY;i++) {
			for (j=0;j<BOARDX;j++) {
				sumwm += tb.spaces[i][j].b.f.wm;
				sumlm += tb.spaces[i][j].b.f.lm;
				ASSERT(tb.spaces[i][j].b.f.lm == tb.spaces[i][MAXR-j].b.f.lm);
				ASSERT(tb.spaces[i][j].b.f.lm == tb.spaces[MAXR-i][MAXC-j].b.f.lm);
				ASSERT(tb.spaces[i][j].b.f.lm == tb.spaces[MAXR-i][j].b.f.lm);
				ASSERT(tb.spaces[i][j].b.f.wm == tb.spaces[i][MAXC-j].b.f.wm);
				ASSERT(tb.spaces[i][j].b.f.wm == tb.spaces[MAXR-i][MAXC-j].b.f.wm);
				ASSERT(tb.spaces[i][j].b.f.wm == tb.spaces[MAXR-i][j].b.f.wm);

			}
		}
		ASSERT(sumwm == B_TTLWM);
		ASSERT(sumlm == B_TTLLM);
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
		ASSERT( (rv!=0));
		strcpy(s, "A7:PLY");
		rv = parsemove(s, &tm, 0);
VERB(VNOISY, "verify parsemove: rv=%d, dir=%d, row=%d col=%d lcount=%d tiles=", rv, tm.dir, tm.row, tm.col, tm.lcount) {
printlstr(tm.tiles); printf("\n");
}
		ASSERT( (rv==0) && (tm.dir == M_VERT) && (tm.col == 0) && (tm.row == 6));
	}
	{
		/* finals. */
		int nid; int bs;

		nid =1; bs = 0;
		bs = finals(nid);
vprintf(VNOISY, "finals for node %d are %x\n", nid, bs);
		ASSERT(bs == 0);
		nid =126; bs = 0;
		bs = finals(nid);
vprintf(VNOISY, "finals for node %d are %x\n", nid, bs);
		ASSERT(bs == 1);
	}
	{
		/* ndn = next door neighbor */
		board_t tb; int r; int c; int d; int s;
		int rv;
		tb = emptyboard;
		tb.spaces[7][7].b.f.letter = c2l('A');

		r = 7; c = 7; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 7; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 7; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 7; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 0; c = 0; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 0; c = 0; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 0; c = 0; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv < 0);
		r = 0; c = 0; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv < 0);

		r = 14; c = 14; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv < 0);
		r = 14; c = 14; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv < 0);
		r = 14; c = 14; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 14; c = 14; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 6; c = 7; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
//:printf("got %d expected %d from %d,%d/%d/%d\n", rv, c2l('A'), r,c,d,s);
		r = 6; c = 7; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == c2l('A'));
		r = 6; c = 7; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 6; c = 7; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 8; c = 7; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 8; c = 7; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 8; c = 7; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == c2l('A'));
		r = 8; c = 7; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 7; c = 6; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == c2l('A'));
		r = 7; c = 6; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 6; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 6; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);

		r = 7; c = 8; d = M_HORIZ; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 8; d = M_VERT; s = 1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 8; d = M_VERT; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == 0);
		r = 7; c = 8; d = M_HORIZ; s = -1;
		rv = ndn(&tb, r, c, d, s);
		ASSERT(rv == c2l('A'));
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
	{
		/* score. simple cases, only 1 word */
		move_t tm; board_t tb = emptyboard; int pt = 0; int rv;
		int i, j, sum1, sum2;
		char ts[16];

		sum1 = 0;  sum2 = 0;
		strcpy(ts,"ZAP");
		c2lstr(ts, tm.tiles, 0); tm.row=0; tm.col = 0; tm.dir= M_HORIZ;
		tm.lcount = 3;
		for (i=0; i < 13; i++) {
			for (j = 0; j<13; j++) {
				tm.row = i; tm.col = j; tm.dir=M_HORIZ;
				sum1 += score2(&tm, &tb, 1);
				tm.dir = M_VERT;
				sum2 += score2(&tm, &tb, 1);
			}
		}
		ASSERT(sum1 == sum2);

		strcpy(ts, SC_LOWL);
		c2lstr(ts, tm.tiles, 0); tm.row=SC_LOWR; tm.col = SC_LOWC;
		tm.dir= M_HORIZ; tm.lcount = 2;
		rv = score2(&tm, &tb, 1);
		ASSERT(rv == SC_LOS);
		strcpy(ts, SC_HIWL);
		c2lstr(ts, tm.tiles, 0); tm.row=SC_HIWR; tm.col = SC_HIWC;
		tm.dir= M_HORIZ; tm.lcount = 15;
		rv = score2(&tm, &tb, 1);
vprintf(VVERB, "%s at %d,%d (dir=%d) scores %d\n",ts, tm.row, tm.col, tm.dir, rv);
		ASSERT(rv == SC_HIS);
	}
	{
		/* movelen */
		board_t tb; move_t tm; int rv; int pt;
		tb = emptyboard;

		tm.row =7; tm.col=7; tm.dir = M_HORIZ;
		strcpy(tm.tiles, "foobar"); pt = 1;

		rv = movelen(&tb, &tm, pt);
		ASSERT(rv == 6);
		pt = 0;
		rv = movelen(&tb, &tm, pt);
		ASSERT(rv == 6);

		tb.spaces[7][6].b.f.letter = c2l('A');
		tb.spaces[7][7].b.f.letter = c2l('B');
		tb.spaces[7][8].b.f.letter = c2l('C');

		strcpy(tm.tiles, "XABCY"); pt =1;
		rv = movelen(&tb, &tm, pt);
		ASSERT(rv == 5);
		strcpy(tm.tiles, "XYz"); tm.row=7;tm.col=5;pt =0;
		rv = movelen(&tb, &tm, pt);
VERB(VVERB, "rv=%d for %d,%d %s pt=%d tiles=", rv, tm.row, tm.col, tm.dir == M_HORIZ ? "horiz" : "vert", pt) {
	printlstr(tm.tiles); printf("\n");
}
		ASSERT(rv == 6);
	}
	{
		/* isroom. */
		int tr, tc, td, ts, rv;

		tr=7;tc=7;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=7;tc=7;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=7;tc=7;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=7;tc=7;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);

		tr=0;tc=0;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=0;tc=0;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=0;tc=0;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);
		tr=0;tc=0;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);

		tr=14;tc=14;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);
		tr=14;tc=14;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);
		tr=14;tc=14;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=14;tc=14;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);

		tr=0;tc=1;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=0;tc=1;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=0;tc=1;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);
		tr=0;tc=1;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);

		tr=13;tc=13;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=13;tc=13;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=13;tc=13;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=13;tc=13;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);

		tr=7;tc=14;td=M_HORIZ;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 0);
		tr=7;tc=14;td=M_VERT;ts=1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=7;tc=14;td=M_VERT;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
		tr=7;tc=14;td=M_HORIZ;ts=-1;
		rv = isroom(tr,tc,td,ts);
		ASSERT(rv == 1);
	}
	{
		/* also isroom, in a different way */
		int tr, tc, td, ts, rv;

		td = M_HORIZ;ts=-1; rv = 0;
		for (tr =0; tr < BOARDY; tr++) {
			for (tc =0; tc < BOARDX; tc++) {
				rv += isroom(tr,tc, 0, -1);
				rv += isroom(tr,tc, 1, -1);
				rv += isroom(tr,tc, 0, 1);
				rv += isroom(tr,tc, 1, 1);
			}
		}
		ASSERT(rv == ((15*15*4) - (4*15)));
	}
	{
		/* other constants */
		ASSERT(g_cnt == GDBYTES / 4);
		// more later.
	}
	{
		/* lookup */
		char tw[25]; char tlw[25]; int l; int nid; int rv;

		strcpy(tw, "AA"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == 1);

		strcpy(tw, "??"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == TWOLW);
		strcpy(tw, "???"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == THREELW);
		strcpy(tw, "????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == FOURLW);
		strcpy(tw, "?????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == FIVELW);
		strcpy(tw, "??????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == SIXLW);
		strcpy(tw, "???????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == SEVENLW);
		strcpy(tw, "????????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == EIGHTLW);
		strcpy(tw, "?????????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == NINELW);
		strcpy(tw, "??????????"); c2lstr(tw, tlw, 0); l = strlen(tw); nid = 1;
		rv = bs_lookup(l, tlw, nid);
		ASSERT(rv == TENLW);
	}
	{
		/* anagram */
		char tw[25]; char tl[25]; int rv;

		strcpy(tw, "AA"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 1);
		strcpy(tw, "PLY"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 1);
		strcpy(tw, "LETTERS"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 76);
		strcpy(tw, "LETTERS"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 76);
		strcpy(tw, "??"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == TWOLW);
		strcpy(tw, "???"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == (TWOLW + THREELW));
		strcpy(tw, "??????"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == (TWOLW + THREELW + FOURLW + FIVELW + SIXLW));
		strcpy(tw, "??????????"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == (TWOLW + THREELW + FOURLW + FIVELW + SIXLW + SEVENLW + EIGHTLW +NINELW + TENLW));
		strcpy(tw, "ZZZ"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 0);
		strcpy(tw, "ANAGRAM"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == 39);
		strcpy(tw, "ABCDEFGHIJKLMNOPQRSTUVWXYZ"); c2lstr(tw, tl, 0);
		rv = anagramstr(tl, 0);
		ASSERT(rv == ATOZANA);
		
	}
	{
		/* rackem. */
		rack_t r1; rack_t r2; bs_t bs; letter_t L;
		c2lstr("ABCDEFG", r1.tiles, UNPLAYED); bs = 0; L = c2l('A');
		rackem(&r1, &r2, &bs, L);
		ASSERT(strlen(r2.tiles) == 6);
		ASSERT( !(l2b(L) & bs));
		L = c2l('G');
		rackem(&r1, &r2, &bs, L);
		ASSERT(strlen(r2.tiles) == 6);
		ASSERT( !(l2b(L) & bs));
		c2lstr("ABMMMYZ", r1.tiles, UNPLAYED); bs = 0; L = c2l('M');
		rackem(&r1, &r2, &bs, L);
		ASSERT(strlen(r2.tiles) == 6);
		ASSERT( (l2b(L) & bs));
	}

	if (verbose != savev) {
		verbose = savev;
	}
	vprintf(VVERB, "finished verify!\n");
}
#endif /* DEBUG */

#define WS	" \n\t"
/* if this function retuns NULL, it should not be called again. */
char *
getnextarg(int argc, char **argv, int *optind)
{
	static char *buf = NULL;
	char *ap = NULL;
	/* read file first, if any */
	if (infile != NULL) {
		int fd = -1;
		off_t len;
		int rv;
		fd = open(infile, O_RDONLY);
		infile = NULL;
		if (fd < 0) {
			perror("open");
			goto end;
		}
		len = lseek(fd, 0, SEEK_END);
		if (len < 0) {
			perror("lseek");
			goto end;
		}
		(void) lseek(fd, 0, SEEK_SET);
		buf = malloc(len+2);
		if (buf == NULL) {
			perror("malloc");
			goto end;
		}
		rv = read(fd, buf, len);
		if (rv < 0) {
			perror("read");
			goto end;
		} else if (rv != len) {
			printf("error reading move file, only got %d out of %d bytes\n", rv, (int)len);
			len = rv;
		}
end:
		infile = NULL;
		close(fd);
		if (buf != NULL) {
			buf[len]='\0';
			ap = strtok(buf, WS);
			if (ap == NULL) {
				free(buf); buf = NULL;
			} else {
				return ap;
			}
		}
	}
	if (buf != NULL) {
		ap = strtok(NULL, WS);
		if (ap == NULL) {
			free(buf);
			buf = NULL;
		} else {
			return ap;
		}
	}
	if (*optind < argc) {
		ap = argv[*optind];
		*optind += 1;
		return ap;
	}
	return NULL;
}

uint32_t
parsedbg(char *arg)
{
	unsigned long rv; char *p;
	int i; uint32_t flags = 0;
	errno = 0;

	if(arg == NULL) return flags;
	rv = strtoul(arg, &p, 16);

	if ((*p == '\0') && (rv != 0) && (errno == 0)) {
		flags = rv;
		return flags;
	}
	if (strcasecmp(arg, "all") == 0) {
		flags = DBG_ALL;
		return flags;
	}
	if (strcasecmp(arg, "none") == 0) {
		flags = 0;
		return flags;
	}
	for (i = 0; i < 32; i++) {
		if (! strcasecmp(arg, dbgs[i])) {
			flags |= 0x1LU << i;
			return flags;
		}
	}
	vprintf(VNORM, "unknown debug option %s\n", arg);
	return 0;
}

#define ACT_LOOKUP	0x001
#define	ACT_ANAGRAM	0x002
#define ACT_SCORE	0x004
#define ACT_MOVE	0x008
#define ACT_PLAYTHRU	0x010
#define ACT_GEN		0x020
#define ACT_STRAT	0x040

#define STRAT_GREEDY	1
#define STRAT_GREED2	2
#define STRAT_GREED2B	3
#define STRAT_LAH1	4
#define STRAT_CREEP	5
#define	STRAT_JUMP	6

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
	char *argstr = NULL;
	int totalscore = 0;
	hrtime_t start, end, totaltime;
	uint64_t evals = 0;

        while ((c = getopt(argc, argv, "LASMGPI:T:n:b:B:D:vqstd:o:R:")) != -1) {
                switch(c) {
		case 'n':
			level = atoi(optarg);
			break;
		case 't':
			dotimes = 1;
#ifdef DEBUG
vprintf(VNORM, "Warning: -t with DEBUG build: data unreliable.\n");
#endif
			break;
		case 'T':
			strat = atoi(optarg);
			action |= ACT_STRAT;
			break;	
		case 'I':
			infile = optarg;
			break;
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
			dflags |= parsedbg(optarg);
DBG(DBG_DBG, "set dflags to 0x%lX\n", dflags);
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
                        dostats++;
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
	DBG(DBG_STAT, "using stat level %d\n", dostats);
	vprintf(VVERB, "Program version %s.%d\n", VER, REV);
#ifdef DEBUG
	verify();
#endif
	sb = startboard;
	/* use the rest of the command line as words. */
	if (action & ACT_SCORE) doscore = 1;
	while ((argstr = getnextarg(argc, argv, &optind)) != NULL) {
		move_t argmove;
		char *w;
		int sc, len;
		len = strlen(argstr);

		argmove = emptymove;
DBG(DBG_MAIN, "actions %d on arg %s\n", action, argstr);
		rv = parsemove(argstr, &argmove, JUSTPLAY);

		if (rv != 0) {
			vprintf(VNORM, "skipping non-parsable move %s\n", argstr);
			continue;
		}
		if (action & ACT_LOOKUP) {
			rv = bs_lookup(argmove.lcount, argmove.tiles, 1);
			if (rv > 0) {
				char *filled = strdup(argmove.tiles);
				l2cstr(argmove.tiles, filled);
				vprintf(VNORM, "%s matched %d  words\n", argstr, rv);
			} else {
				errs++;
				vprintf(VNORM, "%s not in dictionary\n", argstr);
			}
		}
		if (action&ACT_ANAGRAM) {
			vprintf(VNORM, "anagrams of %s are:\n", argstr);
			anas = anagramstr(argmove.tiles, action&ACT_SCORE);
			vprintf(VNORM, "created %d anagrams of %s\n", anas, argstr);
		}
		if (action == ACT_SCORE) {
			if (! (action & ACT_PLAYTHRU)) {
				argmove.lcount = movelen(&sb, &argmove, 0);
			}
			sc = score2(&argmove, &sb, action&ACT_PLAYTHRU);
			totalscore += sc;
			vprintf(VNORM, "%s scores %d\n", argstr, sc);
		}
		if (action&ACT_MOVE) {
			makemove6(&sb, &argmove, action&ACT_PLAYTHRU, 0, NULL);
			VERB(VNORM, "results of move:\n") {
				showboard(sb, B_TILES);
			}
			VERB(VNOISY, "all data") {
				showboard(sb, B_HMLS);
				showboard(sb, B_VMLS);
				showboard(sb, B_HMBS);
				showboard(sb, B_VMBS);
				showboard(sb, B_HMNID);
				showboard(sb, B_VMNID);
				showboard(sb, B_ANCHOR);
			}
		}
		if (action & ACT_GEN) {
			move_t *mvs = NULL;
			int mvsndx = 0;
			position_t gP = startp;
			strcpy(gP.r.tiles, argmove.tiles);
			gP.m = argmove;
			gP.m.tiles[0] = '\0';
			qsort(gP.r.tiles, strlen(gP.r.tiles), 1, lcmp);
			moves = genall_b(&gP, &mvs, &mvsndx);
			VERB(VVERB, "moves:") {
				int i;
				for (i = 0; i< mvsndx; i++) {
					printmove(&(mvs[i]), -1);
				}
			}
			vprintf(VNORM, "gen %d moves from %s\n", moves, argstr);
			free(mvs);
		}
	} /* end while args */

	/* these actions don't need move args, they use bags and racks. */
	if (action&ACT_STRAT) {
		switch (strat) {
		case STRAT_GREEDY:
			if (dotimes) start = gethrtime();
			totalscore = ceo(&sb);
			if (dotimes) end = gethrtime();
			VERB(VVERB, "final board:\n") {
				showboard(sb, B_TILES);
			}
			break;
		case STRAT_GREED2:
			vprintf(VNORM, "GREED2 is defunct\n");
			break;
		case STRAT_GREED2B:
			if (dotimes) start = gethrtime();
			totalscore = ceo2_b(&sb);
			if (dotimes) end = gethrtime();
			VERB(VVERB, "final board:\n") {
				showboard(sb, B_TILES);
			}
			break;
		case STRAT_LAH1:
			startp.sc = -1;
			if (dotimes) start = gethrtime();
			totalscore = lah(&startp, 0, level);
			if (dotimes) end = gethrtime();
			VERB(VVERB, "final board:\n") {
				showboard(startp.b, B_TILES);
			}
			break;
		case STRAT_CREEP:
			if (dotimes) start = gethrtime();
			totalscore = creep(&startp);
			if (dotimes) end = gethrtime();
			VERB(VVERB, "final board:\n") {
				showboard(startp.b, B_TILES);
			}
			break;
		case STRAT_JUMP:
			if (dotimes) start = gethrtime();
			totalscore = jump(&startp);
			if (dotimes) end = gethrtime();
			VERB(VVERB, "final board:\n") {
				showboard(startp.b, B_TILES);
			}
			break;
		}
	}
	if (dotimes) {
		totaltime = end - start;
vprintf(VNORM, "elapsed time is %lld nsec (%lld sec)\n", totaltime, totaltime/1000000000);
	}
	STAT(STLOW, "%llu moves in %llu nsec = %llu ns/m\n", startp.stats.moves, startp.stats.evtime,  startp.stats.evtime / startp.stats.moves);
	if (totalscore > 0)
		vprintf(VNORM, "total score is %d\n", totalscore);
vprintf(VVERB, "global move count = %lu\n", gmcnt);
	if (errs) {
		return -errs;
	} else {
		return anas;
	}
}
