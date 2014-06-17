
/*
 * program to do a deep search on a scrabble solitaire game.
 */

/* most includes are in deeper.c. */
#include <sys/types.h>
#include <assert.h>
#include <stdint.h>

/* just in case */
#define	VER	"0.4.0"

/* turns out gethrtime is not standard */
#if !defined(__sun)
typedef uint64_t hrtime_t;
#else
#define	HRTIME
#endif

/* debugging */
/*
 * the std assert() function is actually a macro, gated by NDEBUG.
 * since -g doesn't define anything for us, we have to use DEBUG and
 * reverse the sense.
 * I like my DBG macro trick. Note: dflags is a global, set by main.
 * Can't quite do it with assert... so far.
 */
#ifdef DEBUG
#define	ASSERT(x)	assert(x)
#define DBG(f, fmt, ...)                   \
        if ((((f)&dflags)==(f)) ? (printf("%s:",__func__) + printf(fmt, ##__VA_ARGS__)) : 0)
#else	/* DEBUG */
#define	ASSERT(x)
#define DBG(f, fmt, ...)	\
	if (0)
#endif	/* DEBUG */

/* add more as needed */
#define	DBG_MAIN	0x00000001	// high-level stuff
#define	DBG_DICT	0x00000002	// dictionary problems
#define DBG_INIT	0x00000004	// when init fails
#define DBG_BAG		0x00000008
#define DBG_STATS	0x00000010	// print out statistic debug info
#define DBG_ANA		0x00000020	// dict ops
#define DBG_LOOK	0x00000040	// dict ops
#define DBG_SCORE	0x00000080	// scoring
#define DBG_MLS		0x00000100	// letter move score stuff
#define DBG_ARGS	0x00000200	// parsing and stuff
#define DBG_RACK	0x00000400	// rack parsing and handling
#define DBG_GOON	0x00000800	// first cut at movegen
#define DBG_GEN		0x00001000	// other half of movegen
#define DBG_MATCH	0x00002000	// match (iterator)
#define DBG_DBG		0x40000000	// debugger: debug thyself.
#define DBG_ALL		0x7FFFFFFF	// extremely noisy
#define DBG_NONE	0x80000000	// doesn't match anything

/* revisit: wrap or otherwise mangle to avoid syntax error in stmts. */
#define vprintf(lvl, fmt,...) \
	if (verbose >= (lvl)) printf(fmt, ## __VA_ARGS__)

#define VERB(lvl, fmt, ...)	\
        if (( verbose >= lvl) ? 1 + printf(fmt, ##__VA_ARGS__) : 0)

/* verbosity levels, 0-9 (and silent) */
#define VSHH	-1	// dummy: don't say anything
#define VNORM	0	// useful, informative, concise.
#define VVERB	1	// verbose
#define VNOISY	2	// run off at the mouth a little
#define VDUMP	5	// tell me EVERYTHING
#define VOMG	9	// avalanche!!!!

/* general game constants */
#define BINGOBONUS	50
#define	RACKSIZE	7
#define	BOARDSIZE	15
#define	BOARDX		BOARDSIZE
#define	BOARDY		BOARDSIZE
#define STARTR		7
#define STARTC		7
char coltags[BOARDX+1] = "ABCDEFGHIJKLMNO";

/* gaddag stuff */
#define DFNEND  ".gaddag"	// dict file name ending
#define BSNEND  ".bitset"	// bitset file name ending
#define DDFN    "ENABLE"	// default dict file name

typedef uint32_t gn_t;		// gaddag node
typedef uint32_t bs_t;		// bitset

#define UBLANK	27		// unplayed blank (Z+1) '['
#define BB	0x20		// played Blank Bit
#define MARK	28		// internal place holder
#define SEP	30		// gaddag seperator, '^' (must be highest)

#if __BYTE_ORDER == 12345
#define gs(n)	((n)&0x80000000)
#define gf(n)	((n)&0x40000000)
#define gl(n)	(((n)>>24)&0x3F)
#define gc(n)	(__builtin_bswap32(n)>>8)
#else	/* "NORMAL" */
#define gc(n)	((n)>>8)	// first child index
#define gs(n)	((n)&0x80)	// have more sibs
#define gl(n)	((n)&0x3F)	// node letter value
#define gf(n)	((n)&0x40)	// final = end of word
#endif

#define is_pblank(n)	((n) & BB) 	// is this a played blank
#define is_ublank(n)	((n)==UBLANK)	// unplayed blank
#define is_blank(n)	(is_pblank(n)||is_ublank(n))
#define is_rvalid(l)	((l)<=UBLANK)	// A-Z, unplayed blank, NULL
#define is_bvalid(l)	(((l) & ~BB) <= UBLANK) // A-Z, played blank, NULL

/* cvt a letter to a char. Assumes is_bvalid(l) is true */
#define l2c(l)		(((l)==UBLANK) ? '?' : ((l)|0x40))
/* cvt an uppercase char to a letter.  A-Z only, no blanks */
#define C2l(C)	((C)&0x1F)
/* general case. A-Z, a-z, ? */
#define c2l(c)	(((c)=='?') ? UBLANK : ((c)&0x3F))
#define UNPLAYED	0
#define	PLAYED		1

#define	gl2l(l)		(l)
#define blankgl(gl)	(gl2l(gl)|BB)
#define deblank(l)	((l) & ~BB)

/* optimized bit twiddling. */
#if !defined(__sun)
#define	ffb	__builtin_ffs
#define popc    __builtin_popcount
#define setbit(w,b) 	asm("btsl %1,%0" : "+r" (w) : "g" (b))
#define clrbit(w,b) 	asm("btrl %1,%0" : "+r" (w) : "g" (b))
#else
#define _popc(w,c)	asm("popc %1,%0\t\n" : "+r" (c) : "r" (w))
#define	setbit(w,b)		((w)|=(0x01<<(b)))
#define	clrbit(w,b)		((w)&=(~(0x01<<(b))))
#define _ffs(w,c)	asm("neg %1, %0\t\n"			\
				"xnor %1, %0, %0\t\n"		\
				"popc %0, %0\t\n"		\
				"movrz %1, %%g0, %0\t\n"	\
				: "+r" (c) : "r" (w))
#endif


/* letter to bit. l must be A-Z^?. Cannot be played blank.*/
#define	l2b(l)	(setbit(0x0,(l-1)))

#define	UBLBIT	(1<<(UBLANK-1))
#define SEPBIT	(1<<(SEP-1))

/* letter values. also worth caching per thread. All blanks are worth 0. */
const uint8_t Vals[32] = {
/* NULL,  A, B, C, D, E, F, G, H, I,  J, K, L, M, N, O, */
      0,  1, 3, 3, 2, 1, 4, 2, 4, 1,  8, 5, 1, 3, 1, 1,
/*    P,  Q, R, S, T, U, V, W, X, Y,  Z, [, \, ], ^, _ */
      3, 10, 1, 1, 1, 1, 4, 4, 8, 4, 10, 0, 0, 0, 0, 0
};

#define lval(l)	(((l)&0xE0) ? 0 : Vals[l] )
#define cval(c)	lval(c2l(c))

/* letter is not char: indexed from 1, 6 bits, non A-Z can be special. */
typedef uint8_t letter_t;	// because we don't have 5/6-bit ints.

/* Rack */
/*
 * it's just an array of 7 letters. Shoud always be sorted, and can
 * contain NULLs.  Local to "position", movegen, etc.
 */
typedef struct Rack {
	letter_t tiles[RACKSIZE+1];
} rack_t;

/* Bag */
/* a bag is just an array of letters, or characters. */
typedef letter_t *bag_t;
typedef char *bagstr_t;		// readable bag
const bagstr_t basebag = "AAAAAAAAABBCCDDDDEEEEEEEEEEEEFFGGGHHIIIIIIIIIJKLLLLMMNNNNNNOOOOOOOOPPQRRRRRRSSSSTTTTTTUUUUVVWWXYYZ??";
const bagstr_t bags[26] = {
	/* A */ "AIOIETPRTIRDDGNEOEDERUCERAAOIOEEFAHASZENKBBSTLRIURMSC?SFGLQETAIGEOYEAOOT?PVNUMLIJVWODNAIIAXLNEWNYUHT",
	/* B */ "BMLUNNRESETO?AOSADTJUOWALITSNTEEDUIRAEAWECNBDTECPIOAYOSINKGERVOYAMIEPTRQEXFRAUVLFOEGEDIIA?HLZOHIIRGN",
	/* C */ "CHHBUERLTJ?PFEXONFADERNRAZOVAEEIOVISWDTPYAEYIN?GENNDILKITOATMSIOEQAITCRILEDEOOGNWGSMRAUALUUEATEBROSI",
	/* D */ "DEHERIOEGDPYOERICIAGFSMYUA?ENAEUFUTBONTRJAWLNITEEINMZNSIRIIPHISE?SQREOTOLEVATAGNCTABORWOAKLDDEOAUVLX",
	/* E */ "E?AVCDNGTIEANJSSCOTLEIREMAEBDPOTLANIEAIWZDTSXRUIPEOONEGUFVIBUMEERIOLWIOAGYNDQ?ESATKYAUHHROEIRFAOTNRL",
	/* F */ "FUOEEBS?ORI?ITARWIDUTATMETAAZQLYEEIMONLOIAVJUGFNAIRTOVEEACYIBPXSEHPEILDISLNRCGOUNHANWOEESDKONARRDEGT",
	/* G */ "GZASFIOIDANNTAAOURMISLN?ONXDDAEEAOEREUFVUGO?HRIMWEOERKETIADRILECTIOEUIIANQNOYPSVEHEWJALREGCBTSPTBTLY",
	/* H */ "HYAIEOEINE?LSIACATLTBEHMERWJWVOFENNRAAILTRQSSBNOEVUGDRCDOOENRUIORPEFYGAALAAKOOTDEIEDEIITPNGTZXU?IMSU",
	/* I */ "IEOUOSNYHCJDEIA?WTTDEQDAZCXEABENAIUTALH?SANWLIIEANELIALREOUOSIUGVTESNEVNORGEFFOPRTEOTRDYRGOIMPBKAIMR",
	/* J */ "JVUQENNWNDEARLAIOUEABZDIREAEBAATFNYOMEAIOT?HRRTAFEEETPOLSNADNIUMEKVGOOXOUWIG?SPYICTSSRTIOHLRCLIEIEDG",
	/* K */ "KHEETWIOEWTMO?OIIACEDORF?VJASTRDNEBNOURQHEASOAYIODIEAIIUNZEULITLCRXGTARMEISVNYNUTAELGNADRESLOPBPEFGA",
	/* L */ "LTUDELNVREITEOSSYBEUNRFA?SOI?DRIHETNUXOMEGPOWACOAIERNTAOJTDIRAVLIWHARDTAGNNEALBUMZGISAPIEEECQIOEKFOY",
	/* M */ "MWLTAFEUEIETAIAXYAOTONNCRFEWAEI?DPEEICIREHILKRZNSJOIDDUYLIBSAHTAAIRNETOUQTOLEDR?GSEPOAUBSGVVRNOOGEMN",
	/* N */ "NARNNMSAAPHCOERRUHAOOIIIEIEKTTAGODUAFOITEDSFDYOOEEGRJENDSIGCLIEITAPQLUME?LRRVBINXTETOL?EWVEANBUZYSWA",
	/* O */ "OETZNIIASEEUHDWDMCTRGOIQDIUNAOOEAEPTWNHENYRINOEDPVRLIIIATATCMV?BNASALBFYSOEIUXELERTEUARORKASOFJL?GGE",
	/* P */ "PEEEENELAJCOOIUNSFIROIEESTBADVMIYWHTRXOULZEGATIECWN?OINE?UMIIBGDVRORAASSOLEPDUATHTREGLQNFATOIAKDRANY",
	/* Q */ "QDSEEOEUUHONGLWRA?ELITRDLNXRMADEZCANYOEOTTAIBVYAEGORNHBTINROPIFSDIMEIGTITNOKSEALOVICFISRAEAJ?UWEPAEU",
	/* R */ "ROTFMAATIAIAGJLAASP?GUUECTNRRIOLRVMYVGASNOXEFDIIDHSOTWZTRNEOIEBAIYEIULDOPSHNWKR?EALENUNOQECEDEEEOTIB",
	/* S */ "SQOJDGAHIAAIBXCYCII?DERLUZSNI?IDNNMRGPMELEKOFGYLOWETVNNOVEOBOLUFRUTNHEOETAITSAAOWEAIRIDUATREAESTEERP",
	/* T */ "TCWIMNVOTAOKRANEZVGIEFOWOURFNXDAOHAIL?GEGEALTRRESICHLAENM?TOSNAUTNSEYDQYJBAAEEDSEIOERTOPDLUIEPIRBIUI",
	/* U */ "UFTUNTSIAR?COZTEMGRJIRMKRDEHLVIAEGEAXIEDAO?OOPTPBBFNYORARHCINIWEEWTGOSEAANLSTUUAELEINYAONEEOIVLQISDD",
	/* V */ "VRETPMPEVAAEEHTCOTENMEIIUWSIOZGARILOGAEIFEOWA?DQAYYIDONOFTXRRELURANSTCOLKTEENJGUOBIR?USANLDHAIIBNEDS",
	/* W */ "WAAVROAYAIIERNTTRIINOXOEPUOLHLGTITAEADDERBOSEROT?ONDECL?GTEUVILJZNQSKMSIEEUIEWAUCSINPDGEEARBYFFHNAOM",
	/* X */ "XPENAHAEAEWTLTRQDVNJTDHIR?SMUTOIITMNEAZETERBOUWROIOERALRFUSBKIECLLEOEDIAYFNOGEOUA?SIAINIESDGCYPGVNOA",
	/* Y */ "YEEAWRUVENLDSSTTZUEABOTIROOAAAONRIMDQFGDRXJGOYLLITTRFITEGSEE?SPBURHHEOANLAECDNOUCENEIWIIMEP?AAIVINKO",
	/* Z */ "ZQSELYRKALAFEBVFRUSHND?UE?REAAEITIGNALOURRAVGOTTXSOOYDMPOSAIEIIAEOIPRHEEETNTCBNMDUGDIJIOWLTCIEOENWNA"
};

/* Space - spaces are what a board is made of. */
/* make sure to assert packing and overlay of union. */
typedef union Space {
	struct {
		uint64_t pad:14;	// pad out to 64 bits.  Reserved.
		uint64_t hmls:7;	// horiz mv letter score.
		uint64_t vmls:7;	// horiz mv letter score.
		uint64_t lm:2;		// letter multiplier (1, 2 or 3)
		uint64_t wm:2;		// word mulitplier (1, 2, or 3)
		uint64_t plays:26;	// bitmap of playable letters
		uint64_t letter:6;	// what's played here. NULL, A-Z,a-z.
	} f;
	uint64_t all;
} space_t;

/* cvt letter to playable bit. */
#define l2bp(l)		(1<<((l)-1))
#define EMPTY	0			// nothing played here yet

/* Board: 15x15 array of spaces. */
/* why is this a struct with only 1 member? Bacause you can assign
 * structures, but you can't assign arrays.
 */
typedef struct Board {
	space_t spaces[BOARDX][BOARDY];
} board_t;

#define	B_NONE		0
#define	B_TILES		1
#define B_VMLS		2
#define B_HMLS		3
#define B_PLAYS		4
#define B_BONUS		5
#define B_BAD		6

#define DL	1
#define TL	2
#define DW	3
#define TW	4

const char bonusnames[5][3] = { "--", "DL", "TL", "DW", "TW" };

/* yes, yes, I know: symmetry. But this is readable. */
const uint8_t boni[BOARDX][BOARDY] = {
/*  A   B   C   D   E   F   G   H   I   J   K   L   M   N   O  */
 { TW,  0,  0, DL,  0,  0,  0, TW,  0,  0,  0, DL,  0,  0, TW },   //1
 {  0, DW,  0,  0,  0, TL,  0,  0,  0, TL,  0,  0,  0, DW,  0 },   //2
 {  0,  0, DW,  0,  0,  0, DL,  0, DL,  0,  0,  0, DW,  0,  0 },   //3
 {  0,  0,  0, DW,  0,  0,  0, DL,  0,  0,  0, DW,  0,  0,  0 },   //4
 {  0,  0,  0,  0, DW,  0,  0,  0,  0,  0, DW,  0,  0,  0,  0 },   //5
 {  0, TL,  0,  0,  0, TL,  0,  0,  0, TL,  0,  0,  0, TL,  0 },   //6
 {  0,  0, DL,  0,  0,  0, DL,  0, DL,  0,  0,  0, DL,  0,  0 },   //7
 { TW,  0,  0, DL,  0,  0,  0, DW,  0,  0,  0, DL,  0,  0, TW },   //8
 {  0,  0, DL,  0,  0,  0, DL,  0, DL,  0,  0,  0, DL,  0,  0 },   //9
 {  0, TL,  0,  0,  0, TL,  0,  0,  0, TL,  0,  0,  0, TL,  0 },   //10
 {  0,  0,  0,  0, DW,  0,  0,  0,  0,  0, DW,  0,  0,  0,  0 },   //11
 {  0,  0,  0, DW,  0,  0,  0, DL,  0,  0,  0, DW,  0,  0,  0 },   //12
 {  0,  0, DW,  0,  0,  0, DL,  0, DL,  0,  0,  0, DW,  0,  0 },   //13
 {  0, DW,  0,  0,  0, TL,  0,  0,  0, TL,  0,  0,  0, DW,  0 },   //14
 { TW,  0,  0, DL,  0,  0,  0, TW,  0,  0,  0, DL,  0,  0, TW }    //15
};

#define ALLPHABITS	0x3FFFFFF	/* 26 1 bits = play any letter */

/* Move. one word played on board */
/* do we need an end-of-game marker here? */
typedef struct Move {
	unsigned short score;	// how much was this move worth
	uint16_t row:4;		// ob
	uint16_t col:4;		// ob
	uint16_t dir:1;		// 0=horizontal, 1=vertical
	uint16_t lcount:4;	// num played (from rack)
	uint16_t pad:3;		// reserved, pad to 16 bits.
	letter_t tiles[BOARDSIZE+1];	// letters to play.
} move_t;

#define	M_HORIZ	0
#define	M_VERT	1

/* position states. WORK IN PROGRESS May need bits instead. */
typedef enum pstate {
	NEW,		// just created, all blank.
	INIT,		// data initialized
	START,		// this is the first position
	LOOK,		// looking for move
	FOUND,		// found move, not made yet
	MOVED,		// move has been placed on board
	SCORE,		// move scored, total score updated
	RACK,		// refilled rack from bag
	SPAWN,		// have child positions
	DONE,		// self and all children completed
	FREE		// can be disposed of.
} pstate_t;

/* position: basically a snapshot of game state. */
typedef struct Position {
	board_t	board;		/* current game board, with move played */
	int score;		/* total of all move scores */
	int bagindex;		/* aka how many tiles used so far */
	rack_t rack;		/* what to play with */
	move_t move;		/* current move */
	struct Position *prev;	/* points to last position. */
	pstate_t state;		/* know what we are doing */
} position_t;

typedef struct Gstats {
	uint64_t evals;		/* total number of board evaluated */
	hrtime_t evtime;	/* elapsed eval time, in nsec. */
	int maxdepth;		/* deepest move stack */
	int maxwidth;		/* move moves for a position */
	int wordhiscore;	/* highest 1-word score */
	int hiscore;		/* highest game score so far */
} gstats_t;


/* internal use for keeping running score during movegen. */
typedef struct _scthingy {
	int ts;		/* tile non-bonus score */
	int tbs;	/* tile with letter bonus score */
	int ssf;	/* score so far */
	int ends;	/* points at end of word */
	int played;	/* count of tiles played, so far */
	int ttl_ts;	/* total non-bonus tile score */
	int ttl_tbs;	/* total tile with letter bonus score */
	int bingo;	/* if we used all 7 letters in rack */
	int wmult;	/* product of word multipliers */
	int xssf;	/* cross score so far */
} scthingy_t;
