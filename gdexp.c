
/* gaddag explorer. simple little program, really. */
/* use new gaddag format. */

#include <sys/types.h>
#include <sys/mman.h>
#include <stdio.h>
#include <errno.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <ctype.h>

typedef unsigned int gn_t;
gn_t *gaddag;
int dfd;
int g_cnt;

#if __BYTE_ORDER__ == 12345
#define gs(n)   ((n)&0x80000000)
#define gf(n)   ((n)&0x40000000)
#define gl(n)   (((n)>>24)&0x3F)
#define gc(n)   (__builtin_bswap32(n)>>8)
#else   /* "NORMAL" */
#define gc(n)   ((n)>>8)        // first child index
#define gs(n)   ((n)&0x80)      // have more sibs
#define gl(n)   ((n)&0x3F)      // node letter value
#define gf(n)   ((n)&0x40)      // final = end of word
#endif

#define	SEP	0x1e
#ifdef OLDGADDAG
#define gl2c(l)          (((l)-4)|0x40)
#else
#define gl2c(l)          ((l)|0x40)
#endif

int
getdict(char *f)
{
	char *fullname = "ENABLE.gaddag";
	int rv;
	struct stat st;
	size_t len;

	if (f != NULL) 
		dfd = open(f, O_RDONLY);
	else
		dfd = open(fullname, O_RDONLY);

	if (dfd < 0) {
		printf( "gaddag file %s failed to open\n", fullname);
		perror("open");
		return -1;
	}
	rv = fstat(dfd, &st);
	if (rv < 0) {
		printf( "cannot fstat open file %s\n", fullname);
		perror("fstat");
		return -2;
	}
	len = st.st_size;
	if (len % sizeof(gn_t)) {
		printf("gaddag data not aligned properly\n");
		return -3;
	}
	g_cnt = len / sizeof(gn_t);
	printf("opened %d len %d for %d entries\n", dfd, len, g_cnt);
	gaddag = (gn_t *)mmap(0, len, PROT_READ, MAP_SHARED, dfd, 0);
	if (gaddag == MAP_FAILED) {
		printf("failed to mmap %d bytes of gaddag\n", len);
		perror("mmap");
		return -4;
	}
	return g_cnt;
}


void
printn(long nodeid)
{
	gn_t node = gaddag[nodeid];
	
	printf("nodeid %ld->%x [%d,%c,%c,%c(%d)]\n", nodeid, node, gc(node), gs(node) ? '$' : '>' , gf(node) ? '.': ' ', gl(node)==0?'_':gl2c(gl(node)), gl(node));
}

void
expnode(int nodeid)
{
	gn_t mynode;
	gn_t curnode;
	gn_t sib, child;
	int sibid, childid;
	char letter;
	int ccnt = 0;
	int scnt = 0;;
	int stop;
	int word;
	int i;
	char sibs[28] = "";
	char kids[28] = "";

	mynode = gaddag[nodeid];
	letter = gl2c(gl(mynode));
	if (gl(mynode) == 0) {
		letter = '^';
	}

// printf("Ok, %d is %x, with %d %d %d (%c)\n", nodeid, mynode, gl(mynode), gl2c(gl(mynode)), letter, letter);
	for (scnt = 0; !gs(gaddag[nodeid+scnt]); scnt++) {
// printf("sib %d (%d) = %x, gs=%d\n", scnt, nodeid+scnt, gaddag[nodeid+scnt], gs(gaddag[nodeid+scnt]));

		sibs[scnt] = gl2c(gl(gaddag[nodeid+scnt]));
		if (gl(gaddag[nodeid+scnt]) == 0) {
			sibs[scnt] = '_';
		} else if (!isprint(sibs[scnt])) {
			 sibs[scnt] = '#';
		}
	}
	sibs[scnt] = gl2c(gl(gaddag[nodeid+scnt]));
	if (gl(gaddag[nodeid+scnt]) == 0) {
		sibs[scnt] = '_';
	} else if (!isprint(sibs[scnt])) {
		 sibs[scnt] = '#';
	}
	childid = gc(mynode);
	child = gaddag[childid];

	for (ccnt = 0; !gs(gaddag[childid+ccnt]); ccnt++) {
// printf("kid %d (%d) = %x, gc=%d\n", ccnt, childid+ccnt, gaddag[childid+ccnt], gl(gaddag[childid+ccnt]));
		kids[ccnt] = gl2c(gl(gaddag[childid+ccnt]));
		if (gl(gaddag[childid+ccnt]) == 0) kids[ccnt] = '^';
		else if (!isprint(kids[ccnt])) kids[ccnt] = '#';
	}
	kids[ccnt] = gl2c(gl(gaddag[childid+ccnt]));
	if (gl(gaddag[childid+ccnt]) == 0) kids[ccnt] = '_';
	else if (!isprint(kids[ccnt])) kids[ccnt] = '#';
	/* gathered all info, print it now. */
	printn(nodeid);
//	printf("nodeid %d->%x [%d,%c,%c,%c(%d)]\n", nodeid, mynode, childid, gs(mynode) ? '$' : '>' , gf(mynode) ? '.': ' ', letter, gl(mynode));
	printf("there are %d siblings: \"%s\"\n", scnt, sibs);
	printf("it has %d children: \"%s\"\n", ccnt, kids);
if (strlen(kids) != ccnt+1)
	printf ("kid count mis mitch str %d cnt %d\n", strlen(kids), ccnt);
}

#define PUSH(v)	(stk[stkp++]=v)
#define POP	((stkp>0)?stk[stkp--]:-1)
#define CLR	(stk[stkp=0]=0)
#define TOP	((stkp>0)?stk[stkp-1]:-1)
#define MT	(stkp==0)
#define REP(v)	((stkp>0)&&(stk[stkp-1]=v))

int
main(int argc, char **argv)
{
	int rv;
	char *l;
	int ncnt;
	char line[1024] = "";
	gn_t node;
	long nodeid = 0;;
	int done = 0;
	int c;		// option letter for getopt
	char mc;	// waydown.
	int cn;
	int noprint = 1;
	long stk[20];	// should max out at 16.
	int stkp = 0;

	
	if (argc > 1)
		ncnt = getdict(argv[1]);
	else 
		ncnt = getdict(NULL);

	if (ncnt <= 0) {
		printf("Dictionary disaster.\n");
		return 1;
	}

	CLR;
	nodeid = 0;
	node = gaddag[nodeid];
	PUSH(0);

	while(! done) {
		printf("gde[%ld]> ", TOP);
		l = fgets(line, 80, stdin);
		if (l == NULL) break;
		if (isdigit(line[0])) {
			nodeid = atol(line);
			PUSH(nodeid);
			noprint = 0;
		} else {
			switch (line[0]) {
			case 'q':	
				done = 1;
				noprint = 1;
			break;
			case 'd':
				nodeid = gc(gaddag[nodeid]);
				PUSH(nodeid);
				noprint = 0;
			break;
			case 'u':
				nodeid = POP;
				noprint = 0;
			break;
			case 's': {
				int i;
				for (i=stkp;i>0;i--) {
					printn(stk[i-1]);
				}
				noprint = 1;
			}
			break;
			case 'w': {
				int i;
				for (i=stkp;i>0;i--) {
					printf("%c", gl2c(gl(gaddag[stk[i-1]])));
				}
				printf("\n");
				noprint = 1;
			}
			break;
			case 'P':
				PUSH(nodeid);
				noprint = 1;
			break;
			case 'X':
				POP;
				nodeid = TOP;
				noprint = 0;
			break;
			case 'n':
				if (gs(node)) {
					printf("no more siblings.\n");
				} else {
					nodeid++;
					REP(nodeid);
					noprint = 0;
				}
			break;
			case 'b':
				if ((nodeid == 0) || (gs(gaddag[nodeid -1]))) {
					printf("At oldest sibling.\n");
				} else {
					nodeid--;
					REP(nodeid);
					noprint = 0;
				}
			break;
			case 'p':
			case '.':
				noprint = 0;
			/* don't have to do anything. */
			break;
			case 'r':
				CLR;
				nodeid = 0;
				noprint = 0;
				PUSH(0);
			break;
			case 'm':
				noprint = 1;
				mc = line[1];
				cn = nodeid;
				if ((!isupper(mc)) && (mc != '^'))  {
					printf("bad char %c to match\n", mc);
					break; /* out of switch */
				}
				do {
					if (gl2c(gl(gaddag[cn])) == mc) {
						nodeid = cn;
						noprint = 0;
						REP(nodeid);
						break;
					}
				} while (!gs(gaddag[cn++]));
			break;
			}
		}
		if (stkp <= 0) {
			printf("stack stupidity\n");
			CLR;
			PUSH(nodeid);
		}
		if ((nodeid < 0) || (nodeid > g_cnt)) {
			printf("node %ld out of range\n", nodeid);
			continue;
		}
		node = gaddag[nodeid];
		if (! noprint) expnode(nodeid);
	}
	return 0;
}
