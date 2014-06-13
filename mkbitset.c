
/* simple program to create the bitset file for a gaddag */

#include <sys/mman.h>
#include <sys/types.h>
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <strings.h>
#include <sys/stat.h>

typedef unsigned int gn_t;
typedef unsigned int bs_t;
gn_t *gaddag;
bs_t *bitset;
int dfd;
int bsfd;
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


#define l2b(l)	(0x01 << ((l)-1))

int
writebitset(char *f)
{
	char *fullname = "ENABLE.bitset";
	ssize_t wrv;
	size_t bss;

	if (f != NULL)
		bsfd = open(f, O_WRONLY|O_CREAT|O_TRUNC, 00644);
	else
		bsfd = open(fullname, O_WRONLY|O_CREAT|O_TRUNC, 00644);

	if (bsfd < 0) {
		printf( "bitset file %s failed to open\n", fullname);
		perror("open");
		return -1;
	}

	bss = g_cnt * sizeof(bs_t);
	wrv = write(bsfd, bitset, bss);
	if (wrv != bss) {
		printf( "bitset file only wrote %d bytes of %d\n", wrv, bss);
	}
	if (wrv < 0) {
		printf("write to bitset file failed\n");
		perror("write");
	}
	return wrv;
}

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

int
main(int argc, char **argv)
{
	int ncnt;
	long nodeid;
	char sc;	// waydown.
	int scnt = 0;;
	bs_t bit;
	bs_t bits;
	int bsbytes;

	if (argc > 1)
		ncnt = getdict(argv[1]);
	else 
		ncnt = getdict(NULL);
	if (ncnt <= 0) {
		printf("gaddag damage.\n");
		return 1;
	}
	printf("sucked up gaddag file\n");
	/* allocate a (big) buffer for the bitset. */
	bitset = (bs_t *)malloc( ncnt * sizeof(bs_t));
	if (bitset == NULL) {
		perror("bitset malloc");
		return 2;
	}
	bzero(bitset, ncnt*sizeof(bs_t));
	printf("bitset buffer allocated, converting...\n");
	for (nodeid = 0; nodeid < ncnt; nodeid++) {
		scnt = -1;
		bits = 0;
		do {
			scnt++;
			sc = gl(gaddag[nodeid+scnt]);
			bit = l2b(sc);
			bits |= bit;
		} while (!gs(gaddag[nodeid+scnt]));
		bitset[nodeid] = bits;
	}
	printf("writing bitset..\n");
	/* save the file. */
	if (argc > 2)
		bsbytes = writebitset(argv[2]);
	else 
		bsbytes = writebitset(NULL);

	printf("done\n");
	return 0;
}

