/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * Note: This assignment is a _baseline_ for the performance grade.
 * You will need to exceed the performance of this implicit first-fit placement
 * (which is about 54/100).
 */

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In my solution I plan to use mm-firstfit.c that is given and work my way with it. I will use LIFO linked list that goes both ways. My variable
        heap_free is the same as heap_listp but points to the first piece of the free blocks. When a block is free'd it will call the coalesce function
        which then will check where that block was, depending on where in the list was it will take different measures for example if its the first
        block already coalesce wont change any pointers, but if the block is in the middle I will put bp at the start, BP-1 will point to BP+1,
        bp+1->reverse will point to BP-1. Having BP as the first block in the LIFO list pointing to the old header of the list. Oldheader->reverse
        points to BP now. With only pointing to the free blocks I am hoping to traverse the linked list much faster and allocating memory much faster.
 *
 */


#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/* Team structure */
/*********************************************************
* NOTE TO STUDENTS: Before you do anything else, please
* provide your team information in below _AND_ in the
* struct that follows.
*
* === User information ===
* Group:Fighting_Mongoose
 * User 1:Juliusg13
 * SSN:2801922799
* User 2:
 * SSN: X
* === End User Information ===
********************************************************/
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* (which is about 54/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define ALIGN(size) (((size_t)(size) + 7) & ~0x7)

#define PRE(bp) ((void *)(bp - DSIZE)) //Predecessor of BP
#define SUC(bp) ((void *)(bp + DSIZE)) //pointer to successor of BP

/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char *freelist; //pointer to start of free list
static int freecount; //the count of free blocks.
/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void addFree(void* bp);
static void removeFree(void* bp);
static void printFree();
/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
	freelist = heap_listp;
    freecount = 0;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    bp = find_fit(asize);
//   printf("malloc bp is %x\n", bp);
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    addFree(bp);
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }
     
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
 
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    freecount += 1;
    /* Coalesce if the previous block was free */
//    return extendCoal(bp);
	addFree(bp);
	return bp;
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
//	printf("New place, bp is: %x\n", bp);
//	printf("asize: %d\n", asize);

    size_t csize = GET_SIZE(HDRP(bp));
//    printf("csize: %d and OVERHEAD: %d\n", csize, OVERHEAD);
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
	removeFree(bp);

        bp = NEXT_BLKP(bp);
       	PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
	addFree(bp);

    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
	removeFree(bp); 
	}

}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
//loops through the free blocks using a generic for loop, and then putting bp has successor of bp.
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp = freelist;
    int i;

    for (i = 0; i < freecount; i++) {
//	 for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {

		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//	        removeFree(bp);
		return bp;
       		 }
		if(i < freecount-1) bp = NEXT_BLKP(bp);
         }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
//	printFree();
//	printf("Pre coalesce \n");
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }
    removeFree(bp);
    if (prev_alloc && !next_alloc) {      /* Case 2 */
//printf("case2\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	removeFree(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
//printf("case3\n");
size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	removeFree(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {   
//printf("else\n");                                  /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
	removeFree(PREV_BLKP(bp));
	removeFree(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    addFree(bp);
//	printFree();
//	printf("after coal \n");
    return bp;
}
//Adds a free block to the free list.
static void addFree(void *bp)
{
	freecount += 1;
	PUT(SUC(bp), GET_ALLOC(freelist));
	PUT(PRE(freelist), GET_ALLOC(bp));
	PUT(PRE(bp), (int)NULL);
	freelist = bp;
}
//removes a free block from the free list.
static void removeFree(void *bp)
{
	void* PP = PRE(bp);
	void* NP = SUC(bp);
	freecount -= 1;
	if(PP == NULL) {
		PUT(PRE(NP), (int)NULL);
		PUT(SUC(bp), (int)NULL);
		freelist = NP;
		return;
	} else if(NP == NULL) {
		PUT(SUC(PP), (int)NULL);
		PUT(PRE(bp), (int)NULL);
		PUT(SUC(bp), (int)NULL);
		return;
	}
	PUT(SUC(PP), GET_ALLOC(NP));
	PUT(PRE(NP), GET_ALLOC(PP));
	PUT(SUC(bp), (int)NULL);
	PUT(PRE(bp), (int)NULL);
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

static void printFree()
{
	void *bp = freelist;

	int i;
	for(i = 0; i < freecount; i++){
		printblock(bp);	
		bp = SUC(bp);
	}

}
