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


// EXPLICIT LIST LIFO




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

team_t team = {
    "Fighting_Mongoose",
    "juliusg13", "2801922799",
    "", "",
    "", ""
};

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

/* Given block ptr block_ptr, compute address of its header and footer */
#define HDRP(block_ptr)       ((char *)(block_ptr) - WSIZE)  
#define FTRP(block_ptr)       ((char *)(block_ptr) + GET_SIZE(HDRP(block_ptr)) - DSIZE)

/* Given block ptr block_ptr, compute address of next and previous blocks */
#define NEXT_BLKP(block_ptr)  ((char *)(block_ptr) + GET_SIZE(((char *)(block_ptr) - WSIZE)))
#define PREV_BLKP(block_ptr)  ((char *)(block_ptr) - GET_SIZE(((char *)(block_ptr) - DSIZE)))

#define ALIGN(size) (((size_t)(size) + 7) & ~0x7)

#define PRE_PTR(block_ptr) ((void *)(block_ptr)) 				//Predecessor of BP
#define SUC_PTR(block_ptr) ((void *)(block_ptr + WSIZE)) 		//pointer to successor of BP

#define PREV(block_ptr) (*(void **)(block_ptr))
#define SUCC(block_ptr) (*(void **)(SUC_PTR(block_ptr)))

/* $end mallocmacros */

/* Global variables */
static char *p_heap_list;  /* pointer to first block */  
static char *mp_firstfreeblock;
static int 	m_freecount;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *block_ptr, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *block_ptr);
static void printblock(void *block_ptr); 
static void checkblock(void *block_ptr);
static void allocate_block(void * block_ptr);
static void free_block(void * block_ptr);

/* 
 * mm_init - Initialize the memory manager 
Begin heap 1: f6a10008
End heap 1: f6a10017
heap list 2: f6a10010
Begin heap 2: f6a10008
End heap 2: f6a11017

Init - End
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((p_heap_list = mem_sbrk(4*WSIZE)) == NULL) return -1;
    PUT(p_heap_list, 0);                        /* alignment padding */
    PUT(p_heap_list+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(p_heap_list+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(p_heap_list+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    p_heap_list += DSIZE;
    mp_firstfreeblock = p_heap_list;
    m_freecount = 0;
	
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

//    PUT((SUCC(mp_firstfreeblock)+WSIZE), (int)NULL);
//    PUT((PREV(mp_firstfreeblock)+WSIZE), (int)NULL);
    SUCC(mp_firstfreeblock + WSIZE) = NULL;
    PREV(mp_firstfreeblock + WSIZE) = NULL;


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
    char *block_ptr;      
//printf("enter malloc \n");
    /* Ignore spurious requests */
    if (size <= 0) return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	{
       		 asize = DSIZE + OVERHEAD;
	}
    else
	{
	        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
	}
    
    /* Search the free list for a fit */
	block_ptr = find_fit(asize);
    if (block_ptr != NULL) 
	{

        place(block_ptr, asize);

        return block_ptr;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    block_ptr = extend_heap(extendsize/WSIZE);
    if (block_ptr == NULL)
    {
        return NULL;
    }
//printf("malloc calling from extend heap \n");
    place(block_ptr, asize);
// printf("last malloc \n");

    return block_ptr;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *block_ptr)
{
    size_t size = GET_SIZE(HDRP(block_ptr));

    PUT(HDRP(block_ptr), PACK(size, 0));
    PUT(FTRP(block_ptr), PACK(size, 0));


    coalesce(block_ptr);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) 
	{
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
	{
        copySize = size;
	}
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *block_ptr = p_heap_list;

    if (verbose)
	{
        printf("Heap (%p):\n", p_heap_list);
		}

    if ((GET_SIZE(HDRP(p_heap_list)) != DSIZE) || !GET_ALLOC(HDRP(p_heap_list)))
	{
        printf("Bad prologue header\n");
	}
    checkblock(p_heap_list);

    for (block_ptr = p_heap_list; GET_SIZE(HDRP(block_ptr)) > 0; block_ptr = NEXT_BLKP(block_ptr)) 
	{
        if (verbose) 
		{
            printblock(block_ptr);
		}
        checkblock(block_ptr);
    }
 
    if (verbose)
	{
        printblock(block_ptr);
	}
    if ((GET_SIZE(HDRP(block_ptr)) != 0) || !(GET_ALLOC(HDRP(block_ptr))))
	{
        printf("Bad epilogue header\n");
	}
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *block_ptr;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((block_ptr = mem_sbrk(size)) == (void *)-1) 
	{
        return NULL;
	}

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(block_ptr), PACK(size, 0));         /* free block header */
    PUT(FTRP(block_ptr), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(block_ptr)), PACK(0, 1)); /* new epilogue header */
  /* Coalesce if the previous block was free */


    return coalesce(block_ptr);

}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block block_ptr 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *block_ptr, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(block_ptr));

	allocate_block(block_ptr);

    if ((csize - asize) >= (DSIZE + OVERHEAD)) 
	{ 
        PUT(HDRP(block_ptr), PACK(asize, 1));
        PUT(FTRP(block_ptr), PACK(asize, 1));
        block_ptr = NEXT_BLKP(block_ptr);
        PUT(HDRP(block_ptr), PACK(csize-asize, 0));
        PUT(FTRP(block_ptr), PACK(csize-asize, 0));
		free_block(block_ptr);

    }
    else 
	{ 
        PUT(HDRP(block_ptr), PACK(csize, 1));
        PUT(FTRP(block_ptr), PACK(csize, 1));
    }
 //printf("last place \n");

}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *block_ptr;

    for (block_ptr = mp_firstfreeblock; m_freecount >= 0; block_ptr = (SUCC(block_ptr))) 
    {
	if (block_ptr == NULL)
	{
		return NULL;
	}
        if (!GET_ALLOC(HDRP(block_ptr)) && (asize <= GET_SIZE(HDRP(block_ptr)))) 
	{
            return block_ptr;
        }

    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *block_ptr) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(block_ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(block_ptr)));
    size_t size = GET_SIZE(HDRP(block_ptr));

    if (prev_alloc && next_alloc) 					/* Case 1 */
    {
	free_block(block_ptr);
        return block_ptr;
    }

    if (prev_alloc && !next_alloc) 			 /* Case 2 */
    {
	allocate_block(NEXT_BLKP(block_ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(block_ptr)));
        PUT(HDRP(block_ptr), PACK(size, 0));
        PUT(FTRP(block_ptr), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc)				 /* Case 3 */
    {     
	allocate_block(PREV_BLKP(block_ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(block_ptr)));
        PUT(FTRP(block_ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(block_ptr)), PACK(size, 0));
        block_ptr = PREV_BLKP(block_ptr);
    }

    else 											/* Case 4 */
	{   

	allocate_block(NEXT_BLKP(block_ptr));
	allocate_block(PREV_BLKP(block_ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(block_ptr))) + GET_SIZE(FTRP(NEXT_BLKP(block_ptr)));
        PUT(HDRP(PREV_BLKP(block_ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(block_ptr)), PACK(size, 0));
        block_ptr = PREV_BLKP(block_ptr);
    }
	free_block(block_ptr);

    return block_ptr;
}


static void printblock(void *block_ptr) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(block_ptr));
    halloc = GET_ALLOC(HDRP(block_ptr));  
    fsize = GET_SIZE(FTRP(block_ptr));
    falloc = GET_ALLOC(FTRP(block_ptr));  
   
    if (hsize == 0) 
	{
        printf("%p: EOL\n", block_ptr);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block_ptr, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *block_ptr) 
{
    if ((size_t)block_ptr % 8)
	{
        printf("Error: %p is not doubleword aligned\n", block_ptr);
	}
    if (GET(HDRP(block_ptr)) != GET(FTRP(block_ptr)))
	{
        printf("Error: header does not match footer\n");
	}
}


static void printfree()
{
    void *block_ptr;
    for (block_ptr = p_heap_list; GET_SIZE(HDRP(block_ptr)) > 0; block_ptr = NEXT_BLKP(block_ptr))
    {
	size_t next_alloc = GET_ALLOC(HDRP((block_ptr)));
	if(next_alloc == 0) printblock(block_ptr);

    }
}


static void free_block(void * block_ptr)
{
	m_freecount += 1;

	if ((mp_firstfreeblock == p_heap_list) || mp_firstfreeblock == NULL){
		SUCC(block_ptr) = NULL;
		PREV(block_ptr) = NULL;
		mp_firstfreeblock = block_ptr;
		return;
	}
	SUCC(block_ptr) = mp_firstfreeblock;
	PREV(block_ptr) = NULL;

	PREV(mp_firstfreeblock) = block_ptr;
	mp_firstfreeblock = block_ptr;
}

static void allocate_block(void * block_ptr)
{
	m_freecount -= 1;

	if((m_freecount == 0)){ //already lowered free list // as in if only one free block.
		PREV(block_ptr) = NULL;
		SUCC(block_ptr) = NULL;
		mp_firstfreeblock = NULL;
		return;
	}
	if(m_freecount == -1){
		printf("SHOULD NOT HAPPEN:: ERROR:: ERROR \n");
		m_freecount = 0;
		return;
	}
	void* pp = PREV(block_ptr);
	void* np = SUCC(block_ptr);

	if(np == NULL){
		SUCC(pp) = NULL;

		SUCC(block_ptr) = NULL;
		PREV(block_ptr) = NULL;
		return;
	}
	else if(pp == NULL){
		mp_firstfreeblock = SUCC(block_ptr);
		PREV(mp_firstfreeblock) = NULL;
		PREV(block_ptr) = NULL;
		SUCC(block_ptr) = NULL;
		return;
	}

	SUCC(pp) = np;
	PREV(np) = pp;


	SUCC(block_ptr) = NULL;
	PREV(block_ptr) = NULL;
}
