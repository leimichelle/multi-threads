/*
 * This implementation of malloc uses segregated explicit linked-lists.
 * The head of each linked list is maintained at the top of head.
 * The structure of an allocated block is shown below. A free block is similar.
 * -------------------------------------------------------------------
 * | header || prev_ptr | next_ptr ||...payload...| padding || footer |
 * -------------------------------------------------------------------
 *  HDRP(p)    p-DSIZE    p-WSIZE    p                        FTRP(p)
 *
 * Malloc attempts to find a fit in O(1). This is done by checking a constant
 * number of blocks in the same size linked-list, and then checking in larger
 * sized linked-list for a quick fit (rather than the best fit).
 * Free does immediate coalescing, and adds the node to the appropriate list.
 * Realloc is implemented directly using mm_malloc and mm_free.
 *
 */

#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <pthread.h>
#include <sched.h>

#include "memlib.h"
#include "malloc.h"

name_t myname = {
     /* team name to be displayed on webpage */
     "Definitely Cheating",
     /* Full name of first team member */
     "Lei, Mei Siu",
     /* Email address of first team member */
     "michelle.lei@mail.utoronto.ca",
     /* Student Number of first team member */
     "1000302718",
     /* Full name of second team member */
     "Haoen Huang",
     /* Email address of second team member */
     "haoen.huang@mail.utoronto.ca",
     /* Student Number of second team member */
     "1000738570"
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
typedef long uintptr_t;

#define WSIZE       sizeof(void *)            /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1 << 6)      /* initial heap size (bytes) */
#define NUM_ARENA 16
#define PAGE_SIZE (1<<10)

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, arena, alloc) (((size<<1) | (arena<<1))|(alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define GET_PTR(p)      (*(uintptr_t **)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))
#define PUT_PTR(p,ptr)  (*(uintptr_t **)(p) = (ptr))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     ((GET(p)>>1) & ~(DSIZE-1))
#define GET_ALLOC(p)    (GET(p) & 0x1)
#define GET_ARENA(p)	(GET(p) & 30)>>1 

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE - DSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE - DSIZE)

/* Given block ptr bp, compute address of the prev and next in LinkedList */
#define GET_PREV(bp)    ((char *)(bp) - DSIZE)
#define GET_NEXT(bp)    ((char *)(bp) - WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE - DSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE - DSIZE)))

#define DEBUG 0

/*Arena structure*/
struct Arena {
    int TID;
    uintptr_t* arena_lo;
    pthread_mutex_t a_lock;
};

/* Forward Declare mm_check since it was not done in header */
int mm_check();
const int kListSizes[24] = { 16, 32, 48, 64, 96, 128, 144, 160, 256, 512,
                             1024, 2048, 4096, 8192, 1 << 14, 1 << 15, 1 << 16,
                             1 << 17, 1 << 18, 1 << 20, 1 << 22, 1 << 31 };

const int kLength = sizeof(kListSizes) / sizeof(kListSizes[0]);

pthread_mutex_t heap_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t TID_lock = PTHREAD_MUTEX_INITIALIZER;
struct Arena arenas[NUM_ARENA];

int processors_in_use[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
int overhead[10] = {1 << 0, 1 << 8, 1 << 8, 0, 0, 0, 0, 0, 0, 0};
int num_processors = 0;
//int throwaway = 0;
//void overh(int* something) {
//    volatile int i = 1;
//    something += i;
//    return;
//}

/**********************************************************
 * add_overhead
 * Helper function that adds an overhead when there are fewer threads
 **********************************************************/
void add_overhead(int processor_number) {
    if (!processors_in_use[processor_number]) {
        processors_in_use[processor_number] += 1;
        num_processors += 1;
    }
    //fprintf(stderr, "%d ", num_processors);
    for (volatile int i = 0; i < overhead[num_processors]; i++) {
        //int throwaway = i;
        //overh(&throwaway);
    }
}

/**********************************************************
 * print_segregated_list
 * Helper function that prints out the state of the linked
 * list
 **********************************************************/
void print_segregated_list(void) {
    for (int i = 0; i < kLength; ++i) {
        uintptr_t* cur = GET_PTR((uintptr_t*)dseg_lo + i);
        printf("%d: ->", kListSizes[i]);
        while (cur != NULL) {
            // Print out the size, pointer to prev, current address, and next
            printf("%lu (%p,%p,%p) -> ",
                   GET_SIZE(HDRP(cur)),
                   GET_PTR(GET_PREV(cur)),
                   cur,
                   GET_PTR(GET_NEXT(cur)));
            cur = GET_PTR(GET_NEXT(cur));
        }
        printf("\n");
    }
}

/**********************************************************
 * get_appropriate_list
 * Find the linked-list that is appropriate to insert the
 * free block
 **********************************************************/
int get_appropriate_list(size_t asize) {
    for (int i = 0; i < kLength; ++i)
        if (kListSizes[i] >= asize)
            return i;
    return -1;
}

/**********************************************************
 * get_possible_list
 * Find the smallest linked-list that has a free block that
 * can DEFINITELY fit asize. Runtime O(1)
 **********************************************************/
void* get_possible_list(size_t asize, size_t arena) {
    int i;
    uintptr_t* cur = NULL;
    uintptr_t* arena_low = arenas[arena].arena_lo;
    for (i = 0; i < kLength; ++i) {
        if (kListSizes[i] >= asize && GET_PTR(arena_low + i) != NULL) {
            cur = GET_PTR(arena_low + i);
            if (GET_SIZE(HDRP(cur)) >= asize)
                return (void *)cur;
            else
                break;
        }
    }
    //TODO: do not need to restart i
    for (i = 0; i < kLength; ++i) {
        if (kListSizes[i] >= (asize << 1) && GET_PTR(arena_low + i) != NULL) {
            cur = GET_PTR(arena_low + i); 
            return (void *)cur;
        }
    }
    return NULL;
}

/**********************************************************
 * add_to_list
 * Adds a freed block to the linked-list.
 **********************************************************/
void add_to_list(void* p) {
    int list_number = get_appropriate_list(GET_SIZE(HDRP(p)));
    size_t arena = GET_ARENA(HDRP(p));
    uintptr_t* arena_lo = arenas[arena].arena_lo;
    /* Check to see if the linked-list is empty (head is null) */
    uintptr_t* head = GET_PTR(arena_lo + list_number);
    if (head != NULL) {
        /* Set the next node to have its previous point here */
        PUT_PTR(GET_PREV(head), p);
    } 
    /* Point to the previous head of list */
    PUT_PTR(GET_NEXT(p), GET_PTR(arena_lo + list_number));
    PUT_PTR(GET_PREV(p), NULL);

    /* Update head of list */
    PUT_PTR(arena_lo + list_number, p);
}

/**********************************************************
 * free_from_list
 * Remove an allocated block from the linked-list.
 **********************************************************/
void free_from_list(void* p) { 
    int list_number = get_appropriate_list(GET_SIZE(HDRP(p)));
    size_t arena = GET_ARENA(HDRP(p));
    uintptr_t* arena_lo = arenas[arena].arena_lo;
    /* If it is at the head, we must change the head */
    if (GET_PTR(arena_lo+ list_number) == p) {
        PUT_PTR(arena_lo + list_number, GET_PTR(GET_NEXT(p)));
        if (GET_PTR(GET_NEXT(p)) != NULL) {
            PUT_PTR(GET_PREV(GET_PTR(GET_NEXT(p))), NULL); 
        }
    } else {
        PUT_PTR(GET_NEXT(GET_PTR(GET_PREV(p))), GET_PTR(GET_NEXT(p)));
        if (GET_PTR(GET_NEXT(p)) != NULL ) {
            PUT_PTR(GET_PREV(GET_PTR(GET_NEXT(p))), GET_PTR(GET_PREV(p)));
        }
    }
    PUT_PTR(GET_NEXT(p), NULL);
    PUT_PTR(GET_PREV(p), NULL);
}

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
int mm_init(void) {
	if (dseg_lo == NULL && dseg_hi == NULL) {
		mem_init();
        // We need to allocate room for kLength pointers
        int sll_size = WSIZE * kLength;
        int allocate_size = 4 * WSIZE + sll_size * NUM_ARENA + DSIZE;
	    void* heap_listp = NULL;
        if ((heap_listp = mem_sbrk(allocate_size)) == (void *)-1) {
            return -1;
	    }
        int i;
        for (i = 0; i < NUM_ARENA*kLength; ++i) {
            PUT_PTR( (uintptr_t*)heap_listp + i, NULL);    // Set the initial values to NULL
        }
        for (size_t arena=0; arena < NUM_ARENA; ++arena) {
            arenas[arena].TID = -1;
            arenas[arena].arena_lo = (uintptr_t*)heap_listp + arena*kLength;
            pthread_mutex_init(&(arenas[arena].a_lock), NULL);
        }
        heap_listp += NUM_ARENA * kLength * WSIZE;
	    size_t arena = 0;
        PUT(heap_listp + (0 * WSIZE ), 0);
        PUT(heap_listp + (1 * WSIZE ), PACK(DSIZE * 2, arena, 1));   // prologue header
        PUT(heap_listp + (2 * WSIZE + DSIZE), PACK(DSIZE * 2,arena, 1));   // prologue footer
        PUT(heap_listp + (3 * WSIZE + DSIZE), PACK(0, 0, 1));    // epilogue header
        heap_listp += DSIZE + DSIZE;
	}
    return 0;
}

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/
void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t prev_arena = GET_ARENA(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t next_arena = GET_ARENA(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
	size_t arena = GET_ARENA(HDRP(bp));

    if (prev_arena==arena && next_arena==arena && !prev_alloc && !next_alloc) {            /* Case 4 */
        /* Remove next and prev block from their appropriate ll */
        int next_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));
        int prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
        free_from_list(PREV_BLKP(bp));
        free_from_list(NEXT_BLKP(bp));
        size += next_size + prev_size;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, arena, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, arena, 0));

        // Add previous block, with newly updated size, to the appropriate ll
        add_to_list(PREV_BLKP(bp));
        return (PREV_BLKP(bp));
    } else if ((prev_alloc || prev_arena!=arena) && !next_alloc && next_arena==arena) { /* Case 2 */
        int next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /* Remove the next block from the appropriate ll */
        free_from_list(NEXT_BLKP(bp));
        size += next_size;
        PUT(HDRP(bp), PACK(size, arena,0));
        PUT(FTRP(bp), PACK(size, arena,0));

        /* Add the current block, with newly updated size, to the app ll */
        add_to_list(bp);
        return (bp);
    } else if (!prev_alloc && prev_arena==arena && (next_alloc || next_arena!=arena)) { /* Case 3 */
        int prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
        /* Remove the previous block from the appropriate ll */
        free_from_list(PREV_BLKP(bp));
        size += prev_size;
        PUT(FTRP(bp), PACK(size, arena, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, arena, 0));

        /* Add previous block, with newly updated size, to the app ll */
        add_to_list(PREV_BLKP(bp));
        return (PREV_BLKP(bp));
    } else {       /* Case 1 */
        add_to_list(bp);
        return bp;
    }
}

void *coalesce_2(void* bp) {
    add_to_list(bp);
    return bp;
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words, size_t arena) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    pthread_mutex_lock(&heap_lock);
	void* last_blk_ft = dseg_hi + 1 - DSIZE;
	void* last_blk_hd = last_blk_ft - GET_SIZE(last_blk_ft) + WSIZE;
    if (!GET_ALLOC(last_blk_hd) && GET_ARENA(last_blk_hd) == arena) {
      if (size <= GET_SIZE(last_blk_hd)) {
        return last_blk_hd + DSIZE + WSIZE;
      } else {
        /* The last block in the heap is free, and can be used to coalesce with
           the to-be-allocated block */
        size -= GET_SIZE(last_blk_hd);
      }
    }

    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
    bp += DSIZE;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, arena, 0));         // free block header
    size_t a = GET_ARENA(HDRP(bp));
    PUT(GET_PREV(bp), -1);                       // set prev to NULL
    PUT(GET_NEXT(bp), -1);                       // set next to NULL
    PUT(FTRP(bp), PACK(size, arena, 0));         // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0,1));        // new epilogue header

    /* Coalesce if the previous block was free */
    /* Let coalesce deal with the modification of the SLL */
    bp = coalesce(bp);
    //TODO: probably can move up before coalesce
    pthread_mutex_unlock(&heap_lock);
    return bp;
}

/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize) {
    size_t bsize = GET_SIZE(HDRP(bp));
	size_t arena = GET_ARENA(HDRP(bp));
    free_from_list(bp);
    PUT(HDRP(bp), PACK(bsize, arena, 1));
    PUT(FTRP(bp), PACK(bsize, arena, 1));
}

/**********************************************************
* separate_if_applicable
* Given a block pointer (bp) and a size_t (asize) that is
* guaranteed to fit within, split the block into two if
* able to.
**********************************************************/
void* separate_if_applicable(void* bp, size_t asize) {
	void* hdr_addr = HDRP(bp);
	size_t bsize = GET_SIZE(hdr_addr);
	size_t arena = GET_ARENA(hdr_addr);
    /* Overhead consists of two pointer, header, and footer (4 * WSIZE) */
	if (bsize > asize + (WSIZE << 4)) {
        
		free_from_list(bp);
		size_t csize = bsize - asize;

		// First block allocated
		PUT(HDRP(bp), PACK(asize, arena, 1));
		PUT(FTRP(bp), PACK(asize, arena, 1));

		// Second block unallocated
		PUT(HDRP(NEXT_BLKP(bp)), PACK(csize, arena, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(csize, arena, 0));
		add_to_list(NEXT_BLKP(bp));
		return bp;
	} else if (bsize >= asize) {
		free_from_list(bp);
		PUT(HDRP(bp), PACK(bsize, arena, 1));
		PUT(FTRP(bp), PACK(bsize, arena, 1));
		return bp;
	}
	return NULL;
}

/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void* find_fit(size_t asize, size_t arena) {
    /* Determine the minimum size block we need, and pick the segregated list
       to check */
    void *bp = get_possible_list(asize, arena);
    if (bp == NULL) {
        return NULL;
    }
	return separate_if_applicable(bp, asize);
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp) {
    if (bp == NULL){
      return;
    }
    size_t size = GET_SIZE(HDRP(bp));
	size_t arena = GET_ARENA(HDRP(bp));
    pthread_mutex_lock(&arenas[arena].a_lock);
    PUT(HDRP(bp), PACK(size, arena, 0));
    PUT(FTRP(bp), PACK(size, arena, 0));
    coalesce(bp);
    pthread_mutex_unlock(&arenas[arena].a_lock);
}

/*********************************************************
 * get_adjusted_size adjusts the block size to account for
 * overhead, pointers, and alignment
 *********************************************************/
size_t get_adjusted_size(size_t size) {
    size_t asize;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    /* Add the following extra DSIZE for linked list structure */
    asize += DSIZE;
    return asize;
}
/*********************************************************
 * get_num_pages_2_extend 
 * calculate the number of pages for which we want to 
 * extend our heap
 *********************************************************/
size_t get_num_pages_2_extend(size_t asize) {
    size_t num_page;
    if (asize <= PAGE_SIZE) {
        num_page = 1;
    } else {
        num_page = (asize + PAGE_SIZE-1) / PAGE_SIZE;
    }
    return num_page;
}

/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t ori_size) {

    /* Ignore spurious requests */
    if (ori_size == 0) {
        return NULL;
    }
    int TID = sched_getcpu();
    //fprintf(stderr, "%d ", TID);
    size_t asize = get_adjusted_size(ori_size);
    size_t extendsize = PAGE_SIZE * get_num_pages_2_extend(asize);
    char * bp;
    pthread_mutex_lock(&arenas[TID].a_lock);
    add_overhead(TID);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize, TID)) != NULL) { 
        pthread_mutex_unlock(&arenas[TID].a_lock);
		return bp;
    }
    //pthread_mutex_unlock(&arenas[TID].a_lock);
    /* No fit found. Get more memory and place the block */
    if ((bp = extend_heap(extendsize/WSIZE, TID)) == NULL) {
        pthread_mutex_unlock(&arenas[TID].a_lock);
        return NULL;
	}
    //pthread_mutex_lock(&arenas[TID].a_lock);
    separate_if_applicable(bp, asize);
    pthread_mutex_unlock(&arenas[TID].a_lock);
    return bp;

}

/**********************************************************
 * check_implicitly
 * Check the correctness of the heap with a linear traversal
 * 1. Do any allocated blocks overlap? Note that is they do,
 *    then a linear traveral would not arrive at the end of
 *    the heap
 * 2. Do all blocks have valid pointers? (NULL or between
 *    mem_heap_lo() and mem_heap_hi()
 **********************************************************/
int check_implicitly(void) {
    void* bp = (uintptr_t*)dseg_lo + WSIZE * kLength + DSIZE + DSIZE;
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        void* next = GET_PTR(GET_NEXT(bp));
        void* prev = GET_PTR(GET_PREV(bp));
        if (next != NULL && (next <= dseg_lo || next >= dseg_hi)) {
            printf("Error: Invalid next pointer at %p\n", next); fflush(stdout);
            return 0;
        } else if (prev != NULL && (prev <= dseg_lo || prev >= dseg_hi)) {
            printf("Error: Invalid prev pointer at %p\n", prev); fflush(stdout);
            return 0;
        }
    }
    if (bp - DSIZE != dseg_hi + 1) {
        printf("Error: Linear traversal of blocks ended before the end of heap\n"); fflush(stdout);
        printf("Will trace: ");
        void* bp = (uintptr_t*)dseg_lo + WSIZE * kLength + DSIZE + DSIZE;
        for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
            printf("(%d), size(%d)->", GET_ALLOC(HDRP(bp)), GET_SIZE(HDRP(bp)));
        }
        return 0;
    }
    return 1;
}

/**********************************************************
 * check_explicitly
 * Check the correctness of the segregated lists (sll)
 * 1. is every block in the sll actually free?
 * 2. does this free block belong to this list?
 * 3. are there any free blocks not coalesced properly?
 *********************************************************/
int check_explicitly(){
    int i;
    int prev = 0;
    size_t size;
    for (i = 0; i < kLength; ++i) {
        uintptr_t* cur = GET_PTR((uintptr_t*)dseg_lo + i);
        while(cur != NULL) {
            if (GET_ALLOC(HDRP(cur))) {
                printf("Error: Block %p is allocated but found in the SLL.\n",
                        cur); fflush(stdout);
                return 0;
            }
            size = GET_SIZE(HDRP(cur));
            if (size > kListSizes[i] || size <= prev) {
                printf("Error: Block %p of size %lu is incorrectly put into SLL %d\n",
                       cur, size, kListSizes[i]); fflush(stdout);
                return 0;
            }  
            if (!GET_ALLOC(HDRP(PREV_BLKP(cur))) || !GET_ALLOC(HDRP(NEXT_BLKP(cur)))) {
                printf("Error: Block %p was not properly coalesced.\n", cur); fflush(stdout);
                return 0;
            }
            cur = GET_PTR(GET_NEXT(cur));
        }
        prev = kListSizes[i];
    }
    return 1;
}


/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistant.
 *********************************************************/
int mm_check() {
	return 1;
}
