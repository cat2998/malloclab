/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "권지현 이민형 진재혁",
    /* First member's email address */
    "cat2998@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define SEGREGATED_SIZE 12

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned long *)(p))
#define PUT(p, val) (*(unsigned long *)(p) = (val))

/* Read the size and allocated fields from address */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Give block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PRED(bp) GET(bp) // *(void **)(bp)
#define SUCC(bp) GET((char *)bp + WSIZE)
#define ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;

static void splice_free_block(void *bp); // 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void add_free_block(void *bp);    // 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
int get_class(size_t size);              // 적합한 가용 리스트를 찾는 함수

static void *find_fit(size_t asize)
{
    /*  First-fit search */
    char *bp;
    char *bp_list;
    int class = get_class(asize);

    while (class < SEGREGATED_SIZE)
    {
        bp_list = ROOT(class);
        for (bp = bp_list; bp != NULL; bp = SUCC(bp))
        {
            if (asize <= GET_SIZE(HDRP(bp)))
                return bp;
        }
        class += 1;
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        add_free_block(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */
    }
    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        splice_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    { /* Case 4 */
        splice_free_block(PREV_BLKP(bp));
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free_block(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE + DSIZE : words * WSIZE + DSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*  New epilogue header */

    /* Coalesce if the previous vlock was free */
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK((2 + SEGREGATED_SIZE) * WSIZE, 1)); // 프롤로그 헤더
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((2 + SEGREGATED_SIZE) * WSIZE), PACK((2 + SEGREGATED_SIZE) * WSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + ((3 + SEGREGATED_SIZE) * WSIZE), PACK(0, 1));                             // 에필로그 헤더
    heap_listp += (2 * WSIZE);

    /* Wxtend the empty hep with a free block of CHUNKSIZE bytes */
    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* 헤더, 푸터, pred, succ 1워드 데이터 2워드 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
        return mm_malloc(size);

    size_t old_size = GET_SIZE(HDRP(bp));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (size + 2 * WSIZE <= old_size)
        return bp;
    if (!next_alloc && size + 2 * WSIZE <= old_size + next_size)
    {
        splice_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(old_size + next_size, 1));
        PUT(FTRP(bp), PACK(old_size + next_size, 1));
        return bp;
    }
    if (!prev_alloc && size + 2 * WSIZE <= old_size + prev_size)
    {
        char *pre = PREV_BLKP(bp);
        splice_free_block(pre);
        memmove(pre, bp, old_size);
        PUT(HDRP(pre), PACK(old_size + prev_size, 1));
        PUT(FTRP(pre), PACK(old_size + prev_size, 1));
        return pre;
    }

    void *newp = mm_malloc(size);
    if (newp == NULL)
        return 0;
    memcpy(newp, bp, old_size);
    mm_free(bp);
    return newp;
}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));

    if (SUCC(bp) != NULL)
        PRED(SUCC(bp)) = PRED(bp);
    if (ROOT(class) == bp) // 처음이면
    {
        ROOT(class) = SUCC(bp);
        return;
    }
    SUCC(PRED(bp)) = SUCC(bp);
    return;
}

// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));

    SUCC(bp) = ROOT(class);
    if (ROOT(class) != NULL)
        PRED(ROOT(class)) = bp;
    ROOT(class) = bp;
    return;
}

// 적합한 가용 리스트를 찾는 함수
int get_class(size_t size)
{
    size_t class_size = 16;

    if (size < 16)
        return -1;

    for (int i = 0; i < SEGREGATED_SIZE; i++)
    {
        class_size <<= 1;
        if (size < class_size)
            return i;
    }
    return SEGREGATED_SIZE - 1;
}