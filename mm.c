/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))


/* Basic constants and macros */
#define WSIZE     4       /* Word and header/footer size (bytes) */
#define DSIZE     8       /* Double word size (bytes) */
#define MINISIZE 24
#define CHUNKSIZE (1<<8) /* Extend heap by this amount (bytes)*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)        (*(unsigned int*)(p))
#define PUT(p, val)   (*(unsigned int*)(p) = val)
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)      ((char*)(bp) - WSIZE)
#define FTRP(bp)      ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

#define GET_PTR(p)      ((p)? *(size_t *)(p) : 0)
#define PUT_PTR(p, val) ((p) ? *(size_t *)(p) = (size_t)(val) : 0)
#define PRED(bp)        ((bp) ? (char *)(bp) : 0)
#define SUCC(bp)        ((bp) ? (char *)(bp) + DSIZE : 0)
#define GET_PRED(bp) ((bp) ? GET_PTR(PRED(bp)) : 0)
#define GET_SUCC(bp) ((bp) ? GET_PTR(SUCC(bp)) : 0)

static char *heap_listp, *free_head[10];

static int find_array(size_t size){
  /*
  int re = 0;
  while (size > 0) {
    if (re == LINK_SIZE - 1) return re;
    size >>= 2;
    re++;
  }
  return re;
  */
  if (size <= (1 << 8)) return 0;
  else if (size <= (1 << 10)) return 1;
  else if (size <= (1 << 12)) return 2;
  else if (size <= (1 << 13)) return 3;
  else if (size <= (1 << 14)) return 4;
  else if (size <= (1 << 15)) return 5;
  else if (size <= (1 << 16)) return 6;
  else return 7;
}

static void remove_block(void *ptr) {
  PUT_PTR(SUCC(GET_PRED(ptr)),GET_SUCC(ptr));
  PUT_PTR(PRED(GET_SUCC(ptr)),GET_PRED(ptr));
  //if (ptr == free_head) free_head = GET_SUCC(free_head);
  int i = find_array(GET_SIZE(HDRP(ptr)));
  if (ptr == free_head[i]) free_head[i] = GET_SUCC(free_head[i]);
}

static void push_block(void *ptr) {
  /*
  PUT_PTR(SUCC(ptr), free_head);
  PUT_PTR(PRED(ptr), 0);
  PUT_PTR(PRED(free_head),ptr);
  free_head = ptr;*/
  
  int i = find_array(GET_SIZE(HDRP(ptr)));
  PUT_PTR(SUCC(ptr), free_head[i]);
  PUT_PTR(PRED(ptr), 0);
  PUT_PTR(PRED(free_head[i]), ptr);
  free_head[i] = ptr;
  
}

static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  if (prev_alloc && next_alloc) { /* Case 1 */
    //return bp;
  } else if (prev_alloc && !next_alloc) { /* Case 2 */
    remove_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) { /* Case 3 */
    remove_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  } else { /* Case 4 */
    remove_block(PREV_BLKP(bp));
    remove_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  push_block(bp);
  return bp;
}

static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;
  PUT(HDRP(bp), PACK(size, 0));   /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));   /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
  return coalesce(bp);
}

static void *find_fit(size_t asize){
  int h = find_array(asize);
  char* bp = free_head[h];
  //char *bp = free_head;
  size_t size;
  while(bp != 0){
    size = GET_SIZE(HDRP(bp));
    if (size >= asize) return bp;
    bp = GET_SUCC(bp);
  }
  for(int i = h + 1; i < 8; i++){
    char* bp = free_head[i];
    while(bp != 0){
      size = GET_SIZE(HDRP(bp));
      if (size >= asize) return bp;
      bp = GET_SUCC(bp);
    }
  }
  return NULL;
}

static void place(void *bp, size_t asize){
  remove_block(bp);
  size_t exist_size = GET_SIZE(HDRP(bp));
  if (exist_size - asize > MINISIZE) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK((exist_size - asize), 0));
    PUT(FTRP(bp), PACK((exist_size - asize), 0));
    coalesce(bp);
  } else {
    PUT(HDRP(bp), PACK(exist_size, 1));
    PUT(FTRP(bp), PACK(exist_size, 1));
  }

}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void)
{
  heap_listp = mem_sbrk(8 * WSIZE);
  PUT(heap_listp, 0);
  PUT(heap_listp + (1 * WSIZE), PACK(MINISIZE, 1));
  PUT_PTR(heap_listp + (2 * WSIZE), 0);
  PUT_PTR(heap_listp + (4 * WSIZE), 0); // prologue succ
  PUT(heap_listp + (6 * WSIZE), PACK(MINISIZE, 1)); // prologue footer
  PUT(heap_listp + (7 * WSIZE), PACK(0,1));// epilogue header
  heap_listp += 2 * WSIZE;
 // free_head = 0;
  for (int i = 0; i < 8; ++i) free_head[i] = 0;
  if(extend_heap(CHUNKSIZE/WSIZE) == NULL)return -1;
  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
  size_t asize;       /* Adjusted block size */
  size_t extendsize;  /* Amount to extend heap if no fit */
  char *bp;
  if (size == 0) return NULL;
  //if (size <= DSIZE) 
  //  asize = 2*DSIZE;
  //else
  //  asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
  asize = ALIGN(MAX(size + MINISIZE, MINISIZE + DSIZE));
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL ) return NULL;
  place(bp, asize);
  return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
  if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;
  if((long)ptr == 0)puts("?");
	size_t size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	verbose = verbose;
}