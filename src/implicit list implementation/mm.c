/*
 * Name: Yijie Ma
 * AndrewID: yijiem
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - 1) - 1;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + 1;
}

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define OVERHEAD 8

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(uint32_t *)(p))
#define PUT(p, val) (*(uint32_t *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;
static void *extend_heap(uint32_t words);
static void *find_fit(uint32_t asize);
static void place(void *bp, uint32_t asize);
static void *coalesce(void *bp);

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  //printf("enter mm_init\n");
  if((heap_listp = mem_sbrk(4 * WSIZE)) == NULL)
    return -1;

  PUT(heap_listp, 0);
  PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1));
  PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1));
  PUT(heap_listp + WSIZE + DSIZE, PACK(0, 1));
  heap_listp += DSIZE;

  if(extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;
  //printf("exit mm_init\n");
  return 0;
}

static void *extend_heap(uint32_t words){
  //printf("enter extend_heap\n");
  char *bp;
  uint32_t size;
  
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if((long)(bp = mem_sbrk(size)) < 0)  // use long for 64-bits machine!
    return NULL;

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // epilogue block
  //printf("exit extend_heap\n");
  return coalesce(bp);
}

/*
 * malloc
 */
void *malloc (size_t size) {
  //printf("enter malloc\n");
  checkheap(1);  // Let's make sure the heap is ok!
  size_t asize;
  size_t extendsize;
  char *bp;

  if(size <= 0)
    return NULL;

  if(size <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + OVERHEAD + (DSIZE - 1)) / DSIZE);

  if((bp = find_fit(asize)) != NULL){ // find fit place
    place(bp, asize);
    //printf("exit malloc\n");
    return bp;
  }
  
  extendsize = MAX(asize, CHUNKSIZE); // do not find fit place
  if((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  //printf("exit malloc\n");
  return bp;
}

static void *find_fit(uint32_t asize){
  //printf("enter find_fit\n");
  void *bp;
  
  for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
      return bp;
    }
  }
  //printf("exit find_fit\n");
  return NULL;
}

static void place(void *bp, uint32_t asize){
  //printf("enter place\n");
  uint32_t csize = GET_SIZE(HDRP(bp));

  if((csize - asize) >= (DSIZE + OVERHEAD)){
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  }
  else{
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
  //printf("exit place\n");
}


/*
 * free
 */
void free (void *ptr) {
  //printf("ptr = %p\n", ptr);
  //printf("%ld\n", (long)ptr);  
  if((long)ptr <= 0)
    return;     
  
  //printf("enter free\n");
  uint32_t size = GET_SIZE(HDRP(ptr));
  //printf("size = %d\n", size);
  PUT(HDRP(ptr), PACK(size, 0));
  //printf("Here1\n");
  PUT(FTRP(ptr), PACK(size, 0));
  //printf("Here2\n");
  coalesce(ptr);
  //printf("exit free\n");
}

static void *coalesce(void *bp){
  //printf("enter coalesce\n");
  uint32_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  //printf("prev_alloc = %x\n", prev_alloc);
  uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  //printf("next_alloc = %x\n", next_alloc);
  uint32_t size = GET_SIZE(HDRP(bp));
  //printf("size = %x\n", size);

  if(prev_alloc && next_alloc){ // no need to coalesce
    //printf("exit coalesce\n");
    return bp;
  }

  else if(prev_alloc && !next_alloc){ // merge next
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    //printf("exit coalesce\n");
    return (bp);
  }

  else if(!prev_alloc && next_alloc){ // merge prev
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    //printf("exit coalesce\n");
    return (PREV_BLKP(bp));
  }

  else{ // merge prev and next
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    //printf("exit coalesce\n");
    return (PREV_BLKP(bp));
  }
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
  //printf("enter realloc\n");
  size_t oldsize;
  void *newptr;

  if(size == 0){
    free(oldptr);
    //printf("exit realloc\n");
    return 0;
  }

  if(oldptr == NULL){
    //printf("exit realloc\n");
    return malloc(size);
  }

  newptr = malloc(size);

  if(!newptr){
    return 0;
  }

  oldsize = GET_SIZE(HDRP(oldptr));
  if(size < oldsize)
    oldsize = size;
  memcpy(newptr, oldptr, oldsize);
  
  free(oldptr);
  //printf("exit realloc\n");
  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
  //printf("enter calloc\n");
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);
  //printf("exit calloc\n");
  return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    verbose = verbose;
    return 0;
}

/*
int main(){
  mm_init();
  char *a = (char *) malloc(5 * sizeof(int));
  if(a != NULL)
    printf("true\n");
}
*/
