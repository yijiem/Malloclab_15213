/*
 *  Name: Yijie Ma
 *  AndrewID: yijiem
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
 *  some useful macro
 */
#define WSIZE 1    // use 4-bytes word size as basic amount of size
#define DSIZE 2
#define CHUNKSIZE (1 << 10) // 1024 words
#define OVERHEAD 2 // normal overhead in word(so it is 2 words)

#define FREE 1
#define ALLOC 0
#define MAX(x, y) ((x) > (y) ? (x) : (y))


static uint32_t *heap_listp;
static void *extend_heap(uint32_t words);
static void *find_fit(uint32_t asize);
static void place(void *bp, uint32_t asize);
static void *coalesce(void *bp);


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

// 参数全部改为指向head的指针 除了block_hdrp
// Return the header pointer of the pointer points to payload

// 参数：payload
// 返回：header
static inline uint32_t* block_hdrp(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block));

    return block - 1;
}

// Return the size of the given block in multiples of the word size
// 结果直接是 size based on word size, 不需要再除以WSIZE
// 前2位: 0, a/f; 后30位: block size

// 参数：header / footer
// 返回：size 
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    //return (block_hdrp(block)[0] & 0x3FFFFFFF)
    return (block[0] & 0x3FFFFFFF);
}

// Return the footer pointer of the pointer points to payload

// 参数：payload
// 返回：footer
static inline uint32_t* block_ftrp(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block));

    return block + block_size(block_hdrp(block)) - DSIZE;
}

// Return true if the block is free, false otherwise
// 只有header或者footer可以作为此函数的参数

// 参数：header / footer
// 返回：free(1) / alloc(0)
static inline int block_free(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.

// 参数：header(footer同时完成)
// 返回：空
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    if(block_size(block) == 0){
      block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
      return;
    } else {
      unsigned int next = block_size(block) - 1; // ? 原: block_size(block) + 1
      block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
      block[next] = block[0]; // 设置footer对应内容
      return;
    }
}

// set the block size to both header and footer

// 参数：header(footer同时完成)
// 返回：空
static inline void block_set_size(uint32_t* block, uint32_t size_in_words) {
  REQUIRES(block != NULL);
  REQUIRES(in_heap(block));
  
  if(size_in_words == 0) { // indicate the block do not have header or footer
    block[0] = size_in_words;
    return;
  } else {
    unsigned int next = size_in_words - 1;
    block[0] = size_in_words;
    block[next] = block[0]; // set footer
    return;
  }
}

// Return a pointer to the memory malloc should return

// 参数：header
// 返回：payload
static inline  uint32_t* block_mem(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}

// Return the head pointer to the previous block

// 参数：header
// 返回：header
static inline uint32_t* block_prev(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - WSIZE); // 原: block_size(block - 1) - 1
}

// Return the header to the next block

// 参数：header
// 返回：header
static inline uint32_t* block_next(uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    // 原: block_size(block) + 1
    return block + block_size(block);
}



#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(uint32_t *)(p))
#define PUT(p, val) (*(uint32_t *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))



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
  if((heap_listp = mem_sbrk(4 * WSIZE * 4)) == NULL) // adjust words to bytes
    return -1;
  
  block_set_size(heap_listp, 0); // set first block for place holder
  block_mark(heap_listp, FREE);
  
  block_set_size(heap_listp + WSIZE, OVERHEAD); // set prologue block for 1st alloc block
  block_mark(heap_listp + WSIZE, ALLOC);
  //block_set_size(heap_listp + DSIZE, OVERHEAD);
  //block_mark(heap_listp + DSIZE, ALLOC);

  block_set_size(heap_listp + WSIZE + DSIZE, 0); // set epilogue block
  block_mark(heap_listp + WSIZE + DSIZE, ALLOC);
  /*
  PUT(heap_listp, 0);
  PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1));
  PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1));
  PUT(heap_listp + WSIZE + DSIZE, PACK(0, 1));
  */
  heap_listp += DSIZE;

  if(extend_heap(CHUNKSIZE) == NULL)
    return -1;
  //printf("exit mm_init\n");
  checkheap(1);
  return 0;
}

static void *extend_heap(uint32_t words){
  //printf("enter extend_heap\n");
  uint32_t *bp;
  uint32_t size;
  
  size = (words % 2) ? ((words + 1) * 4) : (words * 4); // convert to bytes
  if((long)(bp = mem_sbrk(size)) < 0)  // use long for 64-bits machine!
    return NULL;
  
  block_set_size(block_hdrp(bp), size / 4); // bp is not the header, but the payload pointer
  block_mark(block_hdrp(bp), FREE);
  
  //block_set_size(block_ftrp(bp), size / 4);
  //block_mark(block_ftrp(bp), FREE);

  block_set_size(block_next(block_hdrp(bp)), 0);
  block_mark(block_next(block_hdrp(bp)), ALLOC);
  // PUT(HDRP(bp), PACK(size, 0));
  // PUT(FTRP(bp), PACK(size, 0));
  //PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // epilogue block
  //printf("exit extend_heap\n");
  return coalesce(bp);
}

/*
 * malloc
 */
void *malloc (size_t size) {
  //printf("enter malloc\n");
  checkheap(1);  // Let's make sure the heap is ok!
  size_t asize;  // actual size
  size_t extendsize;
  uint32_t *bp;

  if(size <= 0)
    return NULL;

  if(size <= 8) // set actual size
    asize = 8 + 8;
  else
    asize = 8 * ((size + 8 + (8 - 1)) / 8);

  asize = asize / 4; // convert bytes to words

  if((bp = find_fit(asize)) != NULL){ // find fit place
    place(bp, asize);
    //printf("exit malloc\n");
    checkheap(1);
    return bp;
  }
  
  extendsize = MAX(asize, CHUNKSIZE); // do not find fit place
  if((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  checkheap(1);
  //printf("exit malloc\n");
  return bp;
}

static void *find_fit(uint32_t asize){
  //printf("enter find_fit\n");
  void *bp;
  
  for(bp = heap_listp; (in_heap(bp)) && (block_size(block_hdrp(bp)) > 0); 
                        bp = block_mem(block_next(block_hdrp(bp)))){ // convert to payload
    if(block_free(block_hdrp(bp)) && (asize <= block_size(block_hdrp(bp)))){
      return bp;
    }
  }
  /*
  for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
      return bp;
    }
  }
  */
  //printf("exit find_fit\n");
  return NULL;
}

static void place(void *bp, uint32_t asize){
  //printf("enter place\n");
  uint32_t csize = block_size(block_hdrp(bp));

  if((csize - asize) >= (DSIZE + OVERHEAD)){
    block_set_size(block_hdrp(bp), asize);
    block_mark(block_hdrp(bp), ALLOC);

    //block_set_size(block_ftrp(bp), asize);
    //block_mark(block_ftrp(bp), ALLOC);

    bp = block_mem(block_next(block_hdrp(bp)));
    
    block_set_size(block_hdrp(bp), csize - asize);
    block_mark(block_hdrp(bp), FREE);
    return;
    //block_set_size(block_ftrp(bp), csize - asize);
    //block_mark(block_ftrp(bp), FREE);
    //PUT(HDRP(bp), PACK(asize, 1));
    //PUT(FTRP(bp), PACK(asize, 1));
    //bp = NEXT_BLKP(bp);
    //PUT(HDRP(bp), PACK(csize - asize, 0));
    //PUT(FTRP(bp), PACK(csize - asize, 0));
  }
  else{
    block_set_size(block_hdrp(bp), csize);
    block_mark(block_hdrp(bp), ALLOC);
    return;
    //block_set_size(block_ftrp(bp), csize);
    //block_mark(block_ftrp(bp), ALLOC);
    //PUT(HDRP(bp), PACK(csize, 1));
    //PUT(FTRP(bp), PACK(csize, 1));
  }
  //printf("exit place\n");
}


/*
 * free
 */
void free(void *ptr) {
  //printf("ptr = %p\n", ptr);
  //printf("%ld\n", (long)ptr);  
  if((long)ptr <= 0)
    return;     
  checkheap(1);
  //printf("enter free\n");
  //uint32_t size = block_size(block_hdrp(ptr));
  //uint32_t size = GET_SIZE(HDRP(ptr));
  //printf("size = %d\n", size);
  block_mark(block_hdrp(ptr), FREE);
  //block_mark(block_ftrp(ptr), FREE);

  //PUT(HDRP(ptr), PACK(size, 0));
  //printf("Here1\n");
  //PUT(FTRP(ptr), PACK(size, 0));
  //printf("Here2\n");
  coalesce(ptr);
  checkheap(1);
  //printf("exit free\n");
}

static void *coalesce(void *bp){
  //printf("enter coalesce\n");
  int prev_alloc = block_free(block_prev(block_hdrp(bp)));
  //uint32_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  //printf("prev_alloc = %x\n", prev_alloc);
  int next_alloc = block_free(block_next(block_hdrp(bp)));
  //uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  //printf("next_alloc = %x\n", next_alloc);
  uint32_t size = block_size(block_hdrp(bp));
  //uint32_t size = GET_SIZE(HDRP(bp));
  //printf("size = %x\n", size);

  if(!prev_alloc && !next_alloc){ // no need to coalesce
    //printf("exit coalesce\n");
    return bp;
  }

  else if(!prev_alloc && next_alloc){ // merge next
    size += block_size(block_next(block_hdrp(bp)));
    //size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    block_set_size(block_hdrp(bp), size);
    block_mark(block_hdrp(bp), FREE);

    //block_set_size(block_ftrp(bp), size);
    //block_mark(block_ftrp(bp), FREE);
    //PUT(HDRP(bp), PACK(size, 0));
    //PUT(FTRP(bp), PACK(size, 0));
    //printf("exit coalesce\n");
    return (bp);
  }

  else if(prev_alloc && !next_alloc){ // merge prev
    size += block_size(block_prev(block_hdrp(bp)));
    //size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    //block_set_size(block_ftrp(bp), size);
    //block_mark(block_ftrp(bp), FREE);
    
    block_set_size(block_prev(block_hdrp(bp)), size);
    block_mark(block_prev(block_hdrp(bp)), FREE);
    //PUT(FTRP(bp), PACK(size, 0));
    //PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    //printf("exit coalesce\n");
    return block_mem(block_prev(block_hdrp(bp)));
    //return (PREV_BLKP(bp));
  }

  else{ // merge prev and next
    size += block_size(block_prev(block_hdrp(bp))) + 
            block_size(block_next(block_hdrp(bp)));
    //size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    block_set_size(block_prev(block_hdrp(bp)), size);
    block_mark(block_prev(block_hdrp(bp)), FREE);
    
    //block_set_size(block_next(block_hdrp(bp)), size);
    //block_mark(block_next(block_hdrp(bp)), FREE);
    //PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    //PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    //printf("exit coalesce\n");
    return block_mem(block_prev(block_hdrp(bp)));
    //return (PREV_BLKP(bp));
  }
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
  //printf("enter realloc\n");
  size_t oldsize;
  void *newptr;
  checkheap(1);
  if(size == 0){
    free(oldptr);
    //printf("exit realloc\n");
    return NULL; // should return NULL
  }

  if(oldptr == NULL){
    //printf("exit realloc\n");
    return malloc(size);
  }

  newptr = malloc(size);

  if(!newptr){
    return 0;
  }
  
  oldsize = block_size(block_hdrp(oldptr));
  oldsize *= 4;
  //oldsize = GET_SIZE(HDRP(oldptr));
  if(size < oldsize) // convert words to bytes
    oldsize = size;
  memcpy(newptr, oldptr, oldsize);
  
  free(oldptr);
  checkheap(1);
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
  checkheap(1);

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);
  checkheap(1);
  //printf("exit calloc\n");
  return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    if(verbose == 1){ // if verbose == 1, then check heap　
        
        // check prologue blocks
        if(block_size(block_hdrp(heap_listp)) != 2){
          printf(" checkheap: prologue header size error\n");
          return 1;
        }
        if(block_free(block_hdrp(heap_listp)) != 0){
          printf(" checkheap: prologue header free/alloc bit error\n");
          return 1;
        }
        if(block_size(heap_listp) != 2){
          printf(" checkheap: prologue footer size error\n");
          return 1;
        }
        if(block_free(heap_listp) != 0){
          printf(" checkheap: prologue footer free/alloc bit error\n");
          return 1;
        }

        // check heap boundary and epilogue block
        if(block_size((uint32_t *) mem_heap_lo()) != 0){
          printf(" checkheap: heap low boundary size error\n");
          return 1;
        }
        if(block_free((uint32_t *) mem_heap_lo()) != 1){
          printf(" checkheap: heap low boundary free/alloc bit error\n");
          return 1;
        }
        if(block_size((uint32_t *) ((char *)mem_heap_hi() - 3)) != 0){
          printf(" checkheap: epilogue size error\n");
          return 1;
        }
        if(block_free((uint32_t *) ((char *)mem_heap_hi() - 3)) != 0){
          printf(" checkheap: epilogue free/alloc bit error\n");
          return 1;
        }
        
        // check each block's address alignment
        /* check each block's header and footer: minimum size, alignment, 
           bit consistency, header and footer matching, 
           no two consecutive free blocks */
        uint32_t *ptr = heap_listp;
        uint32_t free_block_flag = 0;

        while(1){
            if(aligned(ptr) != 1){
              printf(" checkheap: payload block alignment problem\n");
              return 1;
            }
            if(aligned(block_ftrp(ptr)) != 1){
              printf(" checkheap: footer block alignment problem\n");
              return 1;
            }
            if(ptr == heap_listp){
              if(block_size(block_hdrp(ptr)) < 2){
                printf(" checkheap: size in header of prologue less than 2-words-minimum\n");
                return 1;
              }
            }else{
              if(block_size(block_hdrp(ptr)) < 4){
                printf(" checkheap: size in header less than 4-words-minimum\n");
                return 1;
              }
            }
            if(block_size(block_hdrp(ptr)) != block_size(block_ftrp(ptr))){
              printf(" checkheap: size in header not equal to size in footer\n");
              return 1;
            }
            if(block_free(block_hdrp(ptr)) != block_free(block_ftrp(ptr))){
              printf(" checkheap: free/alloc bit in header not equal to mafree/alloc bit in footer\n");
              return 1;
            }

            // check no two consecutive free blocks
            if(free_block_flag == 0 && block_free(block_hdrp(ptr)) == 1){
              // first time free blocks
              free_block_flag = 1;
            }else if(free_block_flag == 1 && block_free(block_hdrp(ptr)) == 1){
              printf(" checkheap: two consecutive free blocks error\n");
              return 1;
            }else{
              free_block_flag = 0;
            }

            // check whether move to next block or terminate
            // or face with a fatal error
            if(block_size(block_next(block_hdrp(ptr))) == 0 && 
              block_free(block_next(block_hdrp(ptr))) == 0){ 
              // almost ??? reach epilogue ???
              if(block_next(block_hdrp(ptr)) == (uint32_t *)((char *)mem_heap_hi() - 3)){
                return 0;
              }else{
                printf(" checkheap: fatal error: this should be a new header, but its value shows that it is an epilogue\n");
                return 1;
              }
            }else{
              ptr = block_mem(block_next(block_hdrp(ptr))); // move to next block
            }
        }
    }
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
