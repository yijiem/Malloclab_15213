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

#define END_OF_LIST 0

static uint64_t **explicit_free_list_header;
static int explicit_free_list_size;

static uint32_t *heap_listp;
static void *extend_heap(uint32_t words);
static void *find_fit(uint32_t asize);
static void place(void *bp, uint32_t asize);
static void *coalesce(void *bp);
static void addFirst(uint64_t **prev, uint64_t **succ);

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


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {

  // init 6 words for explicit free linked list(add explicit_free_list_header)
  if((heap_listp = mem_sbrk(6 * WSIZE * 4)) == NULL)
    return -1;
  
  explicit_free_list_header = (uint64_t **) heap_listp;
  explicit_free_list_size = 0;

  heap_listp = heap_listp + 2; // move heap_listp to the old first block

  block_set_size(heap_listp, 0); // set first block for place holder
  block_mark(heap_listp, FREE);
  
  block_set_size(heap_listp + WSIZE, OVERHEAD); // set prologue block for 1st alloc block
  block_mark(heap_listp + WSIZE, ALLOC);

  block_set_size(heap_listp + WSIZE + DSIZE, 0); // set epilogue block
  block_mark(heap_listp + WSIZE + DSIZE, ALLOC);

  heap_listp += DSIZE;

  if(extend_heap(CHUNKSIZE) == NULL)
    return -1;

  checkheap(1);
  return 0;
}

static void *extend_heap(uint32_t words){

  uint32_t *bp;
  uint32_t size;
  
  size = (words % 2) ? ((words + 1) * 4) : (words * 4); // convert to bytes
  if((long)(bp = mem_sbrk(size)) < 0)  // use long for 64-bits machine!
    return NULL;
  
  block_set_size(block_hdrp(bp), size / 4); // bp is not the header, but the payload pointer
  block_mark(block_hdrp(bp), FREE);

  block_set_size(block_next(block_hdrp(bp)), 0); // set epilogue
  block_mark(block_next(block_hdrp(bp)), ALLOC);

  // last-in-first-out explicit-free-list implementation
  uint64_t **prev = (uint64_t **) bp; // prev pointer of extended free block
  uint64_t **succ = prev + 1; // succ pointer of extended free block

  addFirst(prev, succ); //LIFO

  return coalesce(bp);
}

/*
// private helper method
// connect from para1 to para2
// one-way connection
static void connect_from_one_to_two(uint64_t *para1, uint64_t *para2){
  uint64_t *para1_innerpointer = (uint64_t *) *para1;

  para1_innerpointer = para2;
}
*/

// add free block indicated by prev and succ to the first element in free list
// 为prev, succ所指向的空间分配实际的数据，也就是指向其他free block的指针
static void addFirst(uint64_t **prev, uint64_t **succ){
  
  // free list is empty(either begin or free list shrinks to empty)
  if(explicit_free_list_size == 0){
      *explicit_free_list_header = (uint64_t *) prev;
      *prev = (uint64_t *) explicit_free_list_header;
      *succ = END_OF_LIST; // succ points to 0(end of list)
      explicit_free_list_size++;
      return;
  }else{ // free list already exist
      uint64_t **oldFirstFreePrev = (uint64_t **) *explicit_free_list_header;
      *explicit_free_list_header = (uint64_t *) prev;
      *prev = (uint64_t *) explicit_free_list_header;
      *succ = (uint64_t *) oldFirstFreePrev;
      *oldFirstFreePrev = (uint64_t *) prev; // free block都是指向前一个或后一个的prev(old payload)
      explicit_free_list_size++;
      return;
  }
}

/*
 * malloc
 */
void *malloc (size_t size) {
  checkheap(1);  // Let's make sure the heap is ok!
  size_t asize;  // actual size
  size_t extendsize;
  uint32_t *bp;

  if(size <= 0)
    return NULL;

  // for explicit free list, minimum size is 24 bytes
  if(size <= 16) // set actual size
    asize = 16 + 8;
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

// find fit for explicit free list
static void *find_fit(uint32_t asize){
  
  uint32_t iter_num = explicit_free_list_size;
  uint64_t **iter_ptr = explicit_free_list_header;

  while(iter_num > 0){
    // first time: move from header to next free block's payload(prev)
    iter_ptr = (uint64_t **) *iter_ptr;
    if(asize <= block_size(block_hdrp((uint32_t *)iter_ptr))){
      return (uint32_t *)iter_ptr;
    }
    iter_ptr++; // move to the succ pointer of this free block
    iter_num--;
    if(iter_num == 0 && *iter_ptr != END_OF_LIST){
      printf(" runtime error: in find_fit(), when iter_num is 0, *iter_ptr != EOL\n");
    }
  }
  return NULL;
}

static void place(void *bp, uint32_t asize){
  //printf("enter place\n");
  uint32_t csize = block_size(block_hdrp(bp));
  
  // explicit free list, splitting condition is 24 bytes(6 words)
  if((csize - asize) >= (DSIZE + OVERHEAD + 2)){ // split the block
    block_set_size(block_hdrp(bp), asize);
    block_mark(block_hdrp(bp), ALLOC);
    
    uint64_t **bp_prevblock_prev = (uint64_t **) *(uint64_t **)bp; // 暂存bp的free list中的前后位置
    uint64_t **bp_succblock_prev = (uint64_t **) *((uint64_t **)bp + 1);

    bp = block_mem(block_next(block_hdrp(bp))); // bp points to next split block's payload
    
    block_set_size(block_hdrp(bp), csize - asize);
    block_mark(block_hdrp(bp), FREE);
    
    // 平移 2 pointers to the next split block's prev and succ's position
    *(uint64_t **)bp = (uint64_t *) bp_prevblock_prev;
    *((uint64_t **)bp + 1) = (uint64_t *) bp_succblock_prev;
    
    if(bp_prevblock_prev == explicit_free_list_header && 
      bp_succblock_prev == END_OF_LIST){ // old bp is the only free block in free list
      *explicit_free_list_header = (uint64_t *) bp;
      // this time, size should be 1
      if(explicit_free_list_size != 1){
        printf(" runtime error: in place(), explicit_free_list_size should be 1 when placing the only block with splitting\n");
      }
      return;
    }else if(bp_prevblock_prev == explicit_free_list_header){ // old bp is the first block in free list
      *explicit_free_list_header = (uint64_t *) bp;
      *bp_succblock_prev = (uint64_t *)bp; //~~~~~~~~~~~~~~~~~~~~~~~~
      return;
    }else if(bp_succblock_prev == END_OF_LIST){
      uint64_t **bp_prevblock_succ = bp_prevblock_prev + 1;
      *bp_prevblock_succ = (uint64_t *)bp; //~~~~~~~~~~~~~~~~~~~~~~~~
      return;
    }else{
      uint64_t **bp_prevblock_succ = bp_prevblock_prev + 1;
      *bp_prevblock_succ = (uint64_t *)bp;
      *bp_succblock_prev = (uint64_t *)bp; //~~~~~~~~~~~~~~~~~~~~~~~~
      return;
    }
  }

  else{ // do not split the block
    block_set_size(block_hdrp(bp), csize);
    block_mark(block_hdrp(bp), ALLOC);

    uint64_t **bp_prevblock_prev = (uint64_t **) *(uint64_t **)bp;
    uint64_t **bp_succblock_prev = (uint64_t **) *((uint64_t **)bp + 1);
    
    // header也需要判断，因为header没有prev与succ之分
    if(bp_prevblock_prev == explicit_free_list_header && // place block's prev points to list head
      bp_succblock_prev == END_OF_LIST){ // place block's succ points to EOL
      *explicit_free_list_header = END_OF_LIST;
      explicit_free_list_size--; 
      // size should be 0
      if(explicit_free_list_size != 0){
        printf(" runtime error: in place(), explicit_free_list_size should be 0 when placing the only block without splitting\n");
      }
      return;
    }else if(bp_succblock_prev == END_OF_LIST){
      uint64_t **bp_prevblock_succ = bp_prevblock_prev + 1;
      *bp_prevblock_succ = END_OF_LIST;
      explicit_free_list_size--;
      return;
    }else if(bp_prevblock_prev == explicit_free_list_header){
      *explicit_free_list_header = (uint64_t *) bp_succblock_prev;
      *bp_succblock_prev = (uint64_t *) explicit_free_list_header;
      explicit_free_list_size--; 
      return;
    }else{ // no special condition
      uint64_t **bp_prevblock_succ = bp_prevblock_prev + 1;
      *bp_prevblock_succ = (uint64_t *) bp_succblock_prev;
      *bp_succblock_prev = (uint64_t *) bp_prevblock_prev;
      explicit_free_list_size--;
      return;
    }
  }
}


/*
 * free
 */
void free(void *bp) {

  if((long)bp <= 0)
    return;     
  checkheap(1);
  block_mark(block_hdrp(bp), FREE);
  
  uint64_t **prev = (uint64_t **) bp;
  uint64_t **succ = prev + 1;

  addFirst(prev, succ);

  coalesce(bp);
  checkheap(1);
}

static void *coalesce(void *bp){

  int prev_alloc = block_free(block_prev(block_hdrp(bp)));

  int next_alloc = block_free(block_next(block_hdrp(bp)));

  uint32_t size = block_size(block_hdrp(bp));


  if(!prev_alloc && !next_alloc){ // no need to coalesce
    return bp;
  }

  else if(!prev_alloc && next_alloc){ // merge next
    // Last-In-First-Out Strategy
    // bp's next block's prev pointer
    uint64_t **bp_physicnext_prev = (uint64_t **) block_mem(block_next(block_hdrp(bp)));
    // bp's next block's succ pointer
    uint64_t **bp_physicnext_succ = bp_physicnext_prev + 1;

    // merge next，所以下面三行语句必须放在上面两行语句的下面
    size += block_size(block_next(block_hdrp(bp)));
    block_set_size(block_hdrp(bp), size);
    block_mark(block_hdrp(bp), FREE);
    
    // for LIFO, bp的物理next的prev不可能指向header
    if(*bp_physicnext_succ == END_OF_LIST){ // if bp的 物理next的succ指向END OF LIST
      //uint64_t **bp_physicnext_prevblock_prev = (uint64_t **) *bp_physicnext_prev;
      uint64_t **bp_physicnext_prevblock_succ = ((uint64_t **) *bp_physicnext_prev) + 1;

      *bp_physicnext_prevblock_succ = END_OF_LIST;
    }else{ // bp的 物理next的succ不指向EOL
      uint64_t **bp_physicnext_prevblock_prev = (uint64_t **) *bp_physicnext_prev;
      uint64_t **bp_physicnext_succblock_prev = (uint64_t **) *bp_physicnext_succ;
      uint64_t **bp_physicnext_prevblock_succ = ((uint64_t **) *bp_physicnext_prev) + 1;
  
      *bp_physicnext_prevblock_succ = (uint64_t *) bp_physicnext_succblock_prev;
      // 如果不加判断，这一步解引用会出错，因为bp_physicnext_succblock_prev可能为0
      *bp_physicnext_succblock_prev = (uint64_t *) bp_physicnext_prevblock_prev;
    }
    
    // for safety, no pointer points to these two pointers now
    *bp_physicnext_prev = 0;
    *bp_physicnext_succ = 0;

    explicit_free_list_size--;
    return bp;
  }

  else if(prev_alloc && !next_alloc){ // merge prev
    size += block_size(block_prev(block_hdrp(bp)));
    block_set_size(block_prev(block_hdrp(bp)), size);
    block_mark(block_prev(block_hdrp(bp)), FREE);
    
    // Last-In-First-Out Strategy
    // bp's prev block's prev pointer
    uint64_t **bp_physicprev_prev = (uint64_t **) block_mem(block_prev(block_hdrp(bp)));
    // bp's prev block's succ pointer
    uint64_t **bp_physicprev_succ = bp_physicprev_prev + 1;

    if(*bp_physicprev_succ == END_OF_LIST){ // bp的物理prev的succ指向EOL
      //uint64_t **bp_physicprev_prevblock_prev = (uint64_t **) *bp_physicprev_prev;
      uint64_t **bp_physicprev_prevblock_succ = ((uint64_t **) *bp_physicprev_prev) + 1;

      *bp_physicprev_prevblock_succ = END_OF_LIST;
    }else{
      uint64_t **bp_physicprev_prevblock_prev = (uint64_t **) *bp_physicprev_prev;
      uint64_t **bp_physicprev_prevblock_succ = ((uint64_t **) *bp_physicprev_prev) + 1;
      uint64_t **bp_physicprev_succblock_prev = (uint64_t **) *bp_physicprev_succ;

      *bp_physicprev_prevblock_succ = (uint64_t *) bp_physicprev_succblock_prev;
      *bp_physicprev_succblock_prev = (uint64_t *) bp_physicprev_prevblock_prev;
    }
    
    /////////////////////////////////////
    uint64_t **header = (uint64_t **) (*(uint64_t **) bp); // for LIFO, it must be the header
    if(header != explicit_free_list_header){
      printf(" runtime error: in coalesce(), the prev of the LIFO free block is not header\n");
      return NULL;
    }
    *header = (uint64_t *) bp_physicprev_prev;

    uint64_t **bp_succblock_prev = (uint64_t **) *((uint64_t **)bp + 1);
    if(bp_succblock_prev == END_OF_LIST){ // if bp's succ points to EOL(can happen)
      // do nothing
    }else{
      *bp_succblock_prev = (uint64_t *) bp_physicprev_prev;
    }
    /////////////////////////////////////

    *bp_physicprev_prev = *((uint64_t **) bp);
    *bp_physicprev_succ = *((uint64_t **) bp + 1); //~~~~~~~~~~~~~~~~~~~~~~~~
    
    // for safety
    *((uint64_t **)bp) = 0;
    *((uint64_t **)bp + 1) = 0;
    
    explicit_free_list_size--;
    return block_mem(block_prev(block_hdrp(bp)));
  }

  else{ // merge prev and next
    size += block_size(block_prev(block_hdrp(bp))) + 
            block_size(block_next(block_hdrp(bp)));

    block_set_size(block_prev(block_hdrp(bp)), size);
    block_mark(block_prev(block_hdrp(bp)), FREE);
    
    /* Deal with its physical next block */
    uint64_t **bp_physicnext_prev = (uint64_t **) block_mem(block_next(block_hdrp(bp)));
    uint64_t **bp_physicnext_succ = bp_physicnext_prev + 1;
     
    if(*bp_physicnext_succ == END_OF_LIST){
      //uint64_t **bp_physicnext_prevblock_prev = (uint64_t **) *bp_physicnext_prev;
      uint64_t **bp_physicnext_prevblock_succ = ((uint64_t **) *bp_physicnext_prev) + 1;

      *bp_physicnext_prevblock_succ = END_OF_LIST;
    }else{
      uint64_t **bp_physicnext_prevblock_prev = (uint64_t **) *bp_physicnext_prev;
      uint64_t **bp_physicnext_prevblock_succ = ((uint64_t **) *bp_physicnext_prev) + 1;
      uint64_t **bp_physicnext_succblock_prev = (uint64_t **) *bp_physicnext_succ;

      *bp_physicnext_prevblock_succ = (uint64_t *) bp_physicnext_succblock_prev;
      *bp_physicnext_succblock_prev = (uint64_t *) bp_physicnext_prevblock_prev;
    }

    // for safety, no pointer points to these two pointers now
    *bp_physicnext_prev = 0;
    *bp_physicnext_succ = 0;

    /* Deal with its physical prev block */
    uint64_t **bp_physicprev_prev = (uint64_t **) block_mem(block_prev(block_hdrp(bp)));
    uint64_t **bp_physicprev_succ = bp_physicprev_prev + 1;
    
    if(*bp_physicprev_succ == END_OF_LIST){
      //uint64_t **bp_physicprev_prevblock_prev = (uint64_t **) *bp_physicprev_prev;
      uint64_t **bp_physicprev_prevblock_succ = ((uint64_t **) *bp_physicprev_prev) + 1;

      *bp_physicprev_prevblock_succ = END_OF_LIST;
    }else{
      uint64_t **bp_physicprev_prevblock_prev = (uint64_t **) *bp_physicprev_prev;
      uint64_t **bp_physicprev_prevblock_succ = ((uint64_t **) *bp_physicprev_prev) + 1;
      uint64_t **bp_physicprev_succblock_prev = (uint64_t **) *bp_physicprev_succ;

      *bp_physicprev_prevblock_succ = (uint64_t *) bp_physicprev_succblock_prev;
      *bp_physicprev_succblock_prev = (uint64_t *) bp_physicprev_prevblock_prev;
    }
    

    uint64_t **header = (uint64_t **) (*(uint64_t **) bp); // for LIFO, it must be the header
    if(header != explicit_free_list_header){
      printf(" runtime error: in coalesce(), the prev of the LIFO free block is not header\n");
      return NULL;
    }
    *header = (uint64_t *) bp_physicprev_prev;

    uint64_t **bp_succblock_prev = (uint64_t **) *((uint64_t **)bp + 1);
    if(bp_succblock_prev == END_OF_LIST){
      // do nothing
    }else{
      *bp_succblock_prev = (uint64_t *) bp_physicprev_prev;
    }

    *bp_physicprev_prev = *((uint64_t **)bp);
    *bp_physicprev_succ = *((uint64_t **)bp + 1); //~~~~~~~~~~~~~~~~~~~~~~~~~~~
    
    // for safety
    *((uint64_t **)bp) = 0;
    *((uint64_t **)bp + 1) = 0;
    
    explicit_free_list_size = explicit_free_list_size - 2;
    return block_mem(block_prev(block_hdrp(bp)));
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

        // check heap boundary(first block next to explicit_free_list_header)
        // check epilogue block
        if(block_size((uint32_t *)mem_heap_lo() + 2) != 0){
          printf(" checkheap: heap low boundary size error\n");
          return 1;
        }
        if(block_free((uint32_t *)mem_heap_lo() + 2) != 1){
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

        int freeblock_num_iterate = 0; // free block count by iterating every block

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
              if(block_size(block_hdrp(ptr)) < 6){
                printf(" checkheap: size in header less than 6-words-minimum for explicit free list\n");
                return 1;
              }
            }
            if(block_size(block_hdrp(ptr)) != block_size(block_ftrp(ptr))){
              printf(" checkheap: size in header not equal to size in footer\n");
              return 1;
            }
            if(block_free(block_hdrp(ptr)) != block_free(block_ftrp(ptr))){
              printf(" checkheap: free/alloc bit in header not equal to free/alloc bit in footer\n");
              return 1;
            }

            // check no two consecutive free blocks
            if(free_block_flag == 0 && block_free(block_hdrp(ptr)) == 1){
              freeblock_num_iterate++; // add free block count
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
                break; // exit while loop
              }else{
                printf(" checkheap: fatal error: this should be a new header, but its value shows that it is an epilogue\n");
                return 1;
              }
            }else{
              ptr = block_mem(block_next(block_hdrp(ptr))); // move to next block
            }
        }

        // explicit free list check
        // check explicit_free_list_size
        if(explicit_free_list_size < 0){
          printf(" checkheap: explicit_free_list_size < 0\n");
          return 1;
        }
        if((explicit_free_list_size == 0 && *explicit_free_list_header != END_OF_LIST) ||
           (*explicit_free_list_header == END_OF_LIST && explicit_free_list_size != 0)) {
          printf(" checkheap: explicit free list seems to be empty, but size does not match with header\n");
          return 1;
        }

        uint64_t **iter_explicit_free_list = explicit_free_list_header;

        int freeblock_num_traverse = 0; // free block count by traversing through pointers

        while(*iter_explicit_free_list != END_OF_LIST){
          if(*iter_explicit_free_list < (uint64_t *) mem_heap_lo() ||
             *iter_explicit_free_list >= (uint64_t *) mem_heap_hi()){
            printf(" checkheap: free list pointer is not between mem_heap_lo and mem_heap_hi\n");
            return 1;
          }

          if(iter_explicit_free_list == explicit_free_list_header){ // header指针与后指针的consistency检查
            uint64_t **header_linknext_prev = (uint64_t **) *iter_explicit_free_list;
            if(iter_explicit_free_list != (uint64_t **) *header_linknext_prev){
              printf(" checkheap: header linknext's prev != header");
              return 1;
            }
            // 直接到next free block,因为header没有succ
            iter_explicit_free_list = (uint64_t **) *iter_explicit_free_list;
            freeblock_num_traverse++;
            continue;
          }else{ // 需要将iter指针向后移动一格至其succ处
            uint64_t **iter_explicit_free_list_succ = iter_explicit_free_list + 1;
            if(*iter_explicit_free_list_succ == END_OF_LIST){
              break;
            }
            uint64_t **iter_explicit_free_list_succ_linknext_prev = 
                                      (uint64_t **) *iter_explicit_free_list_succ;
            if(iter_explicit_free_list != 
                                      (uint64_t **) *iter_explicit_free_list_succ_linknext_prev){
              printf(" checkheap: iter succ linknext's prev != iter prev\n");
              return 1;
            }
            // move to the next free block
            iter_explicit_free_list = (uint64_t **) *iter_explicit_free_list_succ;
            freeblock_num_traverse++;
          }
        }

        if(freeblock_num_traverse != freeblock_num_iterate){
          printf(" checkheap: free blocks number not match\n");
          return 1;
        }
        
    }
    return 0;
}



