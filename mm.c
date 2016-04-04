/*
 * mm.c
 *
 * Yusuf Roohani - yhr
 *
 * A dynamic memory allocating library 
 * This malloc uses an 8 byte word size with an 8-byte alignment. The
 * minimum block size is one word for the data and one word for overheads,
 * a total thus of 16 bytes. 
 *
 * The allocated blocks are traversed using an implicit list. The header and 
 * footer for each block use only 4 bytes each and are packed within a single 
 * word. Thus, one word aligned to 8 bytes contains the header for the current 
 * block and the footer for the previous block. Within this, the footer is 
 * aligned to 4 bytes. The least significant bit of the header and footer 
 * are used to store the allocation bit.
 *
 * The free blocks are managed using segregated free lists. 11 free lists 
 * each represent a range of blocks lying within succesive powers of 2, 
 * starting from 2^6. Eg:- The first list contains blocks between 2^6 and
 * 2^7, the next contains 2^7 and 2^8 ... the final list contains free blocks
 * sized between 2^17 to infinity (or 2^32). Each free block has a next pointer
 * and a previous pointer. These are stored as offsets to the start of the heap
 * and are thus both packed into a single word. Each list is searched using a
 * first fit algorithm, however the largest size bin list is searched using a
 * best fit algorithm.
 *
 * A heap checker for debugging purposes has been included at the end of the
 * file, followed by a set of helper functions. Please make sure to read where
 * the debugging function can be called effectively and where its return values
 * are undefined.
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

/* Paramters  */
#define WSIZE 8
#define DWSIZE 16
#define MIN_SIZE 16
#define PAGESIZE (1<<8)
#define ALIGNMENT 8
#define NO_LISTS 11

/* General Pointer Macros */
#define MAX(x,y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((unsigned)((size) | (alloc)))
#define GET(p) (*(size_t *)(p))
#define GET_INT(p) (*(unsigned *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))
#define PUT_INT(p, val) (*(unsigned*)(p) = (val))

/* Pointer packing into single word using heap offsets. These
 * pointers are used to pack two pointers into a single word. This is
 * done by converting each pointer into a 4byte offset from the start
 * of the heap. This also leaves 3 bytes at the end of each pointer
 * for additional information such as an allocate bit.
 *
 * So a free block looks like this, using a minimum of only 2 words instead
 * of 3.
 * --------------------------
 *       FULL   HEADER      |   <----- This is defined in next section
 * --------------------------
 *     PREVP   |    NEXTP   |   <----- This is what the following macros
 * -------------------------           are for
 *    . . . . . . . . . .   |
 *    .. . . . . . . . .
 *     . . . . . . . . ..   |
 *
 * -------------------------
 */

/* The very first allocated byte in the heap*/
#define FULL_HEAP ((char *)heap - ((NO_LISTS + 1) * WSIZE))  
#define INDEX ((size_t) FULL_HEAP)

/* 32 bits of zeros followed by 32 bits of 1's, a useful bit pattern */
#define SPLIT ((((size_t)1<<32)) - 1)

/* Mask to see only the first/last 32 bits */
#define SEE_NEXT(p) ((size_t)p & SPLIT)
#define SEE_PREV(p) (((size_t)p & ~SPLIT)>>32)

/* Convert the first/last 32 bits of the word into a full 64 bits pointer */
#define NEXTP(p) (char *) ((SEE_NEXT(p)) ? (INDEX + (SEE_NEXT(p))) : (0))
#define PREVP(p) (char *) ((SEE_PREV(p)) ? (INDEX + (SEE_PREV(p))) : (0))

/* Set the first/last 32 bits as zero, prevents complicated conditions for 
 * zero checking */
#define CLEAR_NEXT(dest)    PUT(dest, (GET(dest) & ~SPLIT))
#define CLEAR_PREV(dest)    PUT(dest, (GET(dest) & SPLIT))

/* Convert given 64 bit pointer into a 32 bit (offset) form and place it in the
 * first/last 32 bits of the word (dest) */
#define PUT_NPTR(dest, val)  PUT(dest, GET(dest) | ((size_t)val - INDEX))  
#define PUT_PPTR(dest, val)  PUT(dest, GET(dest) | (((size_t)val - INDEX)<<32)) 

/* Clears and then sets the first/last 32 bits to the given pointer */
#define PUT_PREV(dest, val) CLEAR_PREV(dest); PUT_PPTR(dest, val)
#define PUT_NEXT(dest, val) CLEAR_NEXT(dest); PUT_NPTR(dest, val) 

/* Enhanced header - Instead of assigning one full word for both the
 * header and the footer, they were each converted into 4 byte unsigned
 * integers and fit into a single word. This saved a full word on overhead
 * in both allocated and free bytes.
 *
 * This is what an allocated/free byte looks like
 *-------------------------------------------
 *   CURRENT BLK HEADER |   PREV BLK FOOTER |  <--- This full (8byte) word is
 *-------------------------------------------       referred to as the FULL_HDR
 *   . . . . . . . . . . . . . . . . . . .
 *   . . . . . . . . . . . . . . . . . . .
 *   . . . . . . . . . . . . . . . . . . .
 *   . . . . . . . . . . . . . . . . . . .
 *   . . . . . . . . . . . . . . . . . . .
 * -----------------------------------------
 *   NEXT BLK HEADER |  CURRENT BLK FOOTER  |
 *  ---------------------------------------
 */

/* The full word where the header of the current block and the footer of the
 * previous block are located. Both are 4 bytes each */
#define FULL_HDR(bp)  ((char *)(bp) - WSIZE)

/* Only look the last/first 4 bytes */
#define PREV(p) ((p)+4) 
#define THIS(p) (p)

/* Useful Implicit list macros */
#define GET_SIZE(p) (GET_INT(p) & ~(0x7))
#define GET_ALLOC(p) (GET_INT(p) & 0x1)
#define HDR(bp)  THIS(FULL_HDR(bp))
#define FTR(bp)  PREV((char *)(bp) + GET_SIZE(HDR(bp)) - WSIZE)
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(THIS(FULL_HDR(bp))) )
#define PREV_BLK(bp) ((char *)(bp) - GET_SIZE(PREV(FULL_HDR(bp))) )

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

/* Define global variables */
static char *heap;
//static char *free_list;
int errno;

/* Function prototypes */
void *coalesce(void *bp);
void *grow_heap(size_t words);
void *find_fit(size_t asize);
void place(void *bp, size_t asize);
void lifo_insert(void *bp);
void remove_from_list(void *bp);
static int in_heap(const void *p);
static int aligned(const void *p);
void point_check(const void *bp, char* type, int lineno);
int find_size_bin(int asize);
void check_pro_epi(int lineno);
void check_head_foot(void *bp, int lineno);
void check_match_bin(void *bp, int lineno, int count, int x);
void check_coalesce(void *bp, int lineno);

/*
 * mm_init - Initialize heap: Return -1 on error, 0 on success.
 * The heap starts with a padding word (8 bytes) follow by NO_LISTS bytes
 * for segregated list start pointers. 2 bytes are added on top of this
 * for storing the prologue and the epilogue. The heap is grown to one 
 * pagesize.
 */
int mm_init(void) {
   char *bp;
   if ((heap = mem_sbrk((3 + NO_LISTS) * WSIZE)) == NULL){
      return -1;
   }
   PUT(heap, PACK(0,0)); 			        // Align to even
   PUT_INT(THIS(heap + (NO_LISTS + 1)*WSIZE), PACK(WSIZE, 1)); // Header
   PUT_INT(PREV(heap + (NO_LISTS + 2)*WSIZE), PACK(WSIZE, 1)); // Footer
   
   /* Epilogue header is packed into same block as prologue footer */
   PUT_INT(THIS(heap + (NO_LISTS + 2)*WSIZE), PACK(0, 1));     
   
   /* Initialize free lists for each sub group within the heap */
   heap += (2+NO_LISTS)*WSIZE;
   for (int x = 0; x < NO_LISTS; x++){
      PUT((char *)FULL_HEAP + (x * WSIZE), (size_t)0);
   }
   
   if((bp = grow_heap(PAGESIZE/WSIZE)) == NULL){
      return -1;
   }
   return 0;
}


/*
 * grow_heap - Grows heap. Allocates new page as free and
 * reassigned an allocated epilogue to mark end of heap.
 */
void *grow_heap(size_t words){
   char *bp;
   unsigned size;
   
   /* New page bytes should be a multiple of 8 */
   size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
   if ((long int)(bp = mem_sbrk(size)) < 0){
      return NULL;
   }

   /* Set the new page as free */
   PUT_INT(HDR(bp), PACK(size, 0));
   PUT_INT(FTR(bp), PACK(size, 0));
   PUT_INT(HDR(NEXT_BLK(bp)), PACK(0, 1));
   return coalesce(bp);
}
/*
 * malloc - Allocates size bytes on heap. Searches for a fit using segregated
 * free lists. Calls for a new page if there is no fit. Return NULL if not
 * enough memory is available.
 */
void *malloc (size_t size) {
   unsigned asize;
   unsigned extendsize;
   char *bp;

   if (size <= 0)
      return NULL;

   /* Adjust block size to a minimum of two words and align */
   if (size <= WSIZE)
      asize = WSIZE + WSIZE;
   else
      asize = ALIGN(size + WSIZE);

   /* Search for fit*/
   if ((bp = find_fit(asize)) != NULL){
      place(bp,asize);
      return bp;
   }
   /* No fit, get more memory */
   extendsize = MAX(asize, PAGESIZE);
   if ((bp = grow_heap(extendsize/WSIZE)) == NULL){
      return NULL;
   }
   place(bp, asize);
   return bp;
}

/*
 * find_size_bin - Calculates approporiate size bin for given block of size
 * 'asize'. The range of blocks in each range are successive powers of 2
 * starting with 2^7. So, the first list has a size range of 2^7 to 2^8, the
 * next list has a range 2^8 to 2^9 ... the final list has a range of 2^17 to
 * infinity (or 2^32).
 */
int find_size_bin(int asize){
   int size_bin = 0;
   int cut_off = 64;
   while (asize > (cut_off-1)){
      asize = asize>>1;
      size_bin += 1;
   }
   
   if (size_bin >= NO_LISTS-1){
      size_bin = (NO_LISTS-1);
   }
   return size_bin;
}

/*
 * find fit - Scans free lists for suitable size bin starts with minimum
 * with minimum size and proceeds till largest size. First fit scheme is used 
 * for all size bins except the largest bin where a best fit scheme is used.
 */

void *find_fit(size_t asize){
   char *free_list;
   void *bp;
   int size_bin;
   size_bin = find_size_bin(asize);
   char *best_fitp;
   size_t best_fit;   
   best_fitp = NULL;
   best_fit = (1<<31);

   for (int x = size_bin; x < NO_LISTS; x++){
      free_list = (FULL_HEAP + (x*WSIZE));
      /* If a size bin is empty move to next bin */
      if (GET(free_list) == (size_t)0){    
	 continue;
      }
      bp = (char *)GET(free_list); 

      /* Best fit for largest list */
      if (x == NO_LISTS-1){
      do{
	    if (asize <= (size_t)GET_SIZE(HDR(bp))) {
	       if ((size_t)GET_SIZE(HDR(bp)) <= best_fit){
		  best_fitp = bp;
		  best_fit = (size_t)GET_SIZE(HDR(bp));
               }
	    }
	    bp = (char *)NEXTP(GET(bp));
	 } while ( bp != 0);
      }

      /* First fit for all other size lists */
      else {do{ 
	 if (asize <= GET_SIZE(HDR(bp))) {
	    return bp;
	 }
	 bp = (char *)NEXTP(GET(bp));
      } while ( bp != 0); 
   }
   }

   return best_fitp;
}

/*
 * place - Allocates a block of size asize at assigned location bp. Creates
 * a new free block if there is sufficient leftover space. Otherwise the 
 * full block is allocated
 */
void place(void *bp, size_t asize){
   size_t init_size;
   init_size = GET_SIZE(HDR(bp));
   if ((init_size - asize) >= (MIN_SIZE)){
      remove_from_list(bp);
      PUT_INT(HDR(bp), PACK(asize, 1));
      PUT_INT(FTR(bp), PACK(asize, 1));

      bp = NEXT_BLK(bp);
      PUT_INT(HDR(bp), PACK(init_size - asize, 0)); 
      PUT_INT(FTR(bp), PACK(init_size - asize, 0));
      lifo_insert(bp);
   }
   else { 
      remove_from_list(bp);
      PUT_INT(HDR(bp), PACK(init_size, 1));
      PUT_INT(FTR(bp), PACK(init_size, 1)); 
   }
}

/*
 * lifo_insert - Inserts block bp into approporiate free list at 
 * the start of list
 */
void lifo_insert(void *bp){
   char *free_list;
   int size_bin;
   size_bin = find_size_bin(GET_SIZE(HDR(bp)));
   free_list = (char *)(FULL_HEAP + (size_bin*WSIZE));

   /* If list isn't empty */
   if (GET(free_list) != (size_t)0){    				
      PUT_NEXT(bp, (size_t)(GET(free_list))); // Set next pointer of current
      PUT_PREV((GET(free_list)), bp);         // Set prev pointer of next
   }
   
   /* If list is empty */
   else {
      CLEAR_NEXT(bp);                         // Set prev pointer of current
   }

   /* In any case */
   PUT(free_list, (size_t)bp);                // Set free list start pointer
   CLEAR_PREV(bp);       	              // Set current prev pointer
}

/*
 * remove_from_list - Removes block bp from appropriate free list, adjusts 
 * pointers of previous and next blocks accordingly.
 * WARNING! Behaviour of mm_checkheap as a debugger when called from this
 * function is only defined when coalescence checking is turned off.
 */
void remove_from_list(void *bp){
   char *free_list;
   int size_bin;
   size_bin = find_size_bin(GET_SIZE(HDR(bp)));
   free_list = (char *)(FULL_HEAP + (size_bin*WSIZE));

   /* If block exists behind */
   if (PREVP(GET(bp)) != 0 ){
        		
      /* If block exists ahead as well*/
      if (NEXTP(GET(bp)) != 0){
         
         /* Make previous block's next pointer skip present block */
	 PUT_NEXT(PREVP(GET(bp)), (size_t)NEXTP(GET(bp)));
         /* Make next block's prev pointer skip present block */    
	 PUT_PREV((NEXTP(GET(bp))), (size_t)PREVP(GET(bp)));     
      }
      
      /* If no blocks ahead */
      else {
         /* Clear previous block's next pointer */
	 CLEAR_NEXT(PREVP(GET(bp))); }           
   }

   /* If no blocks behind, only root */
   else{		

      /* Make free list start pointer skip present block */
      PUT(free_list,(size_t)NEXTP(GET(bp)));
      
      /* Clear next blocks previous pointer since it is now at start */
      if (NEXTP(GET(bp)) != 0 ){
	 CLEAR_PREV(NEXTP(GET(bp)));
      }
   }
}

/*
 * free - Frees allocated block, takes its pointer.
 * Calls functions for list manipulation.
 */
void free (void *bp) {
   if(!bp) return;
   
   size_t size = (GET_SIZE(HDR(bp)));
   PUT_INT(HDR(bp), PACK(size,0));
   PUT_INT(FTR(bp), PACK(size, 0));
   
   // Coalesce calls the free list manipulating functions
   coalesce(bp);
}

/*
 * coalesce - Coalesce freed block with adjacent free blocks. Removes 
 * blocks and inserts/reinserts them depending upon coalescing conditions.
 * WARNING! Behaviour of mm_checkheap as a debugger when called from this
 * function is only defined when coalescence checking is turned off. 
 */
void *coalesce(void *bp){
   size_t prev_alloc = GET_ALLOC(FTR(PREV_BLK(bp)));
   size_t next_alloc = GET_ALLOC(HDR(NEXT_BLK(bp)));
   unsigned size = GET_SIZE(HDR(bp));

   // No coalescing required, simply inserts current
   if(prev_alloc && next_alloc){
      lifo_insert(bp);
      return bp;
   }

   // Removes next from list, coalesces with current and inserts current
   else if (prev_alloc && !next_alloc){
      remove_from_list(NEXT_BLK(bp));
      size += GET_SIZE(HDR(NEXT_BLK(bp)));
      PUT_INT(HDR(bp), PACK(size, 0));
      PUT_INT(FTR(bp), PACK(size, 0));
      lifo_insert(bp);
      return bp;
   }

   // Removes current from list, coalesces with prev and inserts prev
   else if (!prev_alloc && next_alloc){
      remove_from_list(PREV_BLK(bp));
      size += GET_SIZE(HDR(PREV_BLK(bp)));
      PUT_INT(HDR(PREV_BLK(bp)), PACK(size, 0));
      PUT_INT(FTR(bp), PACK(size, 0));
      lifo_insert(PREV_BLK(bp));
      return (PREV_BLK(bp));
   }

   // Removes next and prev, coalesces with current and inserts prev
   else {
      remove_from_list(PREV_BLK(bp));
      remove_from_list(NEXT_BLK(bp));
      size += GET_SIZE(HDR(PREV_BLK(bp))) +\
	      GET_SIZE(FTR(NEXT_BLK(bp)));
      PUT_INT(HDR(PREV_BLK(bp)), PACK(size, 0));
      PUT_INT(FTR(NEXT_BLK(bp)), PACK(size, 0));
      lifo_insert(PREV_BLK(bp));
      return (PREV_BLK(bp));
   }
}
/*
 * realloc - Reallocate existing block and data to a new block
 */
void *realloc(void *oldptr, size_t size) {
   unsigned oldsize, asize;
   char *bp;
   size_t buff[1];
   size_t* buffer = buff; 

   /* Adjust block size */
   if (size <= WSIZE)
      asize = WSIZE + WSIZE;
   else
      asize = ALIGN(size + WSIZE);

   /* If size == 0 then this is just free, and we return NULL. */
   if(size == 0) {
      free(oldptr);
      return NULL;
   }

   /* If oldptr is NULL, then this is just malloc. */
   if(oldptr == NULL) {
      return malloc(size);
   }

   /* Save data that will be written over by free-list pointers */
   memcpy(buffer, oldptr, WSIZE); 
   
   /* Unallocate previous block and search for fit as with malloc */
   oldsize = GET_SIZE(HDR(oldptr));
   free(oldptr);

   if((bp = find_fit(asize)) == NULL){
      size_t extendsize = MAX(asize, PAGESIZE);
      if ((bp = grow_heap(extendsize/WSIZE)) == NULL){
	 return NULL;
      }
   }
   
   /* Copy previous contents to new block */
   if(asize < oldsize){ 
      oldsize = asize;
   }

   oldsize = oldsize - WSIZE;
   memcpy((char *)bp + WSIZE, (char *)oldptr + WSIZE, oldsize - WSIZE);
   place(bp, asize);
   memcpy((char *)bp, (char *)buffer, WSIZE);
   return bp;

}

/*
 * calloc - Allocates a block, intialized to zero
 */
void *calloc (size_t nmemb, size_t size) {
   void *bp;
   if ((bp = malloc(nmemb*size)) != NULL){
      for(unsigned i = 0; i < nmemb*size; i += 4){
	 PUT_INT((bp+i), 0);
      }
   }
   return NULL;
}


/*
 * in_heap - Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
   return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * aligned - Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
   return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap - Checks the heap for inconsistencies in data structure
 * invariants. First checks prologue and epilogue, then implicit list members
 * followed by segregated list invariants and list members. 
 * WARNING: Behaviour of mm_checkheap is undefined in mm_init().
 * WARNING: Behaviour of mm_checkheap as a debugger with coalescence checking
 * is not defined in coalesce() and remove_from_list() and in sections of code 
 * where blocks have been freed but not coalesced.
 * WARNING: Behaviour of mm_checkheap is undefined in find_size_bin which is 
 * called by mm_checkheap, resulting in recursion.
 */
void mm_checkheap(int lineno) {
   char *free_list;
   char* bp;  
   int count;

   /* Check prologue and epilogue blocks*/
   check_pro_epi(lineno);

   /* Check allocated blocks in implicit list*/
   for (bp = heap; GET_SIZE(HDR(bp)) > 0; bp = NEXT_BLK(bp)){
      point_check(HDR(bp), "Header of allocated block", lineno);
      point_check((char *)FTR(bp) - 4, "Footer of allocated block", lineno);
      check_head_foot(bp, lineno);
      check_coalesce(bp, lineno);
      point_check(bp, "Allocated block", lineno);
      }
   
   /* Check free blocks in all free lists*/
   for (int x = 0; x < NO_LISTS; x++){
      free_list = (char *)(FULL_HEAP+ (x*WSIZE));
      if((bp = (char *)GET(free_list)) != NULL){
	 point_check(bp, "List start pointer for list ", lineno);
	 count = 0;
	 do{
	    count = count +1;
	    point_check(bp, "Free block", lineno);
	    point_check(HDR(bp), "Header for Free block", lineno);
	    /* Since the footer is an int which starts at the 4th byte */
	    point_check((char *)FTR(bp) - 4, "Footer for Free block", lineno);

	    check_head_foot(bp, lineno);            
	    check_coalesce(bp, lineno);
	    check_match_bin(bp, lineno, count, x);
	    bp = NEXTP(GET(bp));
	 } while (bp != (size_t)0);
      }
   }
}

/*
 * point_check - Checks whether a given pointer bp is in heap and is aligned.
 * String 'type' can be used for labelling errors. Takes line number from 
 * heap checker to display in error message.
 */
void point_check(const void *bp, char *type, int lineno){
   if (!in_heap(bp)){
      printf("%s %p not in heap \n", type, bp);
      /* mem_heap_hi() return the final byte not the final word */
      printf("ERROR Heap top is %p (at line %d) \n",\
	    (char *)mem_heap_hi() - 7, lineno);
      exit(1);
   }
   if (!aligned(bp)){
      printf("ERROR %s %p not aligned (at line %d)\n", type, bp, lineno);
      exit(1);
   }
}

/*
 * check_pro_epi - Checks whether the prologue and epilogue are consistent
 * with initial definition. Takes line number from heap checker to display
 * in error message.
 */
void check_pro_epi(int lineno){
   unsigned size_check;
   int alloc_check;
   for (int flag = 0; flag < 3; flag++){
      char *locate = THIS(heap - WSIZE);
      char *type = "Prologue Header";
      unsigned test = WSIZE;
      if (flag == 1){
	 locate = PREV(heap);
	 type = "Prologue Footer";
      }
      else if (flag == 2){
	 /* mem_heap_hi() return the final byte not the final word */
	 locate = THIS((char *)mem_heap_hi() - 7);
	 type = "Epilogue Header";
	 test = 0;
      }

      if (THIS(locate) == NULL){
	 printf(" WARNING!! %s not assigned yet (at line %d)\n", type, lineno);
	 break;
      }
      if ((size_check = GET_SIZE(locate)) != test ){
	 printf("%s ERROR Size: %d (at line %d)\n", type, size_check, lineno);
	 exit(1);
      }
      if ((alloc_check = GET_ALLOC(locate)) != 1 ){
	 printf("%sERROR Allocated: %d (at line %d)\n", type, alloc_check,\
	       lineno);
	 exit(1);
      }
   }
}
/*
 * check_head_foot - Checks whether size and allocation of header and footer 
 * match. Checks whether block is greater than minimum size.
 */
void check_head_foot(void *bp, int lineno){
   int var1,var2;
   if ((var1 = GET_SIZE(HDR(bp))) != (var2 = GET_SIZE(FTR(bp)))){
      printf("ERROR Header-Footer size mismatch in allocated block %p - \
	    %d vs  %d, (at line %d) \n", bp, var1, var2, lineno);
      exit(1);
   }

   if ((var1 < MIN_SIZE) && (bp != (heap))){
      printf("ERROR Block %p smaller of size %d than minimum size \
	    (at line %d)\n", bp, var1, lineno);
      exit(1);
   }

   if ((var1 = GET_ALLOC(HDR(bp))) != (var2 = GET_ALLOC(FTR(bp)))){ 
      printf("ERROR Header-Footer allocation mismatch in allocated\
	    blocks- %d vs  %d, (at line %d) \n", var1, var2, lineno);
      exit(1);
   }
}

/*
 * check_match_bin - Checks whether the forward pointer of current block
 * matches with the previous pointer for the next block and whether all 
 * the pointers point to the heap. Also checks wether the current block
 * is in the correct segregated list. 
 */
void check_match_bin(void *bp, int lineno, int count, int x){
   /* If bp is the first block then check if previous pointer points to 0 */
   if (count == 1){
      void *prev_ptr; 
      if ((prev_ptr = PREVP(GET(bp))) != 0){
	 printf("ERROR Prev pointer of first entry in list %d is \
	       pointing to %p", x, prev_ptr);
	 exit(1);
      }
   }

   /* Checks whether the forwards pointer of current block matches with
    * the previous pointer of the next block. First checks whether all 
    * pointers point to the heap.
    */
   if ((size_t)NEXTP(GET(bp)) != 0){
      point_check(NEXTP(GET(bp)),"Next pointer ",lineno);
      point_check(NEXTP(GET(bp)),"Prev pointer ",lineno);
      if ((char *)(PREVP(GET(NEXTP(GET(bp))))) != (char *)(bp)){
	 printf("ERROR Free list %d - consecutive pointers mismatch at \
	       block %d (%p) (at line %d) \n", x, count, bp, lineno);
	 exit(1);
      }
   }
   unsigned size = GET_SIZE(HDR(bp));
   int size_bin;
   if ((size_bin = find_size_bin(size)) != x){
      printf("ERROR Free list %d - block %d (%p) of size %d in wrong size\
	    bin (at line %d) \n", x, count, bp, size, lineno);
      exit(1);
   }
}

/*
 * check_coalesce - Checks whether all adjacent free blocks have been coalesced
 * WARNING! This function's behaviour is undefined for calls from:
 * remove_from_list(), coalesce(). Please be aware of code sections where 
 * blocks have been freed but not coalesced - ths is not always an error.
 */
void check_coalesce(void *bp, int lineno){
   /* Get allocated bit for previous, next and current blocks */
   size_t prev_alloc = GET_ALLOC(FTR(PREV_BLK(bp)));
   size_t next_alloc = GET_ALLOC(HDR(NEXT_BLK(bp)));
   size_t alloc = GET_ALLOC(HDR(bp));

   /* Only check free blocks */ 
   if(alloc == 0){
      if (prev_alloc == alloc){ 
	 printf("ERROR Previous block(%p) allocation %ld is same as current\
	       block %p (at line %d)\n", PREV_BLK(bp), prev_alloc, bp, lineno);
	 printf("WARNING please check location of heap checker call \n");
	 exit(1);
      }

      if (next_alloc == alloc){
	 printf("ERROR Next block(%p) allocation %ld is same as current \
	       block %p (at line %d)\n", NEXT_BLK(bp), next_alloc, bp, lineno);
	 printf("WARNING please check location of heap checker call \n");
	 exit(1);
      }
   }
}
