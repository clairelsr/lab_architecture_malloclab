/*
* this solution implements the explicit memory, the allocator allocates spaces but also frees ones (main difference with the naive implicit)
* the structure that enables is to add a free_listp (in 2 senses, one pointer to the next and one point pointer to the previous element) plus a heap_listp (the general pointer to the
memor, similar to the implicit memory)


* to see the naive version, please have a look on the file : mm_backup.c
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
    "Les raisins",
    /* First member's full name */
    "Claire Lasserre",
    /* First member's email address */
    "claire.lasserre@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Ines Potier",
    /* Second member's email address (leave blank if none) */
    "ines.potier@polytechnique.edu"
};
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Additional Macros defined*/
#define WSIZE 4                                                                             //Size of a word 
#define DSIZE 8                                                                             //Size of a double word
#define CHUNKSIZE (1<<12)                                                                   //Initial heap size                                                                    
#define MAX(x ,y)  ((x) > (y) ? (x) : (y))                                                  //Finds the maximum of two numbers
#define PACK(size, alloc)  ((size) | (alloc))                                               //Put the size and allocated byte into one word
#define GET(p)  (*(size_t *)(p))                                                            //Read the word at address p
#define PUT(p, value)  (*(size_t *)(p) = (value))                                           //Write the word at address p
#define GET_SIZE(p)  (GET(p) & ~0x7)                                                        //Get the size from header/footer
#define GET_ALLOC(p)  (GET(p) & 0x1)                                                        //Get the allocated bit from header/footer
#define HDRP(bp)  ((void *)(bp) - WSIZE)                                                    //Get the address of the header of a block
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)                               //Get the address of the footer of a block
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))                                  //Get the address of the next block
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))                          //Get the address of the previous block
#define NEXT_FREEP(bp)  (*(void **)(bp + DSIZE))                                            //Get the address of the next free block
#define PREV_FREEP(bp)  (*(void **)(bp))                                                      //Get the address of the previous free block

                                                 


//Function prototypes for helper routines
static void *extend_heap(size_t words);
static void place(void *bp, size_t size);
static void *find_fit(size_t size);
static void *coalesce(void *bp);
static void insertf(void *bp);
static void remove_block(void *bp);

static char *heap_listp = 0;                                                                //Pointer to the first block
static char *free_listp = 0;                                                                //Pointer to the first free block

/* Initializes the malloc, Return 0 if successful -1 if unsucessful */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*DSIZE)) == NULL){                                          // Check if there is enough space to create the heap
        return -1;
    }

    PUT(heap_listp, 0);                                                                   // Padding at the start of heap
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));                                              // Header block 
    PUT(heap_listp + DSIZE, 0);                                                           // Put the previous pointer (diff from implicit memory)
    PUT(heap_listp + DSIZE + WSIZE, 0);                                                   // Put the next pointer (diff from implicit memory)
    PUT(heap_listp + 2*DSIZE , PACK(DSIZE, 1));                                           // Footer block of the prologue
    PUT(heap_listp + WSIZE + 2*DSIZE , PACK(0, 1));                                       // Epilogue header
    free_listp = heap_listp + DSIZE;                                                      // Initialize the heap list pointer
    heap_listp +=2*WSIZE;                                                                 // Initialize the free list pointer
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL){                                           // Extend the empty heap with a free block of CHUNKSIZE bytes,and return error if impossible
         return -1;
    }

    return 0;
}

/* Allocates a block with at least the specified size of payload */
void *mm_malloc(size_t size)
{
    size_t asize;                                                                    // The size of the adjusted block
    size_t extendsize;                                                               // The amount by which heap is extended if no fit is found
    char *bp;                                                                           

    if(size == 0){                                                                         
        return NULL;
    }
    
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    if (asize <3*DSIZE){                                                            // In the case of explicit memory, each created block has a minimum size of 3*DSIZE
       asize= 3*DSIZE;
    }
  
    if((bp = find_fit(asize)) !=NULL){                                             // Traverse the free list to find a fit 
        place(bp, asize);                                                          //if a place is found then place the blocknd return bp
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);

    if((bp = extend_heap(extendsize / WSIZE)) == NULL){                           //else the goal is to extend the heap and then place the block and return bp
        return NULL;                                                              // if the heap  can not be extended then return null-> the malloc cannot be done                                                              
    }

    place(bp, asize);                                                            // Place the block in the newly extended space
    return bp;
}

/* frees the block given in argument as a pointer */
void mm_free(void *bp)
{
   size_t size = GET_SIZE(HDRP(bp));                                             //  Get the total block size
   PUT(HDRP(bp),PACK(size,0));                                                   // Update to 0 the header and footer of bp because the block is free                                        
   PUT(FTRP(bp),PACK(size,0));
   coalesce(bp);                                                                 // Coalesce and add the block to the free list
}

/* Reallocates a block of memory givent as argument *prt,  return The block pointer to the reallocated block */

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;                                                             // Initialization of the neew block                                                             
    size_t copySize;
   
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    
    if (size < copySize)
      copySize = size;
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

      

/* Extends the heap with free block */
static void* extend_heap(size_t words){
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;                                // Allocate even number of  words to maintain alignment 
                          
    if(((long)(bp = mem_sbrk(size))) == -1){                                                 // if error in extending heap space return null
        return NULL;
    }
    
    PUT(HDRP(bp), PACK(size, 0));                                                           // Free block header
    PUT(FTRP(bp), PACK(size, 0));                                                           // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                                                   // New epilogue header
                                                     
    return coalesce(bp);                                                                    //Coalesce if the previous block was free and add the block to the free list
}

/* Combines the newly freed block with the adjacent free blocks if any */
static void *coalesce(void *bp){
   size_t prev_alloc = 1;
   if (PREV_BLKP(bp) != bp){
      prev_alloc= GET_ALLOC(FTRP(PREV_BLKP(bp)));
   }
         
   size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
   size_t size = GET_SIZE(HDRP(bp)); 
   
   // CASE 1 (book)
   if(prev_alloc && next_alloc){
      insertf(bp);
      return bp;
   }
   
   // CASE 2(book)
   else if(prev_alloc && !next_alloc){
      size+= GET_SIZE(HDRP(NEXT_BLKP(bp)));                                               // New size of the free block (current + next)
      remove_block(NEXT_BLKP(bp));                                                        // Remove the next block of the free list because now it is combined 
      PUT(HDRP(bp),PACK(size,0));                                                         // Free block header
      PUT(FTRP(bp),PACK(size,0));                                                         // Free block footer
   }
   
   // CASE 3(book)
   else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                              // New size of the free block (current + previous)
        bp = PREV_BLKP(bp);                                                                
        remove_block(bp);                                                                   // Remove the previous block
        PUT(HDRP(bp), PACK(size, 0));                                                       // Free new block header 
        PUT(FTRP(bp), PACK(size, 0));                                                       // Free new block footer 
   }
   
   // CASE 4(book)
   else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));              // New size of the free block (current + previous + next)
        remove_block(PREV_BLKP(bp));                                                        // Remove the block previous 
        remove_block(NEXT_BLKP(bp));                                                        // Remove the block next t
        bp = PREV_BLKP(bp);                                                                 // Update the block pointer to the previous block
        PUT(HDRP(bp), PACK(size, 0));                                                       // Update the new block header
        PUT(FTRP(bp), PACK(size, 0));                                                       // Update the new block footer
}

   insertf(bp); 
   return bp;
}

/* Inserts a block at the front of the free list */
static void insertf(void *bp){
    NEXT_FREEP(bp) = free_listp;                                                            
    PREV_FREEP(free_listp) = bp;                                                            
    PREV_FREEP(bp) = NULL;                                                                  
    free_listp = bp;                                                                        
}

/* Removes a block from the free list */
static void remove_block(void *bp){
    if(PREV_FREEP(bp)){                                                                     
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);                                        
    }

    else{                                                                                   
        free_listp = NEXT_FREEP(bp);                                                        
    }
    PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);                                            
}

/* Finds a fit for the block of a given size */
static void *find_fit(size_t asize){
    void *bp;
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0 ; bp = NEXT_FREEP(bp)){                   // Traverse the entire free list
        if( GET_SIZE(HDRP(bp))>=asize){                                                    // If asize can integrate a free block -. then we find our candidate
            return bp;                                                                     
        }
    }
    return NULL;                                                                           // If no fit in all the list -. fit action cannot be done, return NULL
}

/* Places a block of specified size to start of free block */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));                                                    // Get the total size of the free block
    
    // CASE 1 : a lot of free space -> need to split the current space into one allocated space and the remaining free space
    if((csize - asize) >= 3*DSIZE){                                        
                                                           
        PUT(HDRP(bp), PACK(asize, 1));                                                    // Update header to not free
        PUT(FTRP(bp), PACK(asize, 1));                                                    // Update footer to not free
        remove_block(bp);                                                                 // Remove the allocated block from the free list 
        bp = NEXT_BLKP(bp);                                                                 
        PUT(HDRP(bp), PACK(csize - asize, 0));                                           // Put the header of the new block
        PUT(FTRP(bp), PACK(csize - asize, 0));                                           // Put the footer of the new block
        coalesce(bp);                                                                    // Coalesce the new free block with the adjacent free blocks
    }
   
    // CASE 2 : not enough space to have a remaining free space -> no split, only allocation
    else{                                                                                   
        PUT(HDRP(bp), PACK(csize, 1));                                                  // Update header to not free
        PUT(FTRP(bp), PACK(csize, 1));                                                  // Update footer to not free
        remove_block(bp);                                                               // Remove the allocated block from the free list 
    }
}

