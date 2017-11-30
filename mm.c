/*
* this solution implements the segregated memory


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


/*additional Macros defined*/
#define WSIZE     4                                                           // Size of a word
#define DSIZE     8                                                           // Size of a double word
#define CHUNKSIZE (1<<12)                                                     // Default size of extension for extend_heap
#define INIT (1<<6)                                                           // Default init size

#define LISTSIZE  15                                                          // Size of segregated list 

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

#define PACK(size, alloc) ((size) | (alloc))                                  //Put the size and allocated byte into one word

#define GET(p)            (*(unsigned int *)(p))                              // Read a word at address p 
#define PUT(p, val) (*(unsigned int *)(p) = (val))                            // Write a word at address p

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))          // Store predecessor or successor for free blocks 

#define GET_SIZE(p)  (GET(p) & ~0x7)                                          //Get the size from header/footer
#define GET_ALLOC(p) (GET(p) & 0x1)                                           //Get the allocated bit from header/footer

 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)                                     // Address of block's header
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)               // Address of block's footer


#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))      // Address of (physically) next and previous blocks 
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))


#define PREV_FREEP(ptr) ((char *)(ptr))                                       // Address of free block's predecessor and successor entries 
#define NEXT_FREEP(ptr) ((char *)(ptr) + WSIZE)

 
#define PRED(ptr) (*(char **)(ptr))                                           // Address of free block's predecessor and successor on the segregated list
#define SUCC(ptr) (*(char **)(NEXT_FREEP(ptr)))

/*global variable : segregated list*/

void *segregated_lists[LISTSIZE];


//Functions

static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void insert(void *bp, size_t size);
static void removen(void *bp);



/* Initializes the malloc, Return 0 if successful -1 if unsucessful */
int mm_init(void){
   
    char *heap_listp;
    int numlist;
   
// Check if there is enough space to create the heap
    
    if((heap_listp = mem_sbrk(4*WSIZE)) == NULL){                                
        return -1;
    }

// Initialize segregated lists
    
    for (numlist = 0; numlist < LISTSIZE; numlist++) {
        segregated_lists[numlist] = NULL;
   }
    
    PUT(heap_listp, 0);                                                          /* Alignment block */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));                               /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));                               /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));                                   /* Epilogue header */

//Extend the empty heap with a free block of CHUNKSIZE bytes,-1 if not possible 
    
    if(extend_heap(INIT) == NULL){                                           
         return -1;
    }

    return 0;
}

/* Allocates a block with at least the specified size of payload */

void *mm_malloc(size_t size)
{
    size_t asize;                                                                    // The size of the adjusted block
    size_t extendsize;                                                               // The amount by which heap is extended if no fit is found
    void *bp = NULL;                                                                           

    if(size == 0){                                                                         
        return NULL;
    }
    
    asize = ALIGN(size + DSIZE);
    
    if (asize <= 2*DSIZE){                                                            // Each created block has a minimum size of 2*DSIZE
       asize= 2*DSIZE;
    }
  
    int numlist = 0; 
    
    size_t ssize = asize;
   
    
    while (numlist < LISTSIZE) {                                                                          // Search for an adapted free block in segregated list
        if ((numlist == LISTSIZE - 1) || ((ssize <= 1) && (segregated_lists[numlist] != NULL))) {
            bp = segregated_lists[numlist];
            
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))                                                   // Don't take blocks that are too small
            {
                bp = PRED(bp);
            }
            if (bp != NULL)
                break;
        }
        
        ssize >>= 1;
        numlist++;
    }
    
    if (bp == NULL) {                                                                                           // if free block is not found, extend the heap
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
        
    bp = place(bp, asize);                                                                                   //Place the block
    
   return bp;
}

/* frees the block given in argument as a pointer */

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    insert(bp, size);
    coalesce(bp);
    
    return;
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
static void* extend_heap(size_t size){
   
    char *bp;
    size_t asize;
    asize = ALIGN(size);                                                                        // Allocate even number of  words to maintain alignment                               
                          
    if(((long)(bp = mem_sbrk(asize))) == -1){                                                 // if error in extending heap space return null
        return NULL;
    }
    
    
    PUT(HDRP(bp), PACK(asize, 0));                                                           // Free block header
    PUT(FTRP(bp), PACK(asize, 0));                                                           // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                                                   // New epilogue header
    insert(bp, asize);
                                                     
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
      return bp;
   }
   
   // CASE 2(book)
   else if(prev_alloc && !next_alloc){
      removen(bp);                                                                        // Because we inserted bp before calling coalesce function
      size+= GET_SIZE(HDRP(NEXT_BLKP(bp)));                                               // New size of the free block (current + next)
      removen(NEXT_BLKP(bp));                                                              // Remove the next block of the free list because now it is combined 
      PUT(HDRP(bp),PACK(size,0));                                                         // Free block header
      PUT(FTRP(bp),PACK(size,0));                                                         // Free block footer
   }
   
   // CASE 3(book)
   else if(!prev_alloc && next_alloc){
        removen(bp);                                                                         // Because we inserted bp before calling coalesce function
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                              // New size of the free block (current + previous)
        removen(PREV_BLKP(bp));                                                             // Remove the previous block                                                            
        PUT(FTRP(bp), PACK(size, 0));                                                       // Free new block header 
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));                                                       // Free new block footer 
        
   }
   
   // CASE 4(book)
   else{
        removen(bp);                                                                         // Because we inserted bp before calling coalesce function
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));              // New size of the free block (current + previous + next)
        removen(PREV_BLKP(bp));                                                        // Remove the previous block
        removen(NEXT_BLKP(bp));                                                        // Remove the next block 
        bp = PREV_BLKP(bp);                                                                 // Update the block pointer to the previous block
        PUT(HDRP(bp), PACK(size, 0));                                                       // Update the new block header
        PUT(FTRP(bp), PACK(size, 0));                                                       // Update the new block footer
}

   insert(bp, size);                                                                      // Insert the new block created
   return bp;
}


/* Inserts a block in segregated lists */
static void insert(void *bp, size_t size){
   
    int numlist = 0;                                                                         //numlist : the specific list where we are going to insert the node
    void *temp_bp = bp;
    void *insert_bp = NULL;
    
    // Select segregated list
     
    while ((numlist < LISTSIZE - 1) && (size > 1)) {                                       // Find the right list (adapted to block size) : corresponds to number of bits in the size of the block
        size >>= 1;
        numlist++;
    }
    
    temp_bp = segregated_lists[numlist];                                                  
    
    while (( temp_bp!= NULL) && (size > GET_SIZE(HDRP(temp_bp)))) {                          // Search in list numlist for the right free block(ascending order)
        insert_bp = temp_bp;
        temp_bp = PRED(temp_bp);
    }
    
                                                                                             // Set predecessor and successor : update pointers : different cases whether the insertion is at the beginning or the end of the list
    if (temp_bp != NULL) {
        if (insert_bp != NULL) {                                                             
            SET_PTR(PREV_FREEP(bp), temp_bp);
            SET_PTR(NEXT_FREEP(temp_bp), bp);
            SET_PTR(NEXT_FREEP(bp), insert_bp);
            SET_PTR(PREV_FREEP(insert_bp), bp);
        } else {
            SET_PTR(PREV_FREEP(bp), temp_bp);
            SET_PTR(NEXT_FREEP(temp_bp), bp);
            SET_PTR(NEXT_FREEP(bp), NULL);
            segregated_lists[numlist] = bp;
        }
    } else {
        if (insert_bp != NULL) {
            SET_PTR(PREV_FREEP(bp), NULL);
            SET_PTR(NEXT_FREEP(bp), insert_bp);
            SET_PTR(PREV_FREEP(insert_bp), bp);
        } else {
            SET_PTR(PREV_FREEP(bp), NULL);
            SET_PTR(NEXT_FREEP(bp), NULL);
            segregated_lists[numlist] = bp;
        }
    }
    
    return;
}


/* Removes a block from the free list */

static void removen(void *bp){
    
    int numlist = 0;
    size_t size = GET_SIZE(HDRP(bp));
    
 
    while ((numlist < LISTSIZE - 1) && (size > 1)) {                   // Select segregated list number where we are going to remove the block 
        size >>= 1;
        numlist++;
    }
    
    if (PRED(bp) != NULL) {                                        // Different cases wether the block has a preceeding block and a successor in the segregated list chosen
        if (SUCC(bp) != NULL) {
            SET_PTR(NEXT_FREEP(PRED(bp)), SUCC(bp));               // next of prev(bp) becomes next(bp) ... Update pointers
            SET_PTR(PREV_FREEP(SUCC(bp)), PRED(bp));
        } else {
            SET_PTR(NEXT_FREEP(PRED(bp)), NULL);
            segregated_lists[numlist] = PRED(bp);
        }
    } else {
        if (SUCC(bp) != NULL) {
            SET_PTR(PREV_FREEP(SUCC(bp)), NULL);
        } else {
            segregated_lists[numlist] = NULL;
        }
    }
    
    return;
}


/* Places a block of specified size to start of free block */


static void *place(void *bp, size_t asize){
   
    size_t csize = GET_SIZE(HDRP(bp));                                               // Get the total size of the free block                                                  
    removen(bp);                                                                       // Remove former free block that we are going to fill
    
/* CASE 1 : not enough space to have a remaining free space -> no split, only allocation. CASE  2: a lot of free space -> need to split the current space into one allocated space and the remaining free space */

    
// CASE 1 : no split 
    
    if((csize - asize) <= 3*DSIZE){                                                                                                                        
        PUT(HDRP(bp), PACK(csize, 1));                                                  // Update header to not free
        PUT(FTRP(bp), PACK(csize, 1));                                                  // Update footer to not free
    }
    
//CASE 2 : need to split 
    
    // subcase : to avoid segmentation fault 
    
    else if (asize >= 90) {

        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize- asize, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        insert(bp,csize- asize);
        return NEXT_BLKP(bp);
        
    }
    
   else {                                                       
        PUT(HDRP(bp), PACK(asize, 1));                                                    // Update header to not free
        PUT(FTRP(bp), PACK(asize, 1));                                                    // Update footer to not free                                                               
        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));                                 // Put the header of the new block
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));                                 // Put the footer of the new block
        insert(NEXT_BLKP(bp), csize- asize);                                              // Insert remaining free block
      }
   
    

    return (bp);
}



