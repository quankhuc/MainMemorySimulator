/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    union{
        struct{
            struct block* previous;
            struct block* next;
        };
    
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start;
static block_t *list_start; // pointer to list of free blocks
//static block_t *list_end;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* My function prototypes */
static void remove_block(block_t *block);
static void insert_at_front(block_t *block);
static void checkblock(block_t *block);
static int alignment(block_t *block);
//static int in_heap(block_t *block);


/*
 * <what does mm_init do?>
 * this function initializes the memory. How big is the heap? The fuction uses mem_sbrk() function to allocate
 * a 16 bytes - data segment.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    /*
     * This condition checks if the pointer of the prologue is the same as it of the epilogue 
     */
    
   
    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    // list_start points to NULL because there is nothing in the doubly linked list
    list_start = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 * 
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * <what does free do?>
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);

}

/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * <what does coalesce do?>
 * To coalesce newly freed block with neighbours, there are 4 cases
 *   [PREVIOUS -- CURRENT -- NEXT]
 *1: [ALLOC    -- FREE    -- ALLOC] : APPEND THE NEW BLOCK TO THE FRONT OF THE LIST
 *2: [ALLOC    -- FREE    -- FREE]  : APPEND NEW BLOCK (CURRENT + NEXT)
 *3: [FREE     -- FREE    -- ALLOC] : APPEND NEW BLOCK (PREVIOUS + CURRENT)
 *4: [FREE     -- FREE    -- FREE]  : APPEND NEW BLOCK (PREVIOUS + CURRENT + NEXT)
 */
static block_t *coalesce(block_t * block) 
{
    // fill me in
    size_t previous_allocation = get_alloc(find_prev(block)); //store whether the previous block is allocated or not.
    size_t next_allocation = get_alloc(find_next(block)); //store whether the next block is allocated or not.
    size_t size = get_size(block); //store the size of a block
    block_t *block_next;
    block_t *block_previous;

    //Case 1: The block is next to the current block is free
    if(previous_allocation && !next_allocation){
        block_next = find_next(block); //find the next block
        size += get_size(block_next); // update the size to be the size of the current block + the size of the next block
        remove_block(block_next); // remove the next block because it is now one block contained next + current
        write_header(block,size,false); // update header of the new block
        write_footer(block,size,false); // update footer of the new block
        // no need to update the block pointer because it still needs to pointer to the start of the (current + next) block
    }
    //Case 2: The block is previous to the current block is free
    else if(!previous_allocation && next_allocation && find_prev(block) != block){
        block_previous = find_prev(block); //find the block pointer
        size += get_size(block_previous); // update the size to be the sum of the current block and the previous block
        remove_block(block_previous); // remove the previous block because it is now one block contained previous + current
        write_header(block_previous,size,false); // update the header of the previous block and set it to be the header
        write_footer(block_previous,size,false); //update the footer of the current block because the footer location does not change
        block = block_previous; //update the pointer of the block to the previous block as the previous block merged into the current block as one block
    }
    //Case 3: Both previous and next blocks are free
    else if(!previous_allocation && !next_allocation && find_prev(block) != block){
        block_previous = find_prev(block); //find the previous block
        block_next = find_next(block); //find the next block
        size += get_size(block_previous) + get_size(block_next); //update the size to be the sum of previous + current + next
        remove_block(block_next); // remove the next block because it is now one block contained previous + current + next
        remove_block(block_previous); // remove the previous block because it is now one block contained previous + current + next
        write_header(block_previous,size,false); //update the the header of the previous block and set it to be the header of the new block
        write_footer(block_previous,size,false); //update the footer of the next block and set it to be the footer of the new block
        block = block_previous; //update the pointer of the block to the previous block as previous block and next block merged into the current block
    }
    //Case 4: Neither of the previous block and the next block are free
    insert_at_front(block); // just add the block the beginning of the list

    return block;
}

// helper function to remove block pointers when coalescing
static void remove_block(block_t *block){
    if(block -> previous != NULL && block -> next != NULL){
        // how can I get the next pointer of the previous block? Then set it to the next block
        block -> previous -> next = block -> next;
        block -> next -> previous = block -> previous;
    }
    // Case 2: the block is at the tail of the list. There is no block after that to link to
    else if(block -> previous != NULL && block -> next == NULL)   
    {
        block -> previous -> next = NULL;
        // no block -> next
    }
    // Case 3: The block is at the beginning of the list
    else if (block -> previous == NULL && block -> next != NULL){
        block -> next -> previous = NULL;
        // update the list_start to point at the next block
        list_start = block -> next;
    }
    // Case 4: The block is the only thing in the list
    else if (block -> previous == NULL && block -> next == NULL){
        list_start = NULL;
    }

}

// helper function to insert a block at the front of the doubly linked list
static void insert_at_front(block_t *block){
    /* If the free list has nothing, set it the first one*/
    if(list_start == NULL){
        block -> next = NULL;
        block -> previous = NULL;
        list_start = block;
        return;
    }
    block -> next = list_start; //set the next pointer to point to list_start so that the block can be the head of the list
    list_start -> previous = block; //set the previous pointer of the list_start to block to properly linked
    block -> previous = NULL; //set the previous pointer of block to NULL
    list_start = block; //set the block to be the start of the list
}

/*
 * <what does place do?>
 *
 * Place block of asize bytes at the start of the free block pointer
 * Remove free block
 * 
 *
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size) // This is checking if the size of a block is very big so that we can split it and don't have to use the entire block to store data
    {
        block_t *block_next;
        remove_block(block); //remove this block from the free list because it is now is occupied
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        insert_at_front(block_next); // coalesce the block_next which is spliced from the original big block
    }
    // if the block just fits the requested block's size
    else
    { 
        remove_block(block); //removing this block from the free list
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}

/*
 * <what does find_fit do?>
 * 
 * Modified findfit function to iterate through the doubly linked list and find the a fit for the block
 * of a given size.
 */

static block_t *find_fit(size_t asize){
    // In order to traverse from the beginning of the list, block is at the beginning of the list
    block_t * block = list_start;
    // traverse the entire free list
    while(block != NULL){
        if((asize <= get_size(block)) && (!(get_alloc(block)))){    //if the free block's size fits the requested block's size
            return block;
        }
        else{
        block = block -> next; //traverse through the doubly linked list
        }
        
    }
    return NULL;                        //if no fit then return NULL
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 * First, I need to check the heap: Prologue block -> iterate through the heap and check each block
 * -> Probably I need to create a helper function for this check -> Epilogue block
 * Then, I need to check for the validation of the free list by checking their previous/next pointers
 */
bool mm_checkheap(int line)  
{ 
   // (void)line; // delete this line; it's a placeholder so that the compiler
                // will not warn you about an unused variable.
 //   printf("Going to the check_heap");
    block_t *block;
    block = heap_start;
    // Check prologue by checking the size of the header and the allocation bit
    // pointer already points to the header and I can find the next header by find_next()
    if((get_size(block) != 0) || (get_alloc(block) != 1))
    {
        printf("Address: %p -- Prologue Error -- \n" , block);
        assert(0);
    }

    // moving to the next block
  //  block = find_next(block);

    // iterate through each block of a heap
    while(get_size(block) != 0)
    {
        // using helper function here
        checkblock(block);
        block = find_next(block);
    }
  //  while(block != NULL){
  //      printf("Block: %p \n", block);
  //      block = block -> next;
  //  } 

    return true;
}

/*
 * checkblock - check block header and footer
 * In particular: check if the block is at least min size
 *                check for out of bounds
 *                check for address alignment
 *                check if the header and the footer match
 */
// I will need to fix checkblock function later

static void checkblock(block_t *block)
{
    //check each block's address alignment (multiple of n)
    //NEED TO FIX THE EACH CHECK BECAUSE BLOCK IS AN OBJECT
    if(!alignment(block)){
       printf("Address: %p -- Block Alignment Error -- \n", block);
       assert(0);
    }
    //check whether each block is out of bounds
  //  if(!in_heap(block)){
  //      printf("Address: %p -- Access Memory Out of Heap -- \n", block);
  //      assert(0);
  //  }
    //check the min size
    if(get_alloc(block)){
        if(get_size(block) < (2*dsize)){
            printf("Address: %p -- The block size is not valid (smaller than Minimum size) -- \n", block);
            assert(0);
        } 
    }
    //check header/footer alignment
    if(get_size(block) % wsize){
        printf("Address: %p -- Header is not 8 bytes -- \n", block);
        assert(0);
    }
    //check if header matches footer
    //WILL WRITE IT LATER

}

// helper function to return whether the pointer is aligned
static int alignment(block_t* block)
{
    const void *pointer = header_to_payload(block);
    return (long)pointer % 16 == 0;
}

// helper function to return either the pointer is in the heap or not
//static int in_heap(block_t* block)
//{
//    return (void)block <= mem_heap_hi() && (void)block >= mem_heap_lo();
//}


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
