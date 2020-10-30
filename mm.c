/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            struct block *prev;
            struct block *next;
        };
        char payload[0];
    };
} block_t;
/* Global variables */
static block_t *root; // root of the explicit list
/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
static size_t listCount;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    // printf("---------write block---------\n");
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */

void print_heap() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        printf("new block: ");
        printf("size: %zu   ", get_size(block));
        if (get_alloc(block)) {
            printf("true");
            printf("\n");
        }
        if (!get_alloc(block)) {
            printf("false");
            printf("\n");
        }
    }
    return;
}

void print_list() {
    block_t *block;
    printf("printing the list: \n");
    for (block = root; block != NULL; block = block->next) {
        printf("new free in list: ");
        printf("size: %zu   ", get_size(block));
        if (get_alloc(block)) {
            printf("true");
            printf("\n");
        }
        if (!get_alloc(block)) {
            printf("false");
            printf("\n");
        }
    }
    return;
}

void remove_from_list(block_t *block) {
    dbg_requires(mm_checkheap(__LINE__));
    dbg_assert(get_alloc(block) == true);
    // a block has to be allocated to be removed from the free list
    dbg_assert(root != NULL);
    dbg_assert(block != root);
    if (block == NULL) {
        return;
    }
    block_t *prevBlock = block->prev;
    block_t *nextBlock = block->next;
    // note that prevBlock could be the root, block itself could not be root
    if (block->next == NULL) {
        prevBlock->next = NULL;
        return;
    }
    dbg_requires(mm_checkheap(__LINE__));
    dbg_assert(((size_t)nextBlock->payload) % 16 == 0);
    nextBlock->prev = prevBlock; // the normal case
    prevBlock->next = nextBlock;
    dbg_ensures(mm_checkheap(__LINE__));
    return;
}

void add_to_list(block_t *block) {
    dbg_requires(mm_checkheap(__LINE__));
    dbg_assert(get_alloc(block) == false);
    listCount += 1;
    // printf("blocks in list: %zu \n", listCount);
    dbg_assert(root != NULL);
    // printf("add to list -->\n");
    // printf("block size: %zu \n", get_size(block));
    if (root->next == NULL) {
        // printf("adding first block");
        root->next = block;
        block->prev = root;
        block->next = NULL;
        return;
    }
    block_t *firstBlock = root->next;
    root->next = block;
    block->prev = root;
    block->next = firstBlock;
    firstBlock->prev = block;
    return;
}

static void split_block(block_t *block, size_t asize) {
    dbg_requires(asize >= 2 * dsize);

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);
        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        add_to_list(block_next);
    }
    dbg_ensures(get_alloc(block));
}

static block_t *coalesce_block(block_t *block) {
    dbg_requires(mm_checkheap(__LINE__));
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    block_t *prevBlock;
    block_t *nextBlock;
    bool prev_alloc;
    bool next_alloc;
    size_t current_size;
    size_t next_size;
    size_t prev_size;
    current_size = get_size(block);
    prevBlock = find_prev(block);
    nextBlock = find_next(block);
    prev_alloc = get_alloc(prevBlock);
    if (prevBlock == block) {
        // this happens when block happens to be the first block on the heap
        //("first block on the heap\n");
        prev_alloc = true;
    }
    next_alloc = get_alloc(nextBlock);
    if (nextBlock == NULL) {
        next_alloc = true;
    }
    if (prev_alloc && next_alloc) {
        // printf("neither is free\n");
        // neither the prev not the next is free
        add_to_list(block);
        return block;
    } else if (prev_alloc && !next_alloc) {
        // next block is free, write to the current block
        // printf("next is free\n");
        next_size = get_size(nextBlock);
        remove_from_list(nextBlock);
        write_block(block, current_size + next_size, false);
        add_to_list(block);
        return block;
    } else if (!prev_alloc && next_alloc) {
        // prev block is free, write to the previous block
        // printf("prev is free\n");
        prev_size = get_size(prevBlock);
        if (prevBlock != root) {
            remove_from_list(prevBlock);
            write_block(prevBlock, current_size + prev_size, false);
            add_to_list(prevBlock);
            return prevBlock;
        }
        add_to_list(block);
        return block;
    } else {
        // printf("both are free\n");
        dbg_assert((prevBlock != NULL) && (nextBlock != NULL));
        if (prevBlock == root) {
            next_size = get_size(nextBlock);
            remove_from_list(nextBlock);
            write_block(block, current_size + next_size, false);
            add_to_list(block);
            return block;
        }
        prev_size = get_size(prevBlock);
        next_size = get_size(nextBlock);
        remove_from_list(prevBlock);
        remove_from_list(nextBlock);
        write_block(prevBlock, current_size + prev_size + next_size, false);
        add_to_list(prevBlock);
        return prevBlock;
    }
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);
    if (root == NULL) {
        // the root points is the first small block splitted from the new block
        // printf("new root\n");
        // split_block(block, 2 * dsize);
        // //split block writes the block to be splitted to allocated, but it
        // shall
        // //be free here. We use split just to get the "dummy header" for the
        // list write_block(block, 2 * dsize, false);
        root = block;
        root->prev = NULL;
        root->next = NULL;
        listCount = 1;
        block_t *block_next = find_next(block);
        write_epilogue(block_next);
        // assert(((void*)block_next) >= mem_heap_lo()+8);
        // assert(((void*)block_next) <= mem_heap_hi()-7);
        // the root would not be used to allocate
        // print_list();
        return block;
    }
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);
    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    if (root == NULL) {
        return NULL;
    }
    size_t count = 0;          // count how many blocks are searched
    size_t minSize = 0;        // the minimum-sized block that fits
    block_t *bestBlock = NULL; // the best block found so far
    for (block = root; block != NULL; block = block->next) {
        count += 1;
        if (count > 10) {
            if (bestBlock != NULL) {
                return bestBlock;
            } else {
                assert(bestBlock == NULL);
                if ((asize <= get_size(block)) && (block != root)) {
                    dbg_assert(!get_alloc(block));
                    return block;
                }
            }
        }
        if ((asize <= get_size(block)) && (block != root)) {
            assert(count <= 10);
            if (minSize == 0) {
                minSize = get_size(block);
                bestBlock = block;
            }
            if (get_size(block) < minSize) {
                minSize = get_size(block);
                bestBlock = block;
            }
        }
    }
    return bestBlock; // no fit found
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    block_t *block; // current block
    block_t *nextBlock;
    block_t *prevBlock;
    size_t listCount = 0; // count # of free blocks by traversing the list
    size_t allCount = 0;  // count # of free blocks by going over all blocks
    // check that each block's header and footer matches
    // check that each block is bigger than the minimum size
    // check that there are no consecutive free blocks
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        size_t blockSize = get_size(block);
        dbg_assert(blockSize >= 2 * dsize);
        // 2*dsize is the minimum size of a block
        word_t blockHeader = block->header;
        word_t blockFooter = *(header_to_footer(block));
        dbg_assert(((char *)block) > (char *)(mem_heap_lo()));
        // lie within boundary
        dbg_assert(((char *)blockFooter) < (char *)(mem_heap_hi() - 7));
        dbg_assert(((size_t)(block->payload)) % 16 == 0);
        dbg_assert(extract_size(blockHeader) == extract_size(blockFooter));
        dbg_assert(extract_alloc(blockHeader) == extract_alloc(blockFooter));
        nextBlock = find_next(block); // no contiguous block has the same alloc
        assert(get_alloc(nextBlock) != get_alloc(block));
        if (!get_alloc(block)) {
            allCount += 1;
        }
    }
    if (root != NULL) {
        for (block = root; block->next != NULL; block = block->next) {
            listCount += 1;
            dbg_assert(!get_alloc(block));
            prevBlock = block->prev;
            if (prevBlock == NULL) {
                dbg_assert(prevBlock == root);
                break;
            }
            dbg_assert(prevBlock->next == block);
            dbg_assert(block->prev == prevBlock);
        }
    }
    //("listCount: %zu\n", listCount);
    // printf("allCount: %zu\n", allCount);
    dbg_assert(listCount == allCount);
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    // printf("-------init-------\n");
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    root = NULL; // the free list is empty at first, root is just NULL
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        // printf("need to extend\n");
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);
    remove_from_list(block);
    // Try to split the block if too large
    split_block(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    write_block(block, size, false);
    block = coalesce_block(block);
    dbg_ensures(!get_alloc(block));
    dbg_ensures((get_size(block) % 16) == 0);
    dbg_ensures(mm_checkheap(__LINE__));
    return;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 71 6d 41 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 30 84 19 45 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 45 27 40 64 81 1e 4d 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
