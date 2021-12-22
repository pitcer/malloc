/*
 * Piotr Dobiech 316625
 *
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
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define debug_msg(...) printf(__VA_ARGS__)
#define debug_assert(expression) assert(expression)
#else
#define debug(fmt, ...)
#define debug_msg(...)
#define debug_assert(expression)
#endif

#define __Unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

// Annotations for developer

/*
 * Indicates that variable, function parameter or function result may be equal
 * to NULL.
 **/
#define __Nullable

/*
 * Indicates that variable, function parameter or function result is not equal
 * to NULL.
 **/
#define __NotNull

#define MINIMUM_BLOCK_SIZE ALIGNMENT

typedef void Payload;
typedef uint32_t Word;
typedef Word BoundaryTag;
typedef BoundaryTag Header;
typedef BoundaryTag Footer;
typedef Word UnalignedPayloadSize;
typedef Word PayloadSize;
typedef Word BlockSize;
typedef Word UnalignedBlockSize;

#define HEADER_SIZE sizeof(Header)
#define FOOTER_SIZE sizeof(Footer)

typedef struct {
  Header header;
  /*
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   **/
  uint8_t payload[];
  // As we don't know payload size here, we need to manually get the footer.
  // Footer footer;
} Block;

/*
 * Block without its structure.
 **/
typedef Block UninitBlock;

typedef enum {
  FREE = 0x0,
  ALLOCATED = 0x1,
  FREE_AND_PREVIOUS_FREE = 0x2,
  ALLOCATED_AND_PREVIOUS_FREE = 0x3,
} BlockState;

static Block *first_block;
static Block *last_block;
static Word blocks_size;

#define is_block_state(maybe_state) (maybe_state) >= 0 && (maybe_state) <= 2

#define is_aligned(word) ((word) & ~(-ALIGNMENT)) == 0

inline static bool is_uninit_block(__Nullable UninitBlock *block) {
  return block != NULL && is_aligned((size_t)block + HEADER_SIZE);
}

inline static bool is_block(__Nullable Block *block) {
  return is_uninit_block(block);
}

#define is_block_size(maybe_size) is_aligned((maybe_size))

#define is_payload_size(maybe_size)                                            \
  is_aligned((maybe_size) & ~0x8) && (~(maybe_size)&0x8) == 0

static inline const Word round_to_alignment(const Word size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

#define shift_right(pointer, offset) (void *)(pointer) + (offset)

#define shift_left(pointer, offset) (void *)(pointer) - (offset)

static inline bool compare_payloads(__NotNull const Payload *first,
                                    __NotNull const Payload *second,
                                    const PayloadSize size) {
  debug_assert(first != NULL);
  debug_assert(second != NULL);

  for (size_t index = 0; index < size; index++) {
    if (shift_right(first, index) != shift_right(second, index)) {
      return false;
    }
  }

  return true;
}

static inline const UnalignedBlockSize
unaligned_payload_to_block_size(const UnalignedPayloadSize size) {
  return HEADER_SIZE + size + FOOTER_SIZE;
}

static inline const BlockSize
payload_to_block_size(const PayloadSize payload_size) {
  debug_assert(is_payload_size(payload_size));

  const BlockSize block_size = unaligned_payload_to_block_size(payload_size);

  debug_assert(is_block_size(block_size));
  return block_size;
}

static inline const PayloadSize
block_to_payload_size(const BlockSize block_size) {
  debug_assert(is_block_size(block_size));

  const PayloadSize payload_size = block_size - HEADER_SIZE - FOOTER_SIZE;

  debug_assert(is_payload_size(payload_size));
  return payload_size;
}

static inline __NotNull Payload *get_payload(__NotNull Block *block) {
  debug_assert(block != NULL);

  void *payload = block->payload;

  debug_assert(payload != NULL);
  debug_assert(shift_right(block, HEADER_SIZE) == payload);
  return payload;
}

#define PAYLOAD_SIZE_MASK (-ALIGNMENT | 0x8)

static inline const PayloadSize extract_payload_size(const BoundaryTag tag) {
  return tag & PAYLOAD_SIZE_MASK;
}

static inline const PayloadSize get_payload_size(__NotNull Block *block) {
  debug_assert(block != NULL);

  const BoundaryTag header = block->header;
  // debug("%x", header);
  const PayloadSize payload_size = extract_payload_size(header);

  // debug("%u", payload_size);
  debug_assert(is_payload_size(payload_size));
  return payload_size;
}

static inline __NotNull Footer *
get_footer_from_payload_size(__NotNull Block *block,
                             const PayloadSize payload_size) {
  debug_assert(is_block(block));
  debug_assert(is_payload_size(payload_size));

  Footer *footer = shift_right(block, HEADER_SIZE + payload_size);

  debug_assert(footer != NULL);
  return footer;
}

static inline __NotNull BoundaryTag *get_footer(__NotNull Block *block) {
  debug_assert(is_block(block));

  const PayloadSize payload_size = get_payload_size(block);
  return get_footer_from_payload_size(block, payload_size);
}

static inline const BlockState extract_header_state(const Header header) {
  return header & ~PAYLOAD_SIZE_MASK;
}

static inline const BlockState get_state(__NotNull Block *block) {
  debug_assert(block != NULL);

  const BoundaryTag header = block->header;
  const BlockState state = header & ~PAYLOAD_SIZE_MASK;

  debug_assert(is_block_state(state));
  return state;
}

#ifdef DEBUG
#define GET_BLOCK_SNAPSHOT(name, block)                                        \
  __Unused const PayloadSize name##_payload_size =                             \
    extract_payload_size(block->header);                                       \
  __Unused const BlockState name##_block_state =                               \
    extract_header_state(block->header);                                       \
  __Unused const Payload *name##_payload = get_payload(block);
#else
#define GET_BLOCK_SNAPSHOT(name, block)
#endif

static inline const BoundaryTag with_payload_size(const BoundaryTag tag,
                                                  const PayloadSize size) {
  debug_assert(is_payload_size(size));

  return (tag & ~PAYLOAD_SIZE_MASK) | size;
}

static inline void set_header_payload_size(__NotNull Block *block,
                                           const PayloadSize payload_size) {
  debug_assert(block != NULL);
  debug_assert(is_payload_size(payload_size));

  GET_BLOCK_SNAPSHOT(old, block);

  BoundaryTag *header = &block->header;
  *header = with_payload_size(*header, payload_size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_payload_size == payload_size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(compare_payloads(old_payload, new_payload, old_payload_size));
}

static inline void set_payload_size(__NotNull Block *block,
                                    const PayloadSize payload_size) {
  debug_assert(block != NULL);
  debug_assert(is_payload_size(payload_size));

  GET_BLOCK_SNAPSHOT(old, block);

  set_header_payload_size(block, payload_size);
  Footer *footer = get_footer_from_payload_size(block, payload_size);
  *footer = with_payload_size(*footer, payload_size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_payload_size == payload_size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(compare_payloads(old_payload, new_payload, old_payload_size));
}

static inline const BoundaryTag with_block_state(const Header header,
                                                 const BlockState state) {
  debug_assert(is_block_state(state));

  return (header & PAYLOAD_SIZE_MASK) | state;
}

static inline void set_state(__NotNull Block *block, const BlockState state) {
  debug_assert(is_block(block));
  debug_assert(is_block_state(state));

  GET_BLOCK_SNAPSHOT(old, block);

  Header *header = &block->header;
  *header = with_block_state(*header, state);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_block_state == state);
  debug_assert(old_payload_size == new_payload_size);
  debug_assert(compare_payloads(old_payload, new_payload, old_payload_size));
}

static inline bool is_free(__NotNull Block *block) {
  debug_assert(is_block(block));

  return get_state(block) == FREE;
}

static inline bool is_allocated(__NotNull Block *block) {
  debug_assert(is_block(block));

  return get_state(block) == ALLOCATED;
}

static inline void set_free(__NotNull Block *block) {
  debug_assert(is_block(block));

  set_state(block, FREE);

  debug_assert(get_state(block) == FREE);
}

static inline void set_allocated(__NotNull Block *block) {
  debug_assert(is_block(block));

  set_state(block, ALLOCATED);

  debug_assert(get_state(block) == ALLOCATED);
}

static inline const BlockSize get_block_size(__NotNull Block *block) {
  debug_assert(is_block(block));

  const PayloadSize payload_size = get_payload_size(block);
  const BlockSize block_size = payload_to_block_size(payload_size);

  debug_assert(is_block_size(block_size));
  return block_size;
}

static inline __NotNull Block *
get_block_from_payload(__NotNull Payload *payload) {
  debug_assert(payload != NULL);

  Block *block = payload - HEADER_SIZE;

  debug_assert(is_block(block));
  return block;
}

/**
 * Returns next block. Given block must not be the last one.
 */
static inline Block *get_next_block(__NotNull Block *block) {
  debug_assert(is_block(block));
  debug_assert(block != last_block);
  debug_assert(blocks_size > 0);

  const BlockSize block_size = get_block_size(block);
  Block *next_block = shift_right(block, block_size);

  debug_assert(is_block(next_block));
  return next_block;
}

/**
 * Returns next block or NULL if the given block was the last one.
 */
static inline __Nullable Block *maybe_get_next_block(__NotNull Block *block) {
  debug_assert(is_block(block));

  if (block >= last_block) {
    debug_assert(block == last_block);
    return NULL;
  }

  return get_next_block(block);
}

#define iterate_blocks(block, handler)                                         \
  {                                                                            \
    Block *block = first_block;                                                \
    for (; block < last_block; block = get_next_block(block)) {                \
      handler;                                                                 \
    }                                                                          \
    debug_assert(block == last_block);                                         \
    handler;                                                                   \
  }

typedef void *SbrkResult;

static inline bool is_sbrk_failed(SbrkResult result) {
  return result < 0;
}

static inline __Nullable SbrkResult allocate_heap_space(const BlockSize size) {
  debug_assert(is_block_size(size));

  const SbrkResult result = mem_sbrk(size);
  if (is_sbrk_failed(result)) {
    return NULL;
  }

  blocks_size += size;

  return result;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  const SbrkResult allocate_alignment_result =
    mem_sbrk(ALIGNMENT - HEADER_SIZE);
  if (is_sbrk_failed(allocate_alignment_result)) {
    return -1;
  }

  first_block = mem_sbrk(0);
  last_block = first_block;
  blocks_size = 0;

  debug_assert(is_uninit_block(first_block));

  return 0;
}

static inline bool heap_has_no_allocated_blocks() {
  return blocks_size == 0;
}

/*
 * Find first free and sufficient block or return NULL.
 */
static inline __Nullable Block *
find_first_free_block(const PayloadSize payload_size) {
  debug_assert(is_payload_size(payload_size));
  debug_assert(is_block(first_block));
  debug_assert(is_block(last_block));
  debug_assert(blocks_size > 0);

  iterate_blocks(
    block, debug_assert(is_block(block));
    const PayloadSize block_payload_size = get_payload_size(block);
    if (is_free(block) && block_payload_size >= payload_size) {
      return block;
    });

  return NULL;
}

#undef handle_block

static inline __Nullable Payload *
allocate_new_block(const BlockSize block_size, const PayloadSize payload_size) {
  debug_assert(is_block_size(block_size));
  debug_assert(is_payload_size(payload_size));

  __Nullable SbrkResult allocated_space = allocate_heap_space(block_size);
  if (allocated_space == NULL) {
    return NULL;
  }

  UninitBlock *uninit_block = (UninitBlock *)allocated_space;
  debug_assert(is_uninit_block(uninit_block));

  set_header_payload_size(uninit_block, payload_size);
  set_allocated(uninit_block);

  Block *block = uninit_block;
  debug_assert(is_block(block));

  last_block = block;

  return get_payload(block);
}

/**
 * Returns true if block extension was successful or false if not (sbrk failed).
 */
static inline bool extend_last_block(__NotNull Block *block,
                                     const PayloadSize required_payload_size) {
  debug_assert(is_block(block));
  debug_assert(block == last_block);
  debug_assert(shift_right(block, get_block_size(block) - 1) == mem_heap_hi());
  debug_assert(is_payload_size(required_payload_size));

  const PayloadSize old_payload_size = get_payload_size(block);
  const BlockSize additional_space = required_payload_size - old_payload_size;

  const SbrkResult result = allocate_heap_space(additional_space);
  if (result == NULL) {
    return false;
  }

  set_payload_size(block, required_payload_size);

  return true;
}

static inline void split_block(__NotNull Block *block,
                               const BlockSize block_size,
                               const PayloadSize payload_size) {
  debug_assert(is_block(block));
  debug_assert(is_block_size(block_size));
  debug_assert(is_payload_size(payload_size));

  __Unused const BlockSize old_block_size = get_block_size(block);
  const PayloadSize old_payload_size = get_payload_size(block);
  const BlockSize empty_block_size = old_payload_size - payload_size;
  debug_assert(is_block_size(empty_block_size));

  // Block is too small to split.
  if (empty_block_size < MINIMUM_BLOCK_SIZE) {
    return;
  }

  set_payload_size(block, payload_size);

  UninitBlock *empty_uninit_block = shift_right(block, block_size);
  debug_assert(is_uninit_block(empty_uninit_block));

  const PayloadSize empty_block_payload_size =
    block_to_payload_size(empty_block_size);
  debug_assert(HEADER_SIZE + payload_size + FOOTER_SIZE + HEADER_SIZE +
                 empty_block_payload_size + FOOTER_SIZE ==
               old_block_size);

  set_payload_size(empty_uninit_block, empty_block_payload_size);
  set_free(empty_uninit_block);

  Block *empty_block = empty_uninit_block;
  debug_assert(is_block(empty_block));

  if (block == last_block) {
    last_block = empty_block;
  }
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t unaligned_payload_size) {
  debug_assert(unaligned_payload_size < MAX_HEAP);

  const UnalignedBlockSize unaligned_block_size =
    unaligned_payload_to_block_size(unaligned_payload_size);
  const BlockSize block_size = round_to_alignment(unaligned_block_size);
  const PayloadSize payload_size = block_to_payload_size(block_size);

  // This is the first allocation.
  if (heap_has_no_allocated_blocks()) {
    // debug_msg("Allocating the first block...\n");
    return allocate_new_block(block_size, payload_size);
  }

  __Nullable Block *block = find_first_free_block(payload_size);

  // Found empty block with sufficient space.
  if (block != NULL) {
    split_block(block, block_size, payload_size);
    set_allocated(block);
    return get_payload(block);
  }

  // Last block is free, but too small.
  if (is_free(last_block)) {
    const bool result = extend_last_block(last_block, payload_size);
    if (!result) {
      return NULL;
    }
    debug_assert(get_payload_size(last_block) >= payload_size);

    set_allocated(last_block);
    return get_payload(last_block);
  }

  // Last block was allocated, so we need to allocate a new one.
  return allocate_new_block(block_size, payload_size);
}

static inline __NotNull BoundaryTag *
get_previous_footer(__NotNull Block *block) {
  debug_assert(is_block(block));
  debug_assert(block != first_block);
  debug_assert(blocks_size > 0);

  BoundaryTag *previous_footer = shift_left(block, FOOTER_SIZE);

  __Unused Block *previous_block = shift_left(
    previous_footer, extract_payload_size(*previous_footer) + HEADER_SIZE);
  debug_assert(extract_payload_size(*previous_footer) ==
               get_payload_size(previous_block));
  debug_assert(extract_block_state(*previous_footer) ==
               get_state(previous_block));

  return previous_footer;
}

/**
 * Returns previous block. Given block must not be the first one.
 */
static inline __NotNull Block *get_previous_block(__NotNull Block *block) {
  debug_assert(is_block(block));
  debug_assert(block != first_block);
  debug_assert(blocks_size > 0);

  BoundaryTag *previous_footer = get_previous_footer(block);
  const PayloadSize previous_payload_size =
    extract_payload_size(*previous_footer);
  debug_assert(is_payload_size(previous_payload_size));

  const BlockSize previous_block_size =
    payload_to_block_size(previous_payload_size);
  Block *previous_block = shift_left(block, previous_block_size);

  debug_assert(is_block(previous_block));
  return previous_block;
}

/**
 * Returns previous block or NULL if the given block was the first one.
 */
static inline __Nullable Block *
maybe_get_previous_block(__NotNull Block *block) {
  debug_assert(is_block(block));

  if (block <= first_block) {
    debug_assert(block == first_block);
    return NULL;
  }

  return get_previous_block(block);
}

/**
 * Free
 */
void free(Payload *payload) {
  if (payload == NULL) {
    return;
  }

  Block *block = get_block_from_payload(payload);

  BlockSize block_size = get_block_size(block);

  __Nullable Block *next_block = maybe_get_next_block(block);
  if (next_block != NULL && is_free(next_block)) {
    block_size += get_block_size(next_block);

    if (next_block == last_block) {
      last_block = block;
    }
  }

  __Nullable Block *previous_block = maybe_get_previous_block(block);
  if (previous_block != NULL && is_free(previous_block)) {
    block_size += get_block_size(previous_block);

    if (block == last_block) {
      last_block = previous_block;
    }
    block = previous_block;
  }

  const PayloadSize payload_size = block_to_payload_size(block_size);
  set_payload_size(block, payload_size);
  set_free(block);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (old_ptr == NULL) {
    return malloc(size);
  }

  // jeśli «ptr» nie jest równy «NULL», to musiał zostać zwrócony przez
  // procedurę «mm_malloc» lub
  // «mm_realloc», i należy zmienić rozmiar przydzielonego bloku. Dopuszcza się
  // przeniesienie bloku pod nowy adres różny od «ptr». Jeśli użytkownik
  // zwiększa rozmiar bloku, to dodatkowa pamięć w bloku musi pozostać
  // niezainicjowana.

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (new_ptr == NULL) {
    return NULL;
  }

  /* Copy the old data. */
  Block *block = old_ptr - offsetof(Block, payload);
  size_t old_size = get_payload_size(block);
  if (size < old_size) {
    old_size = size;
  }
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr != NULL) {
    memset(new_ptr, 0, bytes);
  }

  return new_ptr;
}

static inline void print_block(const int verbosity, __NotNull Block *block) {
  debug_assert(blocks_size > 0);
  debug_assert(is_block(block));

  const PayloadSize header_payload_size = get_payload_size(block);
  const BlockState header_state = get_state(block);
  Payload *payload = get_payload(block);
  printf("[%p] | (%x) Size: %u; State: %u |\n", block, block->header,
         header_payload_size, header_state);
  printf("      [%p] | ", payload);

  Word length = verbosity < 2 ? 0
                : verbosity < 3 && header_payload_size > 32
                  ? 32
                  : header_payload_size;

  for (size_t index = 0; index < length; index++) {
    Payload *shifted_payload = shift_right(payload, index);
    uint8_t byte = *(uint8_t *)shifted_payload;
    printf("%.2x ", byte);
  }

  if (verbosity < 2 || (verbosity < 3 && header_payload_size > 32)) {
    printf("... ");
  }

  BoundaryTag *footer = get_footer(block);
  const PayloadSize footer_payload_size = extract_payload_size(*footer);
  const BlockState footer_state = extract_block_state(*footer);
  printf("|\n      [%p] | (%x) Size: %u; State: %u |\n", footer, *footer,
         footer_payload_size, footer_state);
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
  // exit if any invariant was not preserved
  debug_assert(mem_heapsize() == blocks_size + ALIGNMENT - HEADER_SIZE);
  if (blocks_size > 0) {
    debug_assert((void *)last_block < mem_heap_hi());
  }

  if (verbose > 0) {
    if (blocks_size == 0) {
      printf("There are no blocks.\n");
      return;
    }

    uint32_t index = 0;
    iterate_blocks(block, printf("%.4u: ", index); print_block(verbose, block);
                   index++;);

    printf("\n");
  }
}
