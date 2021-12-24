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
#define debug(statement) statement
#define debug_msg(...) printf(__VA_ARGS__)
#define debug_trace(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define debug_assert(expression) assert(expression)
#else
#define debug(statement)
#define debug_msg(...)
#define debug_trace(fmt, ...)
#define debug_assert(expression)
#endif

#define __Unused __attribute__((unused))
#define __Deprecated __attribute__((deprecated))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

// Annotations for developer

/**
 * Indicates that variable, function parameter or function result may be equal
 * to NULL.
 */
#define __Nullable

#define MINIMUM_BLOCK_SIZE ALIGNMENT

typedef void *Payload;
typedef uint32_t Word;
typedef Word BoundaryTag;
typedef BoundaryTag Header;
typedef BoundaryTag Footer;
typedef Word UnalignedPayloadSize;
typedef Word PayloadSize;
typedef Word BlockSize;
typedef Word UnalignedBlockSize;
typedef Word BlockState;

#define HEADER_SIZE sizeof(Header)
#define FOOTER_SIZE sizeof(Footer)

struct block {
  Header header;
  /**
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
  // As we don't know payload size here, we need to manually get the footer.
  // Footer footer;
};

typedef struct block *Block;

/**
 * Block without its structure.
 */
typedef Block UninitBlock;
typedef Block FreeBlock;
typedef Block AllocatedBlock;

#ifdef DEBUG
typedef enum {
  MALLOC,
  FREE,
  REALLOC,
} OperationType;
#endif

static Block first_block;
static Block last_block;
static Word blocks_size;
debug(static uint32_t verbosity = 0;)
  debug(static uint32_t operation_counter = 1;);

#define BLOCK_SIZE_MASK (-ALIGNMENT)

#define shift_one_left(shift) (0x1 << (shift))
#define PROPERTIES_SIZE 3

#define ALLOCATED_PROPERTY 0
#define NEXT_ALLOCATED_PROPERTY 1
#define PREVIOUS_ALLOCATED_PROPERTY 2

static inline const bool is_property_mask(const Word property_mask) {
  return !(property_mask & (property_mask - 1)) &&
         property_mask <= shift_one_left(PROPERTIES_SIZE - 1);
}

static inline const bool is_bool(const bool boolean) {
  return boolean == 0 || boolean == 1;
}

static inline const bool is_aligned(const Word word) {
  return (word & ~BLOCK_SIZE_MASK) == 0;
}

static inline const bool is_block_size(const BlockSize block_size) {
  return is_aligned(block_size);
}

static inline const bool is_payload_size(const PayloadSize payload_size) {
  return is_aligned(payload_size & ~0x8 & ~0x4) &&
         (~payload_size & 0x8 & 0x4) == 0;
}

static inline const UnalignedBlockSize
unaligned_payload_to_block_size(const UnalignedPayloadSize size) {
  return HEADER_SIZE + size;
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

  const PayloadSize payload_size = block_size - HEADER_SIZE;

  debug_assert(is_payload_size(payload_size));
  return payload_size;
}

static inline const BlockSize extract_block_size(const BoundaryTag tag) {
  return tag & BLOCK_SIZE_MASK;
}

inline static bool is_uninit_block(__Nullable UninitBlock block) {
  return block != NULL && is_aligned((size_t)block + HEADER_SIZE);
}

inline static bool is_block(__Nullable Block block) {
  return is_uninit_block(block) &&
         extract_block_size(block->header) >= MINIMUM_BLOCK_SIZE;
}

static inline const bool is_block_state(const BlockState state) {
  return (state & BLOCK_SIZE_MASK) == 0;
}

static inline const BlockState extract_header_state(const Header header) {
  return header & ~BLOCK_SIZE_MASK;
}

static inline const BlockState get_state(UninitBlock block) {
  debug_assert(is_uninit_block(block));

  const Header header = block->header;
  const BlockState state = extract_header_state(header);

  debug_assert(is_block_state(state));
  return state;
}

static inline const bool get_property(UninitBlock block,
                                      const Word property_index) {
  debug_assert(is_uninit_block(block));
  debug_assert(property_index <= PROPERTIES_SIZE);

  const Word property_mask = shift_one_left(property_index);
  debug_assert(is_property_mask(property_mask));

  return (get_state(block) & property_mask) >> property_index;
}

static inline const bool is_allocated(Block block) {
  debug_assert(is_block(block));

  return get_property(block, ALLOCATED_PROPERTY);
}

static inline bool is_free(Block block) {
  debug_assert(is_block(block));

  return !is_allocated(block);
}

static inline bool is_next_allocated(Block block) {
  debug_assert(is_block(block));

  return get_property(block, NEXT_ALLOCATED_PROPERTY);
}

static inline bool is_next_free(Block block) {
  debug_assert(is_block(block));

  return !is_next_allocated(block);
}

static inline bool is_previous_allocated(Block block) {
  debug_assert(is_block(block));

  return get_property(block, PREVIOUS_ALLOCATED_PROPERTY);
}

static inline bool is_previous_free(Block block) {
  debug_assert(is_block(block));

  return !is_previous_allocated(block);
}

inline static bool is_free_block(__Nullable FreeBlock block) {
  return is_block(block) && is_free(block);
}

inline static bool is_allocated_block(__Nullable AllocatedBlock block) {
  return is_block(block) && is_allocated(block);
}

static inline const Word round_to_alignment(const Word size) {
  return (size + ALIGNMENT - 1) & BLOCK_SIZE_MASK;
}

#define shift_right(pointer, offset) (void *)(pointer) + (offset)

#define shift_left(pointer, offset) (void *)(pointer) - (offset)

static inline bool compare_payloads(const Payload first, const Payload second,
                                    const BlockSize size) {
  debug_assert(first != NULL);
  debug_assert(second != NULL);
  debug_assert(is_block_size(size));

  const PayloadSize payload_size = size == 0 ? 0 : block_to_payload_size(size);
  for (size_t index = 0; index < payload_size; index++) {
    if (shift_right(first, index) != shift_right(second, index)) {
      return false;
    }
  }

  return true;
}

static inline Payload *get_payload(UninitBlock block) {
  debug_assert(is_uninit_block(block));

  Payload payload = block->payload;

  debug_assert(payload != NULL);
  debug_assert(shift_right(block, HEADER_SIZE) == payload);
  return payload;
}

static inline const BlockSize get_block_size(Block block) {
  debug_assert(is_block(block));

  const Header header = block->header;
  const BlockSize block_size = extract_block_size(header);

  debug_assert(is_block_size(block_size));
  return block_size;
}

static inline const PayloadSize get_payload_size(Block block) {
  debug_assert(is_block(block));

  const BlockSize block_size = get_block_size(block);
  const PayloadSize payload_size = block_to_payload_size(block_size);

  debug_assert(is_payload_size(payload_size));
  return payload_size;
}

static inline Footer *get_footer_from_block_size(FreeBlock block,
                                                 const BlockSize size) {
  debug_assert(is_free_block(block));
  debug_assert(is_block_size(size));

  Footer *footer = shift_right(block, size - FOOTER_SIZE);

  debug_assert(footer != NULL);
  return footer;
}

static inline Footer *get_footer(FreeBlock block) {
  const BlockSize block_size = get_block_size(block);
  return get_footer_from_block_size(block, block_size);
}

#ifdef DEBUG
#define GET_BLOCK_SNAPSHOT(name, block)                                        \
  __Unused const BlockSize name##_header_block_size =                          \
    extract_block_size(block->header);                                         \
  __Unused const BlockState name##_block_state =                               \
    extract_header_state(block->header);                                       \
  __Unused const Payload name##_payload = get_payload(block);
#else
#define GET_BLOCK_SNAPSHOT(name, block)
#endif

static inline const BoundaryTag with_block_size(const BoundaryTag tag,
                                                const BlockSize size) {
  debug_assert(is_block_size(size));

  return (tag & ~BLOCK_SIZE_MASK) | size;
}

static inline void set_header_block_size(UninitBlock block,
                                         const BlockSize size) {
  debug_assert(is_uninit_block(block));
  debug_assert(is_block_size(size));

  GET_BLOCK_SNAPSHOT(old, block);

  Header *header = &block->header;
  *header = with_block_size(*header, size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_header_block_size == size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_footer_block_size(UninitBlock block,
                                         const BlockSize size) {
  debug_assert(is_uninit_block(block));
  debug_assert(is_block_size(size));

  GET_BLOCK_SNAPSHOT(old, block);

  Footer *footer = get_footer_from_block_size(block, size);
  *footer = with_block_size(*footer, size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug(const BlockSize new_footer_block_size =
          extract_block_size(*get_footer(block)));
  debug_assert(new_footer_block_size == size);
  debug_assert(old_header_block_size == new_header_block_size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_allocated_uninit_block_size(UninitBlock block,
                                                   const BlockSize size) {
  debug_assert(is_uninit_block(block));

  set_header_block_size(block, size);
}

static inline void set_allocated_block_size(AllocatedBlock block,
                                            const BlockSize size) {
  debug_assert(is_allocated_block(block));

  set_allocated_uninit_block_size(block, size);
}

static inline void set_free_uninit_block_size(UninitBlock block,
                                              const BlockSize size) {
  debug_assert(is_uninit_block(block));

  set_header_block_size(block, size);
  set_footer_block_size(block, size);

  debug_assert(extract_block_size(block->header) ==
               extract_block_size(*get_footer(block)));
}

static inline void set_free_block_size(FreeBlock block, const BlockSize size) {
  debug_assert(is_free_block(block));

  set_free_uninit_block_size(block, size);
}

static inline const Header with_block_state(const Header header,
                                            const BlockState state) {
  debug_assert(is_block_state(state));

  return (header & BLOCK_SIZE_MASK) | state;
}

static inline void set_state(UninitBlock block, const BlockState state) {
  debug_assert(is_uninit_block(block));
  debug_assert(is_block_state(state));

  GET_BLOCK_SNAPSHOT(old, block);

  Header *header = &block->header;
  *header = with_block_state(*header, state);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_block_state == state);
  debug_assert(old_header_block_size == new_header_block_size);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_property(UninitBlock block, const Word property_index,
                                const bool value) {
  debug_assert(is_uninit_block(block));
  debug_assert(property_index <= PROPERTIES_SIZE);
  debug_assert(is_bool(value));

  const BlockState property_mask = shift_one_left(property_index);
  debug_assert(is_property_mask(property_mask));

  const BlockState state = get_state(block);
  const BlockState zeroed_property = state & ~property_mask;
  set_state(block, zeroed_property | (value << property_index));

  debug_assert((state & ~property_mask) == (get_state(block) & ~property_mask));
  debug_assert(get_property(block, property_index) == value);
}

static inline void set_allocated_property(UninitBlock block, const bool value) {
  set_property(block, ALLOCATED_PROPERTY, value);
}

static inline void set_free(UninitBlock block) {
  set_allocated_property(block, false);
}

static inline void set_allocated(UninitBlock block) {
  set_allocated_property(block, true);
}

static inline AllocatedBlock initialize_allocated_block(UninitBlock block,
                                                        const BlockSize size) {
  debug_assert(is_uninit_block(block));

  set_allocated(block);
  set_allocated_uninit_block_size(block, size);

  debug_assert(is_allocated_block(block));
  return block;
}

static inline FreeBlock initialize_free_block(UninitBlock block,
                                              const BlockSize size) {
  debug_assert(is_uninit_block(block));

  set_free(block);
  set_free_uninit_block_size(block, size);

  debug_assert(is_free_block(block));
  return block;
}

static inline void set_next_allocated_property(Block block, const bool value) {
  debug_assert(is_block(block));

  set_property(block, NEXT_ALLOCATED_PROPERTY, value);
}

static inline void set_next_free(Block block) {
  debug_assert(is_block(block));

  set_next_allocated_property(block, false);
}

static inline void set_next_allocated(Block block) {
  debug_assert(is_block(block));

  set_next_allocated_property(block, true);
}

static inline void set_previous_allocated_property(Block block,
                                                   const bool value) {
  debug_assert(is_block(block));

  set_property(block, PREVIOUS_ALLOCATED_PROPERTY, value);
}

static inline void set_previous_free(Block block) {
  debug_assert(is_block(block));

  set_previous_allocated_property(block, false);
}

static inline void set_previous_allocated(Block block) {
  debug_assert(is_block(block));

  set_previous_allocated_property(block, true);
}

/**
 * Returns next block. Given block must not be the last one.
 */
static inline Block get_next_block(Block block) {
  debug_assert(is_block(block));
  debug_assert(block != last_block);
  debug_assert(blocks_size > 0);

  const BlockSize block_size = get_block_size(block);
  Block next_block = shift_right(block, block_size);

  debug_assert(is_block(next_block));
  return next_block;
}

/**
 * Returns next block or NULL if the given block was the last one.
 */
static inline __Nullable Block maybe_get_next_block(Block block) {
  debug_assert(is_block(block));

  if (block == last_block) {
    return NULL;
  }
  debug_assert(block < last_block);

  return get_next_block(block);
}

#define iterate_blocks(block, handler)                                         \
  {                                                                            \
    Block block = first_block;                                                 \
    for (; block != last_block; block = get_next_block(block)) {               \
      debug_assert(block < last_block);                                        \
      handler;                                                                 \
    }                                                                          \
    handler;                                                                   \
  }

#ifdef DEBUG
static inline void print_block(Block block, const int verbosity) {
  debug_assert(blocks_size > 0);
  debug_assert(is_block(block));

  const BlockSize header_block_size = get_block_size(block);
  if (verbosity < 3) {
    printf("%u; ", header_block_size);
    return;
  }

  const PayloadSize header_payload_size = get_payload_size(block);
  Payload *payload = get_payload(block);
  printf("[%p] | (%x) Block size: %u; Payload size: %u; Allocated: %u; "
         "Previous allocated: %u |\n",
         block, block->header, header_block_size, header_payload_size,
         is_allocated(block), is_previous_allocated(block));
  printf("      [%p] | ", payload);

  Word length = header_payload_size;
  if (verbosity < 4) {
    length = 0;
  } else if (verbosity < 5 && header_payload_size > 32) {
    length = 32;
  }

  for (size_t index = 0; index < length; index++) {
    Payload *shifted_payload = shift_right(payload, index);
    uint8_t byte = *(uint8_t *)shifted_payload;
    printf("%.2x ", byte);
  }

  if (verbosity < 4 || (verbosity < 5 && header_payload_size > 32)) {
    printf("... ");
  }
  printf("|\n");

  if (is_free(block)) {
    BoundaryTag *footer = get_footer(block);
    const BlockSize footer_block_size = extract_block_size(*footer);
    const PayloadSize footer_payload_size =
      block_to_payload_size(footer_block_size);
    printf("      [%p] | (%x) Block size: %u; Payload size: %u |\n", footer,
           *footer, footer_block_size, footer_payload_size);
  }
}

static inline void check_invariants() {
  debug_assert(mem_heapsize() == blocks_size + ALIGNMENT - HEADER_SIZE);

  if (blocks_size > 0) {
    debug_assert((void *)last_block < mem_heap_hi());

    iterate_blocks(
      block, __Nullable Block next = maybe_get_next_block(block);
      if (next != NULL) {
        if (is_allocated(block) != is_previous_allocated(next)) {
          print_block(block, 3);
          print_block(next, 3);
        }
        debug_assert(is_allocated(block) == is_previous_allocated(next));
      });
  }
}

static inline void put_operation_name(OperationType operation, char **name) {
  switch (operation) {
    case MALLOC:
      *name = "malloc";
      break;
    case FREE:
      *name = "free";
      break;
    case REALLOC:
      *name = "realloc";
      break;
    default:
      *name = "?";
      break;
  }
}

static inline void check_heap(OperationType operation, size_t size) {
  check_invariants();

  if (verbosity == 0) {
    return;
  }

  if (blocks_size == 0) {
    printf("There are no blocks.\n");
    return;
  }

  char *operation_name[8];
  put_operation_name(operation, operation_name);

  debug(printf("%s %lu (%u): ", *operation_name, size, operation_counter););
  if (verbosity > 1) {
    printf("\n");
  }

  uint32_t index = 0;
  iterate_blocks(
    block, if (verbosity > 1) {
      printf("%.4u: ", index);
      print_block(block, verbosity);
    } index++;);
  if (verbosity == 2) {
    printf("\n");
  }
  printf("%u blocks\n", index);

  if (verbosity > 1) {
    printf("\n");
  }

  debug(operation_counter++;);
}
#endif

typedef Payload SbrkResult;

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
static inline __Nullable FreeBlock find_first_free_block(const BlockSize size) {
  debug_assert(is_block_size(size));
  debug_assert(is_block(first_block));
  debug_assert(is_block(last_block));
  debug_assert(blocks_size > 0);

  iterate_blocks(
    block, debug_assert(is_block(block));
    if (is_free(block) && get_block_size(block) >= size) {
      debug_assert(is_free_block(block));
      return block;
    });

  return NULL;
}

#undef handle_block

static inline __Nullable Payload allocate_new_block(const BlockSize size) {
  debug_assert(is_block_size(size));

  __Nullable SbrkResult allocated_space = allocate_heap_space(size);
  if (allocated_space == NULL) {
    return NULL;
  }

  UninitBlock uninit_block = (UninitBlock)allocated_space;

  AllocatedBlock block = initialize_allocated_block(uninit_block, size);
  // We call this function if all blocks were allocated, so previous must be
  // allocated.
  set_previous_allocated(uninit_block);

  last_block = block;

  return get_payload(block);
}

static inline __Nullable Payload
allocate_to_extended_last_block(FreeBlock block, const BlockSize size) {
  debug_assert(is_free_block(block));
  debug_assert(block == last_block);
  debug_assert(shift_right(block, get_block_size(block) - 1) == mem_heap_hi());
  // We call this function on first free block, so previous must be allocated.
  debug_assert(is_previous_allocated(block));
  debug_assert(is_block_size(size));

  const BlockSize old_size = get_block_size(block);
  const BlockSize additional_space = size - old_size;

  const SbrkResult result = allocate_heap_space(additional_space);
  if (result == NULL) {
    return NULL;
  }

  set_allocated(block);

  AllocatedBlock allocated_block = block;
  debug_assert(is_allocated_block(allocated_block));

  set_allocated_block_size(allocated_block, size);

  return get_payload(allocated_block);
}

static inline Payload allocate_with_split(FreeBlock block,
                                          const BlockSize size) {
  debug_assert(is_free_block(block));
  // We call this function on first free block, so previous must be allocated.
  debug_assert(is_previous_allocated(block));
  debug_assert(is_block_size(size));

  const BlockSize old_block_size = get_block_size(block);
  const BlockSize empty_block_size = old_block_size - size;
  debug_assert(is_block_size(empty_block_size));

  set_allocated(block);

  AllocatedBlock allocated_block = block;
  debug_assert(is_allocated_block(allocated_block));

  const Payload payload = get_payload(allocated_block);

  // Block is too small to split, its size stays the same.
  if (empty_block_size < MINIMUM_BLOCK_SIZE) {
    __Nullable Block next = maybe_get_next_block(block);

    if (next != NULL) {
      set_previous_allocated(next);
    }

    return payload;
  }

  set_allocated_block_size(allocated_block, size);

  UninitBlock empty_uninit_block = shift_right(allocated_block, size);
  debug_assert(is_uninit_block(empty_uninit_block));

  FreeBlock empty_block =
    initialize_free_block(empty_uninit_block, empty_block_size);
  set_previous_allocated(empty_block);

  debug_assert(shift_right(block, old_block_size - FOOTER_SIZE) ==
               get_footer(empty_block));

  if (allocated_block == last_block) {
    last_block = empty_block;
  }

  return payload;
}

static inline Payload allocate(UnalignedPayloadSize size) {
  debug_assert(size < MAX_HEAP);

  const UnalignedBlockSize unaligned_block_size =
    unaligned_payload_to_block_size(size);
  const BlockSize block_size = round_to_alignment(unaligned_block_size);

  // This is the first allocation.
  if (heap_has_no_allocated_blocks()) {
    // There are no previous blocks, so previous block is not free - it is
    // allocated.
    return allocate_new_block(block_size);
  }

  __Nullable FreeBlock found_block = find_first_free_block(block_size);

  // Found empty block with sufficient space.
  if (found_block != NULL) {
    return allocate_with_split(found_block, block_size);
  }

  // Last block is free, but too small.
  if (is_free(last_block)) {
    FreeBlock block = last_block;
    debug_assert(is_free_block(block));

    return allocate_to_extended_last_block(block, block_size);
  }

  // Last block was allocated, so we need to allocate a new one.
  __Nullable Payload payload = allocate_new_block(block_size);
  return payload;
}

/**
 * Malloc
 */
void *malloc(size_t size) {
  void *result = allocate(size);

  debug(check_heap(MALLOC, size););

  return result;
}

static inline Footer *get_previous_footer(Block block) {
  debug_assert(is_block(block));
  debug_assert(is_previous_free(block));
  debug_assert(block != first_block);
  debug_assert(blocks_size > 0);

  BoundaryTag *previous_footer = shift_left(block, FOOTER_SIZE);

  debug(const BlockSize previous_footer_block_size =
          extract_block_size(*previous_footer));
  debug(Block previous_block = shift_left(block, previous_footer_block_size));
  debug_assert(is_free_block(previous_block));
  debug_assert(previous_footer_block_size == get_block_size(previous_block));

  return previous_footer;
}

/**
 * Returns previous block. Given block must have free previous block property.
 */
static inline FreeBlock get_previous_block(Block block) {
  BoundaryTag *previous_footer = get_previous_footer(block);
  const BlockSize previous_block_size = extract_block_size(*previous_footer);
  debug_assert(is_block_size(previous_block_size));

  FreeBlock previous_block = shift_left(block, previous_block_size);

  debug_assert(is_free_block(previous_block));
  return previous_block;
}

static inline AllocatedBlock get_block_from_payload(Payload payload) {
  debug_assert(payload != NULL);

  AllocatedBlock block = shift_left(payload, HEADER_SIZE);

  debug_assert(is_allocated_block(block));
  return block;
}

static inline void deallocate(Payload payload) {
  AllocatedBlock block = get_block_from_payload(payload);
  BlockSize block_size = get_block_size(block);

  // TODO: use NEXT_ALLOCATED property (set it in malloc first)
  __Nullable Block next_block = maybe_get_next_block(block);
  if (next_block != NULL) {
    if (is_free(next_block)) {
      block_size += get_block_size(next_block);

      if (next_block == last_block) {
        last_block = block;
      }
    } else {
      set_previous_free(next_block);
    }
  }

  if (is_previous_free(block)) {
    FreeBlock previous_block = get_previous_block(block);
    block_size += get_block_size(previous_block);

    if (block == last_block) {
      last_block = previous_block;
    }
    block = previous_block;
  }

  set_free(block);
  set_free_block_size(block, block_size);
}

/**
 * Free
 */
void free(void *ptr) {
  if (ptr == NULL) {
    return;
  }

  deallocate(ptr);

  debug(check_heap(FREE, 0););
}

static inline Payload reallocate(Payload old_payload,
                                 UnalignedPayloadSize size) {
  Block block = get_block_from_payload(old_payload);
  size_t old_size = get_payload_size(block);

  if (size == old_size) {
    return old_payload;
  }

  // TODO: poszerzanie bloku
  // TODO: zmniejszanie bloku

  // jeśli «ptr» nie jest równy «NULL», to musiał zostać zwrócony przez
  // procedurę «mm_malloc» lub
  // «mm_realloc», i należy zmienić rozmiar przydzielonego bloku. Dopuszcza się
  // przeniesienie bloku pod nowy adres różny od «ptr». Jeśli użytkownik
  // zwiększa rozmiar bloku, to dodatkowa pamięć w bloku musi pozostać
  // niezainicjowana.

  Payload new_payload = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (new_payload == NULL) {
    return NULL;
  }

  /* Copy the old data. */
  if (size < old_size) {
    old_size = size;
  }
  memcpy(new_payload, old_payload, old_size);

  /* Free the old block. */
  free(old_payload);

  return new_payload;
}

/**
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 */
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_payload is NULL, then this is just malloc. */
  if (old_ptr == NULL) {
    return malloc(size);
  }

  void *result = reallocate(old_ptr, size);

  debug(check_heap(REALLOC, size););
  return result;
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

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
  debug(verbosity = verbose;);
}
