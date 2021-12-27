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
 * This code is correct and blazing fast, but very bad usage-wise since
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
// #define DEBUG
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

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define MINIMUM_BLOCK_SIZE ALIGNMENT

typedef void *MemoryLocation;
typedef uint32_t Word;

typedef Word BoundaryTag;
typedef BoundaryTag Header;
typedef BoundaryTag Footer;

typedef MemoryLocation Payload;

typedef Word UnalignedPayloadSize;
typedef Word PayloadSize;

typedef Word BlockSize;
typedef Word UnalignedBlockSize;

typedef Word BlockState;

typedef BoundaryTag NodeAddress;

#define HEADER_SIZE sizeof(Header)
#define FOOTER_SIZE sizeof(Footer)

typedef MemoryLocation NullableBlock;
typedef MemoryLocation RawBlock;
typedef struct {
  Header header;
  /**
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
} * AnyBlock;

typedef struct {
  Header header;
  NodeAddress previous;
  NodeAddress next;
  /**
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
  // As we don't know payload size here, we need to manually get the footer.
  // Footer footer;
} * FreeBlock;

typedef AnyBlock AllocatedBlock;

typedef union {
  NullableBlock nullable;
  RawBlock raw;
  AnyBlock any;
  FreeBlock free;
  AllocatedBlock allocated;
} Block;

typedef FreeBlock Cursor;

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
static Cursor root;
static NodeAddress root_address;
static Cursor back;
static NodeAddress back_address;
debug(static uint32_t verbosity = 0;);
debug(static uint32_t operation_counter = 1;);

#define BLOCK_SIZE_MASK (-ALIGNMENT)

#define shift_one_left(shift) (0x1 << (shift))
#define PROPERTIES_SIZE 3

#define ALLOCATED_PROPERTY 0
#define PREVIOUS_ALLOCATED_PROPERTY 1

static const NodeAddress EMPTY_NODE_ADDRESS = 0;

#define shift_right(pointer, offset) (void *)(pointer) + (offset)

#define shift_left(pointer, offset) (void *)(pointer) - (offset)

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

inline static const bool is_raw_block(const Block block) {
  return block.nullable != NULL &&
         is_aligned((size_t)shift_right(block.raw, HEADER_SIZE));
}

inline static const bool is_any_block(const Block block) {
  return is_raw_block(block) &&
         extract_block_size(block.any->header) >= MINIMUM_BLOCK_SIZE;
}

static inline const bool is_block_state(const BlockState state) {
  return (state & BLOCK_SIZE_MASK) == 0;
}

static inline const BlockState extract_header_state(const Header header) {
  return header & ~BLOCK_SIZE_MASK;
}

static inline const BlockState get_state(const Block block) {
  debug_assert(is_raw_block(block));

  const Header header = block.any->header;
  const BlockState state = extract_header_state(header);

  debug_assert(is_block_state(state));
  return state;
}

static inline const bool get_property(const Block block,
                                      const Word property_index) {
  debug_assert(is_raw_block(block));
  debug_assert(property_index <= PROPERTIES_SIZE);

  const Word property_mask = shift_one_left(property_index);
  debug_assert(is_property_mask(property_mask));

  return (get_state(block) & property_mask) >> property_index;
}

static inline const bool is_allocated(const Block block) {
  return get_property(block, ALLOCATED_PROPERTY);
}

static inline const bool is_free(const Block block) {
  return !is_allocated(block);
}

static inline const bool is_previous_allocated(const Block block) {
  return get_property(block, PREVIOUS_ALLOCATED_PROPERTY);
}

static inline const bool is_previous_free(const Block block) {
  return !is_previous_allocated(block);
}

static inline const bool is_free_block(const Block block) {
  return is_any_block(block) && is_free(block);
}

static inline const bool is_allocated_block(const Block block) {
  return is_any_block(block) && is_allocated(block);
}

static inline const Word round_to_alignment(const Word size) {
  return (size + ALIGNMENT - 1) & BLOCK_SIZE_MASK;
}

#define DECLARE_FROM_FUNCTION(name, type)                                      \
  static inline Block from_##name(type name##_block) {                         \
    const Block block = {.name = name##_block};                                \
    debug_assert(is_##name##_block(block));                                    \
    return block;                                                              \
  }

DECLARE_FROM_FUNCTION(raw, RawBlock)
DECLARE_FROM_FUNCTION(any, AnyBlock)
DECLARE_FROM_FUNCTION(free, FreeBlock)
DECLARE_FROM_FUNCTION(allocated, AllocatedBlock)

static inline const Block from_nullable(const NullableBlock nullable_block) {
  debug_assert(nullable_block != NULL);
  const Block block = {.nullable = nullable_block};
  return block;
}

#define DECLARE_INTO_FUNCTION(name, type)                                      \
  static inline type into_##name(const Block block) {                          \
    debug_assert(is_##name##_block(block));                                    \
    return block.name;                                                         \
  }

DECLARE_INTO_FUNCTION(raw, RawBlock)
DECLARE_INTO_FUNCTION(any, AnyBlock)
DECLARE_INTO_FUNCTION(free, FreeBlock)
DECLARE_INTO_FUNCTION(allocated, AllocatedBlock)

static inline const NullableBlock into_nullable(const Block block) {
  return block.nullable;
}

static inline const RawBlock shift_right_block(const Block block,
                                               const size_t amount) {
  const RawBlock result = shift_right(into_raw(block), amount);
  debug_assert(is_raw_block(from_raw(result)));
  return result;
}

static inline const RawBlock shift_left_block(const Block block,
                                              const size_t amount) {
  const RawBlock result = shift_left(into_raw(block), amount);
  debug_assert(is_raw_block(from_raw(result)));
  return result;
}

static inline const bool compare_payloads(const Payload first,
                                          const Payload second,
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

static inline const Payload get_payload(const AllocatedBlock allocated_block) {
  const Payload payload = allocated_block->payload;

  debug_assert(payload != NULL);
  debug_assert(shift_right(allocated_block, HEADER_SIZE) == payload);
  return payload;
}

static inline const BlockSize get_block_size(const Block block) {
  const AnyBlock any_block = into_any(block);
  const Header header = any_block->header;
  const BlockSize block_size = extract_block_size(header);

  debug_assert(is_block_size(block_size));
  return block_size;
}

static inline const BlockSize get_free_block_size(const FreeBlock free_block) {
  const Block block = from_free(free_block);
  return get_block_size(block);
}

static inline const BlockSize
get_allocated_block_size(const AllocatedBlock allocated_block) {
  const Block block = from_allocated(allocated_block);
  return get_block_size(block);
}

static inline const PayloadSize get_payload_size(const Block block) {
  const BlockSize block_size = get_block_size(block);
  const PayloadSize payload_size = block_to_payload_size(block_size);

  debug_assert(is_payload_size(payload_size));
  return payload_size;
}

static inline Footer *get_footer_from_block_size(const FreeBlock free_block,
                                                 const BlockSize size) {
  debug_assert(is_block_size(size));

  Footer *footer = shift_right(free_block, size - FOOTER_SIZE);

  debug_assert(footer != NULL);
  return footer;
}

static inline Footer *get_footer(const FreeBlock free_block) {
  const BlockSize block_size = get_free_block_size(free_block);
  return get_footer_from_block_size(free_block, block_size);
}

#define compare_blocks(first, relation, second)                                \
  (into_raw((first)) - into_raw((second)) relation 0)

static inline bool is_first_block(const Block block) {
  return into_raw(block) == into_raw(first_block);
}

static inline bool is_last_block(const Block block) {
  const RawBlock raw = into_raw(block);
  return raw == into_raw(last_block);
}

static inline void set_first_block(const Block block) {
  first_block = block;
}

static inline void set_last_block(const Block block) {
  last_block = block;
}

#ifdef DEBUG
#define GET_BLOCK_SNAPSHOT(name, block)                                        \
  __Unused const BlockSize name##_header_block_size =                          \
    extract_block_size(block.any->header);                                     \
  __Unused const BlockState name##_block_state =                               \
    extract_header_state(block.any->header);                                   \
  __Unused const Payload name##_payload = get_payload(block.allocated);
#else
#define GET_BLOCK_SNAPSHOT(name, block)
#endif

static inline const BoundaryTag with_block_size(const BoundaryTag tag,
                                                const BlockSize size) {
  debug_assert(is_block_size(size));

  return (tag & ~BLOCK_SIZE_MASK) | size;
}

static inline void set_header_block_size(const RawBlock raw_block,
                                         const BlockSize size) {
  const Block block = from_raw(raw_block);
  debug_assert(is_block_size(size));

  GET_BLOCK_SNAPSHOT(old, block);

  Header *header = &block.any->header;
  *header = with_block_size(*header, size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_header_block_size == size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_footer_block_size(const FreeBlock free_block,
                                         const BlockSize size) {
  debug_assert(is_block_size(size));

  debug(Block block = from_free(free_block););
  GET_BLOCK_SNAPSHOT(old, block);

  Footer *footer = get_footer_from_block_size(free_block, size);
  *footer = with_block_size(*footer, size);

  GET_BLOCK_SNAPSHOT(new, block);
  debug(const BlockSize new_footer_block_size =
          extract_block_size(*get_footer(free_block)));
  debug_assert(new_footer_block_size == size);
  debug_assert(old_header_block_size == new_header_block_size);
  debug_assert(old_block_state == new_block_state);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_allocated_raw_block_size(const RawBlock raw_block,
                                                const BlockSize size) {
  set_header_block_size(raw_block, size);
}

static inline void set_allocated_block_size(const AllocatedBlock block,
                                            const BlockSize size) {
  set_allocated_raw_block_size(block, size);
}

static inline void set_free_raw_block_size(const RawBlock raw_block,
                                           const BlockSize size) {
  set_header_block_size(raw_block, size);
  const FreeBlock free_block = into_free(from_raw(raw_block));
  set_footer_block_size(free_block, size);

  debug_assert(extract_block_size(free_block->header) ==
               extract_block_size(*get_footer(free_block)));
}

static inline void set_free_block_size(const FreeBlock block,
                                       const BlockSize size) {
  set_free_raw_block_size(block, size);
}

static inline const Header with_block_state(const Header header,
                                            const BlockState state) {
  debug_assert(is_block_state(state));

  return (header & BLOCK_SIZE_MASK) | state;
}

static inline void set_state(const Block block, const BlockState state) {
  debug_assert(is_raw_block(block));
  debug_assert(is_block_state(state));

  GET_BLOCK_SNAPSHOT(old, block);

  Header *header = &block.any->header;
  *header = with_block_state(*header, state);

  GET_BLOCK_SNAPSHOT(new, block);
  debug_assert(new_block_state == state);
  debug_assert(old_header_block_size == new_header_block_size);
  debug_assert(
    compare_payloads(old_payload, new_payload, old_header_block_size));
}

static inline void set_property(const Block block, const Word property_index,
                                const bool value) {
  debug_assert(is_raw_block(block));
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

static inline void set_allocated_property(const Block block, const bool value) {
  set_property(block, ALLOCATED_PROPERTY, value);
}

static inline void set_free(const Block block) {
  set_allocated_property(block, false);
}

static inline void set_allocated(const Block block) {
  set_allocated_property(block, true);
}

static inline void set_previous_allocated_property(const Block block,
                                                   const bool value) {
  debug_assert(is_any_block(block));

  set_property(block, PREVIOUS_ALLOCATED_PROPERTY, value);
}

static inline void set_previous_free(const Block block) {
  debug_assert(is_any_block(block));

  set_previous_allocated_property(block, false);
}

static inline void set_previous_allocated(const Block block) {
  debug_assert(is_any_block(block));

  set_previous_allocated_property(block, true);
}

static inline const bool is_empty_cursor(const Cursor cursor) {
  return cursor == NULL;
}

static inline const bool is_root_cursor(const Cursor cursor) {
  return cursor == root;
}

static inline const bool is_back_cursor(const Cursor cursor) {
  return cursor == back;
}

static inline const bool is_cursor(const Cursor cursor) {
  return is_free_block(from_free(cursor));
}

static inline const bool is_null_node_address(const NodeAddress address) {
  return address == EMPTY_NODE_ADDRESS;
}

static inline const bool is_node_address(const NodeAddress address) {
  return !is_null_node_address(address) &&
         is_block_size(extract_block_size(address));
}

static inline const Cursor node_address_to_cursor(const NodeAddress address) {
  debug_assert(is_node_address(address));
  const BlockSize offset = extract_block_size(address);
  const RawBlock raw_block = shift_right_block(first_block, offset);
  const Block block = from_raw(raw_block);
  return (Cursor)into_free(block);
}

static inline const NodeAddress cursor_to_node_address(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  debug_assert(compare_blocks(from_free(cursor), >=, first_block));
  const BlockSize offset = shift_left(cursor, into_raw(first_block));
  debug_assert(is_block_size(offset));
  // Set the lowest bit to indicate that this is not an empty address.
  const NodeAddress address = (offset & BLOCK_SIZE_MASK) | 1;
  return address;
}

static inline const bool test_is_root_cursor(const Cursor cursor) {
  return is_root_cursor(cursor) && is_cursor(cursor) &&
         !is_empty_cursor(cursor) && cursor->previous == EMPTY_NODE_ADDRESS &&
         cursor_to_node_address(cursor) == root_address;
}

static inline void print_cursor(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  printf("[%p] %x <- %x -> %x\n", cursor, cursor->previous,
         cursor_to_node_address(cursor), cursor->next);
}

static inline void set_root(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  root = cursor;
  root_address = cursor_to_node_address(cursor);
}

static inline void set_back(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  back = cursor;
  back_address = cursor_to_node_address(cursor);
}

static inline const Cursor new_cursor(const FreeBlock block) {
  return (Cursor)block;
}

static inline const FreeBlock front() {
  return root;
}

static inline const Cursor move_next(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  const NodeAddress next = cursor->next;
  const Cursor next_cursor = node_address_to_cursor(next);
  debug_assert(is_cursor(next_cursor));
  return next_cursor;
}

static inline const Cursor move_previous(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  const NodeAddress previous = cursor->previous;
  const Cursor previous_cursor = node_address_to_cursor(previous);
  debug_assert(is_cursor(previous_cursor));
  return previous_cursor;
}

static inline const FreeBlock current_item(const Cursor cursor) {
  return (FreeBlock)cursor;
}

static inline void push_front(const FreeBlock item) {
  const Cursor cursor = new_cursor(item);
  if (is_empty_cursor(root)) {
    debug_assert(is_empty_cursor(back));
    cursor->next = EMPTY_NODE_ADDRESS;
    cursor->previous = EMPTY_NODE_ADDRESS;
    set_root(cursor);
    set_back(cursor);
    return;
  }
  debug_assert(test_is_root_cursor(root));
  debug_assert(is_cursor(cursor));
  const NodeAddress address = cursor_to_node_address(cursor);
  debug_assert(is_null_node_address(root->previous));
  root->previous = address;
  cursor->next = root_address;
  cursor->previous = EMPTY_NODE_ADDRESS;
  set_root(cursor);
}

static inline void push_back(const FreeBlock item) {
  const Cursor cursor = new_cursor(item);
  if (is_empty_cursor(root)) {
    debug_assert(is_empty_cursor(back));
    cursor->next = EMPTY_NODE_ADDRESS;
    cursor->previous = EMPTY_NODE_ADDRESS;
    set_root(cursor);
    set_back(cursor);
    return;
  }
  // debug_assert(test_is_root_cursor(root));
  debug_assert(is_cursor(cursor));
  const NodeAddress address = cursor_to_node_address(cursor);
  debug_assert(is_null_node_address(back->next));
  back->next = address;
  cursor->next = EMPTY_NODE_ADDRESS;
  cursor->previous = back_address;
  set_back(cursor);
}

/**
 * Removes current element.
 */
static inline void remove_current(const Cursor cursor) {
  debug_assert(is_cursor(cursor));
  const NodeAddress previous_address = cursor->previous;
  const NodeAddress next_address = cursor->next;

  if (is_null_node_address(previous_address)) {
    if (is_null_node_address(next_address)) {
      debug_assert(cursor == root);
      debug_assert(cursor_to_node_address(cursor) == root_address);
      debug_assert(test_is_root_cursor(cursor));
      debug_assert(test_is_root_cursor(root));
      root = NULL;
      root_address = EMPTY_NODE_ADDRESS;
      back = NULL;
      back_address = EMPTY_NODE_ADDRESS;
    } else {
      const Cursor next_cursor = move_next(cursor);
      debug_assert(next_cursor->previous == cursor_to_node_address(cursor));
      next_cursor->previous = EMPTY_NODE_ADDRESS;
      if (is_root_cursor(cursor)) {
        debug_assert(test_is_root_cursor(cursor));
        set_root(next_cursor);
      }
    }
  } else {
    if (is_null_node_address(next_address)) {
      const Cursor previous_cursor = move_previous(cursor);
      debug_assert(previous_cursor->next == cursor_to_node_address(cursor));
      previous_cursor->next = EMPTY_NODE_ADDRESS;
      if (is_back_cursor(cursor)) {
        // debug_assert(test_is_root_cursor(cursor));
        set_back(previous_cursor);
      }
    } else {
      const Cursor previous_cursor = move_previous(cursor);
      debug_assert(previous_cursor->next == cursor_to_node_address(cursor));
      previous_cursor->next = next_address;
      const Cursor next_cursor = move_next(cursor);
      debug_assert(next_cursor->previous == cursor_to_node_address(cursor));
      next_cursor->previous = previous_address;
    }
  }
}

#define iterate_nodes(cursor, handler)                                         \
  {                                                                            \
    for (; !is_null_node_address(cursor->next); cursor = move_next(cursor)) {  \
      handler;                                                                 \
    }                                                                          \
    debug_assert(is_null_node_address(cursor->next));                          \
    handler;                                                                   \
  }

static inline const FreeBlock find_first_free_node(const BlockSize size) {
  Cursor cursor = root;
  if (is_empty_cursor(cursor)) {
    return NULL;
  }

  iterate_nodes(
    cursor, const FreeBlock block = current_item(cursor);
    const BlockSize item_size = get_free_block_size(block);
    if (item_size >= size) { return block; });

  return NULL;
}

#ifdef DEBUG
static inline const FreeBlock
find_node_with_address(const NodeAddress address) {
  Cursor cursor = root;
  if (is_empty_cursor(cursor)) {
    return NULL;
  }

  iterate_nodes(
    cursor, if (cursor_to_node_address(cursor) == address) { return cursor; });
  return NULL;
}

static inline void print_nodes() {
  Cursor cursor = root;
  if (is_empty_cursor(cursor)) {
    return;
  }
  iterate_nodes(cursor, print_cursor(cursor););
  return;
}

static inline bool nodes_double_contains(const NodeAddress address) {
  Cursor cursor = root;
  if (is_empty_cursor(cursor)) {
    return false;
  }
  bool found = false;

  iterate_nodes(
    cursor, if (cursor_to_node_address(cursor) == address) {
      if (found) {
        return true;
      }
      found = true;
    });
  return false;
}

static inline bool find_duplicates() {
  Cursor cursor = root;
  if (is_empty_cursor(cursor)) {
    return false;
  }
  iterate_nodes(cursor, nodes_double_contains(cursor_to_node_address(cursor)););
  return false;
}
#endif

static inline const AllocatedBlock
initialize_allocated_block(const RawBlock raw_block, const BlockSize size) {
  const Block block = from_raw(raw_block);

  set_allocated(block);
  set_allocated_raw_block_size(raw_block, size);

  return into_allocated(block);
}

static inline const FreeBlock initialize_free_block(const RawBlock raw_block,
                                                    const BlockSize size) {
  const Block block = from_raw(raw_block);

  set_free(block);
  set_free_raw_block_size(raw_block, size);

  const FreeBlock free_block = into_free(block);
  push_back(free_block);

  return free_block;
}

/**
 * Returns next block. Given block must not be the last one.
 */
static inline const Block get_next_block(const Block block) {
  debug_assert(!is_last_block(block));
  debug_assert(blocks_size > 0);

  const BlockSize block_size = get_block_size(block);
  const RawBlock next_block = shift_right_block(block, block_size);
  const Block result = from_raw(next_block);

  debug_assert(is_any_block(result));
  return result;
}

/**
 * Returns next block or NULL if the given block was the last one.
 */
static inline const NullableBlock maybe_get_next_block(const Block block) {
  if (is_last_block(block)) {
    return NULL;
  }
  debug_assert(into_raw(block) < into_raw(last_block));

  return into_nullable(get_next_block(block));
}

#define iterate_blocks(block, handler)                                         \
  {                                                                            \
    Block block = first_block;                                                 \
    for (; !is_last_block(block); block = get_next_block(block)) {             \
      debug_assert(into_raw(block) < into_raw(last_block));                    \
      handler;                                                                 \
    }                                                                          \
    handler;                                                                   \
  }

#ifdef DEBUG

#define color(color) "\e[48;5;" color "m"
#define GREEN "34"
#define RED "88"
#define RESET "\e[0m"

static inline void print_block(Block block, const uint32_t index,
                               const int verbosity) {
  debug_assert(blocks_size > 0);
  debug_assert(is_any_block(block));

  const BlockSize header_block_size = get_block_size(block);
  if (verbosity < 3) {
    if (is_free(block)) {
      printf(color(GREEN) "%u" RESET "; ", header_block_size);
    } else {
      printf(color(RED) "%u" RESET "; ", header_block_size);
    }
    return;
  }

  if (index > 0) {
    if (is_free(block)) {
      printf(color(GREEN) "%.4u" RESET ": ", index);
    } else {
      printf(color(RED) "%.4u" RESET ": ", index);
    }
  } else {
    printf("      ");
  }

  const PayloadSize header_payload_size = get_payload_size(block);
  // We want to print payload despite the block type.
  Payload *payload = get_payload(block.allocated);
  printf("[%p] | (%x) Size: %u; Alloc: %u; "
         "Prev alloc: %u",
         block.raw, block.any->header, header_block_size, is_allocated(block),
         is_previous_allocated(block));
  if (is_free(block)) {
    printf("; Prev: %x; Next: %x", block.free->previous, block.free->next);
  }
  printf(" |\n");
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
    BoundaryTag *footer = get_footer(into_free(block));
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
    debug_assert((void *)last_block.raw < mem_heap_hi());

    iterate_blocks(
      block, NullableBlock next_nullable = maybe_get_next_block(block);
      if (next_nullable != NULL) {
        Block next = from_nullable(next_nullable);
        if (is_allocated(block) != is_previous_allocated(next)) {
          print_block(block, 0, 4);
          print_block(next, 0, 4);
        }
        debug_assert(is_allocated(block) == is_previous_allocated(next));
      });

    iterate_blocks(
      block, NullableBlock next_nullable = maybe_get_next_block(block);
      if (is_free(block) && next_nullable != NULL) {
        Block next = from_nullable(next_nullable);
        debug_assert(!is_free(next));
      });

    // too slow for binary*.rep
    // iterate_blocks(
    //   block, if (is_free(block)) {
    //     const FreeBlock free_block = into_free(block);
    //     debug_assert(
    //       find_node_with_address(cursor_to_node_address(free_block)) !=
    //       NULL);
    //   });

    // find_duplicates();
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

static inline void check_heap(OperationType operation, void *input_payload,
                              size_t size, void *output_payload) {
  if (verbosity == 0) {
    check_invariants();
    return;
  }

  if (blocks_size == 0) {
    debug_msg("There are no blocks.\n");
    check_invariants();
    return;
  }

  char *operation_name[8];
  put_operation_name(operation, operation_name);

  debug_msg("%s ", *operation_name);
  if (operation != MALLOC) {
    debug_msg("%p ", input_payload);
  }
  if (operation != FREE) {
    debug_msg("%lu -> %p ", size, output_payload);
  }
  debug_msg("(%u): ", operation_counter);

  if (verbosity > 1) {
    debug_msg("\n");
  }

  uint32_t index = 1;
  iterate_blocks(
    block,
    if (verbosity > 1) { print_block(block, index, verbosity); } index++;);
  if (verbosity == 2) {
    printf("\n");
  }
  printf("%u block(s)\n", index - 1);

  if (verbosity > 1) {
    print_nodes();
    printf("\n");
  }

  debug(operation_counter++;);

  check_invariants();
}
#endif

/**
 * Allocates new uninitialized block. Returns NULL if allocation
 * fails.
 */
static inline const RawBlock new_raw_block(const BlockSize size) {
  debug_assert(is_block_size(size));

  const MemoryLocation result = mem_sbrk(size);
  if (result < 0) {
    return NULL;
  }

  const RawBlock block = (RawBlock)result;
  blocks_size += size;

  debug_assert(is_raw_block(from_raw(block)));
  return block;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  const MemoryLocation allocate_alignment_result =
    mem_sbrk(ALIGNMENT - HEADER_SIZE);
  if (allocate_alignment_result < 0) {
    return -1;
  }

  set_first_block(from_raw(mem_sbrk(0)));
  set_last_block(first_block);
  blocks_size = 0;
  root = NULL;
  root_address = EMPTY_NODE_ADDRESS;
  back = NULL;
  back_address = EMPTY_NODE_ADDRESS;

  return 0;
}

/**
 * Finds first free and sufficient block or returns NULL.
 */
static inline const NullableBlock find_first_free_block(const BlockSize size) {
  debug_assert(is_block_size(size));
  debug_assert(is_any_block(first_block));
  debug_assert(is_any_block(last_block));
  debug_assert(blocks_size > 0);

  iterate_blocks(
    block, if (is_free(block) && get_block_size(block) >= size) {
      return into_nullable(block);
    });

  return NULL;
}

static inline const Payload allocate_new_block(const BlockSize size) {
  debug_assert(is_block_size(size));

  const RawBlock raw_block = new_raw_block(size);
  if (raw_block == NULL) {
    return NULL;
  }

  const AllocatedBlock allocated_block =
    initialize_allocated_block(raw_block, size);
  // We call this function if all blocks were allocated, so previous must be
  // allocated.
  const Block block = from_allocated(allocated_block);
  // There are no previous blocks, so previous block is not free - it is
  // allocated.
  set_previous_allocated(block);

  set_last_block(block);

  return get_payload(allocated_block);
}

static inline const AllocatedBlock
allocate_free_block(const FreeBlock free_block) {
  remove_current(free_block);
  const Block block = from_free(free_block);
  set_allocated(block);
  return into_allocated(block);
}

static inline const Payload
allocate_to_extended_last_block(const FreeBlock free_block,
                                const BlockSize size) {
  const Block block = from_free(free_block);
  debug_assert(is_last_block(block));
  // We call this function on first free block, so previous must be allocated.
  debug_assert(is_previous_allocated(block));
  debug_assert(is_block_size(size));

  const BlockSize old_size = get_block_size(block);
  const BlockSize additional_space = size - old_size;

  const RawBlock result = new_raw_block(additional_space);
  if (result == NULL) {
    return NULL;
  }

  const AllocatedBlock allocated_block = allocate_free_block(free_block);
  set_allocated_block_size(allocated_block, size);

  return get_payload(allocated_block);
}

static inline const Payload allocate_with_split(const FreeBlock free_block,
                                                const BlockSize size) {
  const Block block = from_free(free_block);
  // We call this function on first free block, so previous must be allocated.
  debug_assert(is_previous_allocated(block));
  debug_assert(is_block_size(size));

  const BlockSize old_block_size = get_block_size(block);
  const BlockSize empty_block_size = old_block_size - size;
  debug_assert(is_block_size(empty_block_size));

  // Block is too small to split, its size stays the same.
  if (empty_block_size < MINIMUM_BLOCK_SIZE) {
    AnyBlock next = maybe_get_next_block(block);

    if (next != NULL) {
      set_previous_allocated(from_any(next));
    }

    const AllocatedBlock allocated_block = allocate_free_block(free_block);
    return get_payload(allocated_block);
  }

  const RawBlock empty_raw_block = shift_right_block(block, size);

  const FreeBlock empty_free_block =
    initialize_free_block(empty_raw_block, empty_block_size);
  const Block empty_block = from_free(empty_free_block);
  set_previous_allocated(empty_block);

  debug_assert(shift_right(into_raw(block), old_block_size - FOOTER_SIZE) ==
               get_footer(empty_free_block));

  if (is_last_block(block)) {
    set_last_block(empty_block);
  }

  const AllocatedBlock allocated_block = allocate_free_block(free_block);
  set_allocated_block_size(allocated_block, size);

  return get_payload(allocated_block);
}

static inline const Payload allocate(const UnalignedPayloadSize size) {
  debug_assert(size < MAX_HEAP);

  const UnalignedBlockSize unaligned_block_size =
    unaligned_payload_to_block_size(size);
  const BlockSize block_size = round_to_alignment(unaligned_block_size);

  // This is the first allocation.
  if (blocks_size == 0) {
    return allocate_new_block(block_size);
  }

  const NullableBlock nullable_found_block = find_first_free_node(block_size);
  debug(const NullableBlock nullable_found_block_implicit =
          find_first_free_block(block_size););
  if (nullable_found_block == NULL) {
    debug_assert(nullable_found_block_implicit == NULL);
  }

  // Found empty block with sufficient space.
  if (nullable_found_block != NULL) {
    const Block found_block = from_nullable(nullable_found_block);
    const FreeBlock found_free_block = into_free(found_block);
    return allocate_with_split(found_free_block, block_size);
  }

  // Last block is free, but too small.
  if (is_free(last_block)) {
    const FreeBlock free_block = into_free(last_block);
    return allocate_to_extended_last_block(free_block, block_size);
  }

  // Last block was allocated, so we need to allocate a new one.
  return allocate_new_block(block_size);
}

/**
 * Malloc
 */
void *malloc(size_t size) {
  debug(if (verbosity > 1) { debug_trace("malloc %lu", size); });

  void *result = allocate(size);

  debug(check_heap(MALLOC, NULL, size, result););

  return result;
}

static inline const Footer *get_previous_footer(const Block block) {
  debug_assert(is_any_block(block));
  debug_assert(is_previous_free(block));
  debug_assert(!is_first_block(block));
  debug_assert(blocks_size > 0);

  const BoundaryTag *previous_footer = shift_left(into_raw(block), FOOTER_SIZE);

  debug(const BlockSize previous_footer_block_size =
          extract_block_size(*previous_footer));
  debug(Block previous_block =
          from_raw(shift_left_block(block, previous_footer_block_size)));
  debug_assert(is_free_block(previous_block));
  debug_assert(previous_footer_block_size == get_block_size(previous_block));

  return previous_footer;
}

/**
 * Returns previous block. Given block must have free previous block property.
 */
static inline const FreeBlock get_previous_block(const Block block) {
  const BoundaryTag *previous_footer = get_previous_footer(block);
  const BlockSize previous_block_size = extract_block_size(*previous_footer);
  debug_assert(is_block_size(previous_block_size));

  const RawBlock raw_previous_block =
    shift_left_block(block, previous_block_size);
  const Block previous_block = from_raw(raw_previous_block);
  return into_free(previous_block);
}

static inline const AllocatedBlock
get_block_from_payload(const Payload payload) {
  debug_assert(payload != NULL);

  const RawBlock raw_block = shift_left(payload, HEADER_SIZE);
  const Block block = from_raw(raw_block);
  return into_allocated(block);
}

static inline const FreeBlock
deallocate_allocated_block(AllocatedBlock allocated_block) {
  const Block block = from_allocated(allocated_block);
  set_free(block);
  const FreeBlock free_block = into_free(block);
  push_back(free_block);
  return free_block;
}

static inline void deallocate(const Payload payload) {
  const AllocatedBlock allocated_block = get_block_from_payload(payload);
  const Block block = from_allocated(allocated_block);
  BlockSize block_size = get_block_size(block);

  const NullableBlock nullable_next_block = maybe_get_next_block(block);
  if (nullable_next_block != NULL) {
    const Block next_block = from_nullable(nullable_next_block);
    if (is_free(next_block)) {
      remove_current(into_free(next_block));
      block_size += get_block_size(next_block);

      if (is_last_block(next_block)) {
        set_last_block(block);
      }
    } else {
      set_previous_free(next_block);
    }
  }

  if (!is_previous_free(block)) {
    const FreeBlock free_block = deallocate_allocated_block(allocated_block);
    set_free_block_size(free_block, block_size);
    return;
  }

  const FreeBlock free_previous_block = get_previous_block(block);
  const Block previous_block = from_free(free_previous_block);

  block_size += get_block_size(previous_block);

  if (is_last_block(block)) {
    set_last_block(previous_block);
  }

  set_free_block_size(free_previous_block, block_size);
  debug_assert(find_node_with_address(
                 cursor_to_node_address(free_previous_block)) != NULL);
}

/**
 * Free
 */
void free(void *ptr) {
  if (ptr == NULL) {
    return;
  }

  debug(if (verbosity > 1) { debug_trace("free %p", ptr); });

  deallocate(ptr);

  debug(check_heap(FREE, ptr, 0, NULL););
}

static inline void
reallocate_shrink_with_split(const AllocatedBlock allocated_block,
                             const BlockSize old_size, const BlockSize size) {
  debug_assert(is_block_size(old_size));
  debug_assert(is_block_size(size));
  debug_assert(old_size > size);

  const BlockSize empty_block_size = old_size - size;
  debug_assert(is_block_size(empty_block_size));

  // Block is too small to split, so its size stays the same.
  if (empty_block_size < MINIMUM_BLOCK_SIZE) {
    return;
  }

  const Block block = from_allocated(allocated_block);
  const RawBlock empty_raw_block = shift_right_block(block, size);

  const NullableBlock nullable_next = maybe_get_next_block(block);

  set_allocated_block_size(allocated_block, size);

  if (nullable_next == NULL) {
    const FreeBlock empty_free_block =
      initialize_free_block(empty_raw_block, empty_block_size);
    const Block empty_block = from_free(empty_free_block);
    set_previous_allocated(empty_block);
    set_last_block(empty_block);
    return;
  }

  const Block next = from_nullable(nullable_next);
  if (is_allocated(next)) {
    const FreeBlock empty_free_block =
      initialize_free_block(empty_raw_block, empty_block_size);
    const Block empty_block = from_free(empty_free_block);
    set_previous_allocated(empty_block);
    set_previous_free(next);
    return;
  }

  const BlockSize next_block_size = get_block_size(next);
  const FreeBlock empty_free_block =
    initialize_free_block(empty_raw_block, empty_block_size + next_block_size);
  const Block empty_block = from_free(empty_free_block);
  set_previous_allocated(empty_block);

  if (is_last_block(next)) {
    set_last_block(empty_block);
  }
}

static inline void reallocate_extend_with_split(
  const AllocatedBlock allocated_block, const FreeBlock free_next,
  const BlockSize block_size, const BlockSize next_size,
  const BlockSize new_size) {
  debug_assert(is_block_size(block_size));
  debug_assert(is_block_size(next_size));
  debug_assert(is_block_size(new_size));
  debug_assert(block_size + next_size >= new_size);

  const BlockSize empty_block_size = block_size + next_size - new_size;
  debug_assert(is_block_size(empty_block_size));

  const Block block = from_allocated(allocated_block);
  const Block next = from_free(free_next);

  remove_current(free_next);

  // Block is too small to split, so its size stays the same.
  if (empty_block_size < MINIMUM_BLOCK_SIZE) {
    set_allocated_block_size(allocated_block, new_size);

    const NullableBlock nullable_next_next = maybe_get_next_block(next);
    if (nullable_next_next == NULL) {
      set_last_block(block);
      return;
    }

    const Block next_next = from_nullable(nullable_next_next);
    set_previous_allocated(next_next);
    return;
  }

  const RawBlock empty_raw_block = shift_right_block(block, new_size);
  const FreeBlock empty_free_block =
    initialize_free_block(empty_raw_block, empty_block_size);
  const Block empty_block = from_free(empty_free_block);
  set_previous_allocated(empty_block);

  if (is_last_block(next)) {
    set_last_block(empty_block);
  }

  set_allocated_block_size(allocated_block, new_size);
}

static inline const MemoryLocation
reallocate_with_extend(const AllocatedBlock block, const BlockSize old_size,
                       const BlockSize size) {
  debug_assert(is_block_size(old_size));
  debug_assert(is_block_size(size));
  debug_assert(size > old_size);

  const BlockSize additional_space = size - old_size;

  const MemoryLocation result = new_raw_block(additional_space);
  if (result == NULL) {
    return NULL;
  }

  set_allocated_block_size(block, size);

  return result;
}

static inline const Payload reallocate(const Payload old_payload,
                                       const UnalignedPayloadSize size) {
  debug_assert(size < MAX_HEAP);

  const UnalignedBlockSize unaligned_block_size =
    unaligned_payload_to_block_size(size);
  const BlockSize block_size = round_to_alignment(unaligned_block_size);

  const AllocatedBlock allocated_block = get_block_from_payload(old_payload);
  const BlockSize old_block_size = get_allocated_block_size(allocated_block);

  if (block_size == old_block_size) {
    return old_payload;
  }

  if (block_size < old_block_size) {
    reallocate_shrink_with_split(allocated_block, old_block_size, block_size);
    return old_payload;
  }

  const Block block = from_allocated(allocated_block);
  const NullableBlock nullable_next = maybe_get_next_block(block);

  // Reallocated block is the last one.
  if (nullable_next == NULL) {
    debug_assert(is_last_block(block));

    const MemoryLocation result =
      reallocate_with_extend(allocated_block, old_block_size, block_size);
    if (result == NULL) {
      return NULL;
    }

    return old_payload;
  }

  const Block next = from_nullable(nullable_next);
  if (is_free(next)) {
    const FreeBlock free_next = into_free(next);
    const BlockSize next_size = get_block_size(next);

    if (old_block_size + next_size >= block_size) {
      reallocate_extend_with_split(allocated_block, free_next, old_block_size,
                                   next_size, block_size);
      return old_payload;
    }

    // Next free block is too small, so check if it is the last block.
    if (is_last_block(next)) {
      remove_current(free_next);
      const MemoryLocation result = reallocate_with_extend(
        allocated_block, old_block_size + next_size, block_size);
      if (result == NULL) {
        return NULL;
      }

      set_last_block(block);
      return old_payload;
    }
  }

  // Next block is allocated, so we don't have enough space to allocate.

  const Payload payload = allocate(size);

  /* If malloc() fails, the original block is left untouched. */
  if (payload == NULL) {
    return NULL;
  }

  const PayloadSize payload_size = block_to_payload_size(old_block_size);
  /* Copy the old data. */
  memcpy(payload, old_payload, payload_size);

  /* Free the old block. */
  deallocate(old_payload);

  return payload;
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

  debug(if (verbosity > 1) { debug_trace("realloc %p %lu", old_ptr, size); });

  void *result = reallocate(old_ptr, size);

  debug(check_heap(REALLOC, old_ptr, size, result););

  return result;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  const size_t bytes = nmemb * size;
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
  // I prefer to call check heap after an operation.
}
