/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include <math.h>
#include "mm.h"
#include "memlib.h"


/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE 4             /* word size (bytes) */
#define DSIZE 8             /* doubleword size (bytes) */
#define CHUNKSIZE (1 << 12) /* initial heap size (bytes) */
#define OVERHEAD 8          /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y)
{
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc)
{
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p)
{
  return *(uint32_t *)p;
}
static inline void PUT(void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE(void *p)
{
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC(void *p)
{
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp)
{
  return ((char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp)
{
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp)
{
  return ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)));
}

static inline void *PREV_BLKP(void *bp)
{
  return ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

int convertSize(int sizeMem)
{
  return ceil(log2(sizeMem));
}

static char *heap_listp; /* pointer to first block */

struct mmMainPointer
{
  struct mmMainPointer *prev;
  struct mmMainPointer *next;
};

static struct mmMainPointer mmMainHelper[32];

static inline void addNewNode(struct mmMainPointer *nodePointer, int sizeMem)
{
  struct mmMainPointer *ptr = &mmMainHelper[convertSize(sizeMem)];
  nodePointer->next = ptr->next;
  nodePointer->prev = ptr;
  ptr->next->prev = nodePointer;
  ptr->next = nodePointer;
}

static inline void reorderFreeListNode(struct mmMainPointer *ptr)
{
  ptr->prev->next = ptr->next;
  ptr->next->prev = ptr->prev;
  ptr->prev = NULL;
  ptr->next = NULL;
}

static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

int mm_init(void)
{
  for (int i = 0; i < 32; i++)
  {
    mmMainHelper[i].next = mmMainHelper[i].prev = &mmMainHelper[i];
  }
  if ((mem_sbrk(4 * WSIZE)) == (void *)-1)
  {
    return -1;
  }

  heap_listp = (mem_sbrk(4 * WSIZE));

  PUT(heap_listp, 0);
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
  heap_listp += (2 * WSIZE);
  return 0;

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
  {
    return -1;
  }

}

static void *extend_heap(uint32_t words)
{

  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

  if ((long)(bp = mem_sbrk(size)) == -1)
  {
    return NULL;
  }
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

  struct mmMainPointer *ptr = ((struct mmMainPointer *)coalesce(bp));
  addNewNode(ptr, size);
  return (void *)ptr;
}

static void *find_fit(uint32_t asize)
{
  struct mmMainPointer *bp;
  for (int size = convertSize(asize); size < 32; size++)
  {
    for (bp = mmMainHelper[size].next; bp != &mmMainHelper[size]; bp = bp->next)
    {
      if (asize <= GET_SIZE(HDRP(bp))) 
      {
        return bp;
      }
    }
  }
  return NULL; 
}

void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  struct mmMainPointer *ptr = ((struct mmMainPointer *)coalesce(bp));
  addNewNode(ptr, size);
}

static void *coalesce(void *bp)
{
  size_t previousAlloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t nextAlloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (nextAlloc  && previousAlloc)
  { 
    return bp;
  }
  else if (!nextAlloc && !previousAlloc)
  {
    reorderFreeListNode((struct mmMainPointer *)PREV_BLKP(bp));
    reorderFreeListNode((struct mmMainPointer *)NEXT_BLKP(bp));
    size += GET_SIZE(FTRP(NEXT_BLKP(bp)))+ GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp); 
  }
  else if (!nextAlloc && previousAlloc)
  {                                                             /* Case 2 */
    reorderFreeListNode((struct mmMainPointer *)NEXT_BLKP(bp)); //explicit
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else
  { 
    reorderFreeListNode((struct mmMainPointer *)PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  return bp;
}

void *mm_malloc(uint32_t size)
{
  size_t asize;
  size_t biggerSize;
  char *bp;

  size = MAX(size, sizeof(struct mmMainPointer));

  if (size == 0)
  {
    return NULL;
  }

  if (size > DSIZE)
  {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  else
  {
    asize = 2 * DSIZE;
  }

  if ((bp = find_fit(asize)) != NULL)
  {
    reorderFreeListNode((struct mmMainPointer *)bp);
    place(bp, asize);
    return bp;
  }

  biggerSize = MAX(asize, CHUNKSIZE);

  if ((bp = extend_heap(biggerSize / WSIZE)) == NULL)
  {
    return NULL;
  }

  reorderFreeListNode((struct mmMainPointer *)bp);
  place(bp, asize);
  return bp;
}

static void place(void *bp, uint32_t asize)
{
  size_t mmSize = GET_SIZE(HDRP(bp));

  int minimum = (sizeof(struct mmMainPointer) + OVERHEAD);

  if ((mmSize - asize) < (minimum))
  {
    PUT(HDRP(bp), PACK(mmSize, 1));
    PUT(FTRP(bp), PACK(mmSize, 1));
  }
  else
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(mmSize - asize, 0));
    PUT(FTRP(bp), PACK(mmSize - asize, 0));
    addNewNode(((struct mmMainPointer *)bp), (mmSize - asize));
  }
}

void *mm_realloc(void *ptr, uint32_t size)
{
  void *newPointer;
  uint32_t cSize;

  int minimum = MAX(size, sizeof(struct mmMainPointer)) + OVERHEAD;
  int sizeBlock = GET_SIZE(HDRP(ptr));

  if (sizeBlock == minimum)
  {
    return ptr;
  }
  if (sizeBlock > minimum)
  {
    place(ptr, sizeBlock);
    return ptr;
  }

  newPointer = mm_malloc(size);
  if (newPointer == NULL)
  {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  cSize = GET_SIZE(HDRP(ptr));

  if (size < cSize)
  {
    cSize = size;
  }
  memcpy(newPointer, ptr, cSize);
  mm_free(ptr);
  return newPointer;
}

void mm_checkheap(int verbose)
{
  void *bp = heap_listp;

  if (verbose)
  {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
  {
    printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
  {
    if (verbose)
    {
      printblock(bp);
    }
    checkblock(bp);
  }

  if (verbose)
  {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
  {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp)
{
  uint32_t nSize, nalloc, jsize, malloc;

  nSize = GET_SIZE(HDRP(bp));
  nalloc = GET_ALLOC(HDRP(bp));
  jsize = GET_SIZE(FTRP(bp));
  malloc = GET_ALLOC(FTRP(bp));

  if (nSize == 0)
  {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
         bp,
         (int)nSize, (nalloc ? 'a' : 'f'),
         (int)jsize, (malloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
  if ((uintptr_t)bp % 8)
  {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
  {
    printf("Error: header does not match footer\n");
  }
}