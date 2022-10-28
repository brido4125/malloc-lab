/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "jungle5A",
    /* First member's full name */
    "Brido",
    /* First member's email address */
    "brido@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*MACRO 함수 및 할당기에서 사용할 상수 정의*/
#define WSIZE       4 // Word 사이즈를 4 byte로 할당
#define DSIZE       8 // Double Word 사이즈는 8 byte로 할당
#define CHUNKSIZE   (1<<12) // 할당할 Heap의 사이즈 대략 4096 byte(4KB) 정도, 추후 4096으로 변경하고 실험 필요

#define MAX(x,y) ((x) > (y) ? (x) : (y) //x,y와 중 더 큰 숫자 return

#define PACK(size,alloc) ((size) | (alloc)) // or bit 연산으로 헤더 또는 푸터에 들어갈 size의 크기 및 할당 유무 비트 연산

//p는 (void*) 포인터이며, 직접 * 연산을 사용할 수 없음
#define GET(p) (*(unsigned int*)(p)) // p라는 주소가 가지고 있는 값(워드)을 리턴
#define PUT(p,val) (*(unsigned int*)(p) = (val)) //p라는 주소가 가지고 있는 값을 val을 대입

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 또는 푸터의 size 값 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 해당 블럭의 할당 유무 (0 또는 1)를 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE) // 헤더의 포인터(주소) 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp) - DSIZE) // 헤더의 포인터(주소) 반환

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))//bp에서 현재 블럭의 사이즈를 더하면 다음 블럭의 payload의 시작주소 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))//bp에서 이전 블럭의 사이즈를 배면 이전 블럭의 payload의 시작주소 반환

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp;
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) {
        return -1;
    }
    PUT(heap_listp,0);//Alignment Padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1));//Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1));//Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));//Epilogue Header
    heap_listp += (2 * WSIZE);// DSIZE로 변경 해보기

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;//Block Pointer
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    //long bp = mem_sbrk(size);
    if ((long) (bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0)));
    coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))));

    size_t size = GET_SIZE(HDRP(bp));//현재 블록의 사이즈

    //양쪽 모두 할당된 경우 -> coalescing할 공간이 없다
    if (prev_alloc && next_alloc) {
        return bp;

    }
    // next가 Free인 경우
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp))));
        PUT(FTRP(bp), PACK(size, 0)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














