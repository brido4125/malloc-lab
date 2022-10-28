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
#define WSIZE 4 // Word 사이즈를 4 byte로 할당
#define DSIZE 8 // Double Word 사이즈는 8 byte로 할당
#define CHUNKSIZE (1<<12) // 할당할 Heap의 사이즈 대략 4096 byte(4KB) 정도, 추후 4096으로 변경하고 실험 필요

#define MAX(x,y) ((x)>(y)? (x) : (y))

// or bit 연산으로 헤더 또는 푸터에 들어갈 size의 크기 및 할당 유무 비트 연산
#define PACK(size,alloc) ((size)| (alloc))

//p는 (void*) 포인터이며, 직접 * 연산을 사용할 수 없음
#define GET(p) (*(unsigned int*)(p)) // p라는 주소가 가지고 있는 값(워드)을 리턴
#define PUT(p,val) (*(unsigned int*)(p)=(val)) //p라는 주소가 가지고 있는 값을 val을 대입

// 헤더 또는 푸터의 size 값 리턴
#define GET_SIZE(p) (GET(p) & ~0x7)
// 해당 블럭의 할당 유무 (0 또는 1)를 리턴
#define GET_ALLOC(p) (GET(p) & 0x1)

// 헤더의 포인터(주소) 반환
#define HDRP(bp) ((char*)(bp) - WSIZE)
// 헤더의 포인터(주소) 반환
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//bp에서 현재 블럭의 사이즈를 더하면 다음 블럭의 payload의 시작주소 반환
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
//bp에서 이전 블럭의 사이즈를 배면 이전 블럭의 payload의 시작주소 반환
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

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
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }
    if (size <= DSIZE) {
        asize = 2 * DSIZE;//8byte는 헤더 + 푸터만의 최소 블록 크기이므로, 그 다음 8의 배수인 16바이트로 설정
    }
    //size가 8보다 크다면
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = first_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    //fit 전략이 성공하지 않은 경우, asize 또는 CHUNKSIZE만큼 가용 리스트의 범위를 넓혀준다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void *first_fit(size_t asize){
    //block을 쭉 돌면서 찾아야함
    char *bp;//Prologue 블럭 이후 첫 번째 block
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (((asize) <= GET_SIZE(HDRP(bp))) && GET_ALLOC(HDRP(bp)) != 0) {
            //first_fit 조건 만족하니 return
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    //bp가 find_fit을 통해 얻은 블럭 주소 또는 extend_heap을 통해 얻은 블럭 주소
    //요청한 블록을 가용 블록의 시작 부분에 배치
    size_t current_size = GET_SIZE(HDRP(bp));
    if ((current_size - asize) > 2 * DSIZE) {
        //asize만큼으로 bp의 사이즈를 변경해주었기에 NEXT_BLKP 시 처음 할당 받은 bp 블럭 내의 포인터로 이동한다.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(current_size - asize,0));
        PUT(FTRP(bp), PACK(current_size - asize,0));
    }
    else{
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
    }
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

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
    }
    // prev가 Free인 경우
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    //양쪽 모두 Free인 경우
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
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














