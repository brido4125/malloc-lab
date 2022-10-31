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
#include <stdint.h>

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
#define MINIMUM 16 //Explicit 방식의 블럭에서 필요한 최소 노드의 크기


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

/* Explicit의 Free List 상에서의 이전, 이후의 블럭의 포인터를 리턴 */
# define PRED_FREEP(bp) (*(char**)(bp))
# define SUCC_FREEP(bp) (*(char**)(bp + WSIZE))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *next_fit(size_t asize);
static void *best_fit(size_t asize);
void putFreeBlock(void* bp);
void removeBlock(void* bp);

static char *heap_listp;
static char *free_listp;
/*
 * next_bp 변경지점
 * 1) 처음에 Prologue Block의 heap_listp로 지정
 * 2) fit 될 경우 next_bp 업데이트
 * 3) coalescing 경우에도 next_bp 업데이트
 * */
static char *next_bp;
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /*
     * 6워드 size = 미사용 패딩(1Byte) + Prologue(4byte) + Epilogue(1Byte)
     * 만큼 메모리로부터 가져옴, 실패시 -1 return
     * */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) -1) {
        return -1;
    }
    PUT(heap_listp,0);//Alignment Padding
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM,1));//Prologue Header
    PUT(heap_listp + (2 * WSIZE), NULL); //Prologue Block내의 PREC 포인터 초기값 = NULL
    PUT(heap_listp + (3 * WSIZE), NULL); //Prologue Block내의 PREC 포인터 초기값 = NULL
    PUT(heap_listp + (4 * WSIZE), PACK(MINIMUM,1));//Prologue Footer
    PUT(heap_listp + (5 * WSIZE), PACK(0,1));//Epilogue Header

    heap_listp += (2 * WSIZE);// heap_listp의 초기 주소값 = 시작지점 + 2Word
    free_listp = heap_listp;// 사용할 이중 연결 리스트의 시작점 -> free_listp
    next_bp = heap_listp;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * Word 단위의 메모리 크기를 인자로 받아 현재 힙의 사이즈를 늘려주는 메서드
 * */
static void *extend_heap(size_t words){
    char *bp;//Block Pointer
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;//Double Word 정책에 따라 짝수 형태로 변환
    bp = mem_sbrk(size);//변경 지점
    if ((long)bp == -1) {
        return NULL;
    }
    /*
     * 새롭게 할당 받은 가용 block의 header와 footer 설정
     * bp = 새롭게 할당 받은 블럭의 시작 주소
     * */
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
    asize = ALIGN(size + SIZE_T_SIZE);

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
        if (((asize) <= GET_SIZE(HDRP(bp))) && !GET_ALLOC(HDRP(bp))) {
            //first_fit 조건 만족하니 return
            return bp;
        }
    }
    return NULL;
}

static void *next_fit(size_t asize){
    char *bp;
    /*
     * 최근 지점부터 끝까지 search
     * */
    for (bp = next_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (((asize) <= GET_SIZE(HDRP(bp))) && !GET_ALLOC(HDRP(bp))) {
            next_bp = bp;
            return bp;
        }
    }
    //없으면 처음부터 next_bp 지점까지 search
    for (bp = heap_listp; bp < next_bp; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            next_bp = bp;
            return bp;
        }
    }
    //그래도 없으면 NULL 반환
    return NULL;
}

static void *best_fit(size_t asize){
    char *bp;
    char *return_bp = NULL;
    /*
     * best-fit 전략 : for문 다 돌면서 (currentSize - asize)가 작은 pointer를 리턴
     * */
    size_t min = SIZE_MAX;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (((asize) <= GET_SIZE(HDRP(bp))) && (!GET_ALLOC(HDRP(bp)))) {
            size_t remainSize = GET_SIZE(HDRP(bp)) - asize;
            if (remainSize == 0) {
                return bp;
            }
            if (min > remainSize) {
                min = remainSize;
                return_bp = bp;
            }

        }
    }
    if (return_bp == NULL) {
        return NULL;
    }
    return return_bp;
}

static void place(void *bp, size_t asize){
    //bp가 find_fit을 통해 얻은 블럭 주소 또는 extend_heap을 통해 얻은 블럭 주소
    //요청한 블록을 가용 블록의 시작 부분에 배치
    size_t current_size = GET_SIZE(HDRP(bp));
    removeBlock(bp);
    if ((current_size - asize) > 2 * DSIZE) {
        //asize만큼으로 bp의 사이즈를 변경해주었기에 NEXT_BLKP 시 처음 할당 받은 bp 블럭 내의 포인터로 이동한다.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(current_size - asize,0));
        PUT(FTRP(bp), PACK(current_size - asize,0));
        putFreeBlock(bp);
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
        putFreeBlock(bp);
        return bp;//변경지점
    }
    // next가 Free인 경우
    else if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    // prev가 Free인 경우
    else if (!prev_alloc && next_alloc) {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    //양쪽 모두 Free인 경우
    else{
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp);
    next_bp = bp;
    return bp;
}

void putFreeBlock(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PRED_FREEP(bp) = NULL;
    PRED_FREEP(free_listp) = bp;
    free_listp = bp;
}

void removeBlock(void* bp){
    //free list의 첫번째 블록을 없앨 때
    if (bp == free_listp) {
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    /*
     * 현재 할당 받는 블럭이 리스트의 첫번째 노드가 아닌 경우
     * 할당 될 노드 기준 앞 뒤 노드를 서로 이중 연결 해줘야한다.
     * */
    else{
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














