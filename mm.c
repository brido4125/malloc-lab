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
#include<semaphore.h>
#include<pthread.h>

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
        "hcs4125@gmail.com",
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
#define CHUNKSIZE (1<<12) // 할당할 Heap의 사이즈
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
static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);
void putFreeBlock(void* bp);
void removeBlock(void* bp);

static char *heap_listp;
static void *free_listp;
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

    heap_listp += (2 * WSIZE);
    free_listp = heap_listp;// 사용할 이중 연결 리스트의 시작점 -> free_listp

    /*
     * extend_heap을 통해 가용 블럭 크기를 늘려줌
     * */
    if (extend_heap(CHUNKSIZE / DSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * Word 단위의 메모리 크기를 인자로 받아 현재 힙의 사이즈를 늘려주는 메서드
 * 기존의 에필로그 block이 새로운 extned_heap을 통해 생기는 가용 블럭의 헤더가 되고
 * 새로운 Epilogue 블럭을 PUT 한다.
 * */
static void *extend_heap(size_t words){
    char *bp;//Block Pointer
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;//Double Word 정책에 따라 짝수 형태로 변환
    bp = mem_sbrk(size);//현재 할당된 블럭의 가장 마지막 주소(힙 영역의 마지막 주소)
    if ((long)bp == -1) {
        return NULL;
    }
    /*
     * 새롭게 할당 받은 가용 block의 header와 footer 설정
     * bp = 새롭게 할당 받은 블럭의 시작 주소
     * */
    PUT(HDRP(bp), PACK(size,0));//기존에 할당된 Epilogue 블럭 초기화
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));//새로운 Epilogue 블럭

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
    void *bp;

    /*
     * ALIGN 과정
     * */
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
    char *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            //first_fit 조건 만족하니 return
            return bp;
        }
    }
    return NULL;
}

static void *best_fit(size_t asize){
    char *bp;
    char *return_bp = NULL;
    size_t min = SIZE_MAX;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
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
        return bp;
    }
    //next가 Free인 경우
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
 * 만일 이미 할당된 메모리 영역에서 크기를 조정할 수 있다면(옆 블럭이 가용블럭 or epilogue) 반환되는 주소는 첫 번째 인자로 전달된 주소와 같다.(현재 아파트의 발코니를 확장하는 경우)
 * 그러나 불가능하다면 기존의 메모리를 해제하고 새로운 영역에 다시 할당한 후, 새로 할당된 메모리의 주소를 반환한다.(새로운 아파트로 이사가는 경우)
 */
void *mm_realloc(void *bp, size_t size)
{
    if (size < 0)
        return NULL;
    else if (size == 0)
    {
        mm_free(bp);
        return NULL;
    }
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE); // 2 words(hd+ft)

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size)
    {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

    // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
    if (!next_alloc && current_size >= new_size)
    {
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        return bp;
    }
    /*
     * realloc할 주소에서 가용 공간이 없기에 새로운 주소로 이사가야 하는 경우
     * */
    else
    {
        void *new_bp = mm_malloc(new_size);
        /*
         * malloc을 통해 받아온 새로운 할당 공간은 place를 하기 전에는 가용 공간 => 그래서 putFreeBlock을 해준뒤, place를 호출해야한다.
         * */
        putFreeBlock(new_bp);
        place(new_bp, new_size);
        memcpy(new_bp, bp, old_size); // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
        mm_free(bp);
        return new_bp;
    }
}

