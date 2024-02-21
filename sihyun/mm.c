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
    "team 6",
    /* First member's full name */
    "Sihyun Lee",
    /* First member's email address */
    " moorow0729@hufs.ac.kr",
    /* Second member's full name (leave blank if none) */
    "SeongJun Moon, Habin Choi",
    /* Second member's email address (leave blank if none) */
    " ",
    /* Third member's full name (leave blank if none) */
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// 상수 정의
#define WSIZE 4                 // 워드와 헤더, 푸터 크기(바이트 단위)
#define DSIZE 8                 // 더블 워드 크기 (바이트 단위)
#define CHUNKSIZE (1<<12)       // 12바이트 크기로 힙 확장
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 메모리 할당 정책
#define FIRST_FIT
// #define NEXT_FIT
//#define BEST_FIT

// 힙에 사용될 매크로
#define MAX(x, y) (x > y ? x : y)
#define PACK(size, alloc) (size | alloc)          // 사이즈와 할당된 비트를 워드로 패킹
#define GET(p) (*(unsigned int *)(p))             // 주소 p에 워드단위로 읽어오기
#define PUT(p, val) (*(unsigned int *)(p) = val)  // 주소 p에 워드단위로 쓰기
#define GET_SIZE(p) (GET(p) & ~0x7)               // 주소 p로부터 사이즈 읽어오기
#define GET_ALLOC(p) (GET(p) & 0x1)               // 주소 p로부터 할당여부 읽어오기
#define HDRP(bp) ((char*)(bp) - WSIZE)            // 주어진 bp(블록포인터)를 통해 그 블록의 헤더 주소를 계산
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 주어진 bp(블록포인터)를 통해 그 블록의 푸터 주소를 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 주어진 bp(블록포인터)를 통해 이전과 다음 블록의 주소를 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 주어진 bp(블록포인터)를 통해 이전과 다음 블록의 주소를 계산

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


char *last_bp;
char *heap_listp;

int mm_init(void)
{
    heap_listp = mem_sbrk(4*WSIZE);
    // 빈 힙을 만들기
    if ((heap_listp == (void *) -1))
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    last_bp = heap_listp;

    // 빈 힙을 CHUNKSIZE 바이트(4096 바이트)로 확장하기
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;       // 조정된 블록 사이즈
    size_t extendsize;  // 만약 맞는 블록이 없으면 힙을 확장하는데, 확장을 얼마나 할 것인가에 대한 크기
    char *bp;

    // 유효하지 않은 사이즈를 무시
    if (size == 0)
        return NULL;

    // 오버헤드와 정렬 조건을 포함하기 위해 블록 사이즈를 조정
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    // free list에서 크기가 맞는 가용 블록 검색
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        last_bp = bp;
        return bp;
    }

    // 맞는 크기가 있는 가용 블록이 없으면, 힙을 확장하고 가용 블록을 할당
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    last_bp = bp;
    return bp;

}

static void *extend_heap(size_t words)
{ 
    char *bp;
    size_t size;

    // 정렬을 유지하기 위해 (word * 짝수) 개수 만큼 할당
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // 가용 블록의 헤더와 풋터, 에필로그 블록을 초기화
    PUT(HDRP(bp), PACK(size, 0));            // 가용 블록의 헤더
    PUT(FTRP(bp), PACK(size, 0));            // 가용 블록의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    // 새로운 에필로그 헤더

    // 만약 이전 블록이 가용 블록이었으면 통합
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // Case 1
        return bp;
    }

    else if (prev_alloc && !next_alloc) { // Case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { // Case 3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else { // Case 4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_bp = bp;
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;

    size_t originsize = GET_SIZE(HDRP(oldptr));    // 현재 bp가 보고 있는 블록의 크기
    size_t newsize = size + DSIZE;                 // realloc 하고싶은 블록의 최소 크기
    size_t addSize;

    if (newsize <= originsize) {
        return oldptr;
    }
    else {
        //realloc 최적화 중
        addSize = originsize + GET_SIZE(FTRP(PREV_BLKP(oldptr)));  // 이전 블록의 크기 + 현재 bp가 보고 있는 블록의 크기
        if (!GET_ALLOC(FTRP(PREV_BLKP(oldptr))) && (newsize <= addSize))
        {
            PUT(HDRP(PREV_BLKP(oldptr)), PACK(addSize, 1));
            PUT(FTRP(PREV_BLKP(oldptr)), PACK(addSize, 1));
            return PREV_BLKP(oldptr);
        }
        addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize))
        {
            PUT(HDRP(oldptr), PACK(addSize, 1));
            PUT(FTRP(oldptr), PACK(addSize, 1));
            return oldptr;
        }
        else
        {
            newptr = mm_malloc(newsize);
            if (newptr == NULL)
                return NULL;
            memmove(newptr, oldptr, newsize);
            mm_free(oldptr);
            return newptr;
        }
    }
}


// first_fit 구현
#if defined(FIRST_FIT)
static void *find_fit(size_t asize)
{
    // first-fit search
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;     // no fit
}

// next-fit 구현
#elif defined(NEXT_FIT)
static void *find_fit(size_t asize)
{
    // next-fit search
    char *bp;

    // last_bp가 설정되지 않았거나 유효하지 않은 경우, 힙의 시작부터 검색 시작
    for (bp = NEXT_BLKP(last_bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    for (bp = heap_listp; bp <= last_bp; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    
    return NULL;     // no fit
}

#elif defined(BEST_FIT)
static void *find_fit(size_t asize)
{
    // best-fit search
    void *bp;
    void *best_bp = NULL;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            if ( best_bp == NULL || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_bp))) {
                best_bp = bp;
            }
        }
    }
    return best_bp;     // no fit
}

#endif

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        last_bp = bp;
        PUT(HDRP(bp), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK((csize - asize), 0));
        
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
        last_bp = NEXT_BLKP(bp);
    }
}