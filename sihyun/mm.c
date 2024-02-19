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
    // 빈 힙을 만들기
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

    // 빈 힙을 CHUNKSIZE 바이트(12 바이트)로 확장하기
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
        return bp;
    }

    // 맞는 크기가 있는 가용 블록이 없으면, 힙을 확장하고 가용 블록을 할당
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
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
    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    /* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    /* 데이터 복사 */
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

    /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
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

// static void *find_fit(size_t asize)
// {
//     // first-fit search
//     void *bp;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//             return bp;
//     }
//     return NULL;     // no fit
// }

static void *find_fit(size_t asize)
{
    // next-fit search
    void *bp;

    // last_bp가 설정되지 않았거나 유효하지 않은 경우, 힙의 시작부터 검색 시작
    if (last_bp == NULL || GET_SIZE(HDRP(last_bp)) == 0) {
        last_bp = heap_listp;
    }
    for (bp=last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    
    return NULL;     // no fit
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        last_bp = bp;
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK((csize - asize), 0));
        
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
        last_bp = bp;
    }
}