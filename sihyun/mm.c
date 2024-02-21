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

// bp는 항상 블록의 페이로드를 가리키고 있다.
// 가상메모리는 초기에 20MB로 할당된다. 그 안에서 힙을 얼마나 이용할지는 테스트에 따라 달라진다.

// 워드(4 byte) 혹은 더블 워드(8 byte) 정렬 선택하기
#define ALIGNMENT 8

// 정렬하고자 하는 단위의 배수와 가장 가까운 만큼 정렬 (ex 23 -> 24)
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// 상수 정의
#define WSIZE 4                             // 워드와 헤더, 푸터 크기(바이트 단위)
#define DSIZE 8                             // 더블 워드 크기 (바이트 단위)
#define CHUNKSIZE (1<<12)                   // 2^12(4096 byte) 크기로 힙 확장

// 메모리 할당 정책 - 주석 해제하여 사용할 수 있음
// #define FIRST_FIT
#define NEXT_FIT
// #define BEST_FIT

// explicit, implicit free list - 주석 해제하여 사용 가능
#define EXPLICIT
// #define IMPLICIT

// 힙에 사용될 매크로
#define MAX(x, y) (x > y ? x : y)
#define PACK(size, alloc) (size | alloc)          // 사이즈와 할당된 비트를 워드로 패킹
#define GET(p) (*(unsigned int *)(p))             // 주소 p가 참조하는 워드 반환
#define PUT(p, val) (*(unsigned int *)(p) = val)  // 주소 p가 참조하는 워드에 값(val) 저장
#define GET_SIZE(p) (GET(p) & ~0x7)               // 주소 p가 참조하는 워드의 사이즈 읽어오기 - 블록의 크기 반환
#define GET_ALLOC(p) (GET(p) & 0x1)               // 주소 p가 참조하는 워드의 할당여부 읽어오기 - 블록의 할당 여부 반환
#define HDRP(bp) ((char*)(bp) - WSIZE)            // 주어진 bp(블록포인터)를 통해 그 블록의 헤더 주소를 계산 - 블록의 헤더의 포인터
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 주어진 bp(블록포인터)를 통해 그 블록의 푸터 주소를 계산 - 블록의 푸터의 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 주어진 bp(블록포인터)를 통해 이전과 다음 블록의 주소를 계산 - bp 블록의 다음 블록
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 주어진 bp(블록포인터)를 통해 이전과 다음 블록의 주소를 계산

// explicit free list를 위한 매크로
#define GET_PRED(bp) (*(void **)((char *)(bp)))         // 현재 블록의 이전 가용 블록의 주소
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 현재 블록의 다음 가용 블록의 주소 

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void splice_free_block(void *bp);
static void add_free_block(void *bp);

static char *last_bp;               // next_fit을 위한 last_bp 포인터 선언
static char *heap_listp;            // implicit free list에서의 mem_init() 이후의 초기 힙의 위치를 가리키는 포인터 선언
static char *free_listp;            // explicit free list에서의 mem_init() 이후의 초기 힙의 위치를 가리키는 포인터 선언

#if defined IMPLICIT         // 전처리 사용하여 implicit, explicit 사용 가능
int mm_init(void)
{
    heap_listp = mem_sbrk(4*WSIZE);               // 힙을 위한 공간(16 byte)을 가상메모리에 만듦
    if ((heap_listp == (void *) -1))              // 만약 힙을 만들지 못하였다면 heap_listp에 -1이 저장되므로, 힙을 만들지 못하였다는 의미의 -1 반환
        return -1;
    PUT(heap_listp, 0);                           // 힙 초기 포인터가 가리키는 위치 즉, 힙의 가장 맨 처음에 0 저장 - 16 byte 힙의 맨 처음 4 byte는 사용하지 않음을 의미
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  // 힙 초기 포인터가 가리키는 위치 + 1워드(4 byte) 만큼 간 위치에 프롤로그 헤더(더블 워드, 8 byte 크기만큼) 설정
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // 힙 초기 포인터가 가리키는 위치 + 2워드(8 byte) 만큼 간 위치에 프롤로그 푸터(더블 워드, 8 byte 크기만큼) 설정
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));      // 힙 초기 포인터가 가리키는 위치 + 3워드(12 byte) 만큼 간 위치에 에필로그 헤더(크기는 0) 설정
    heap_listp += (2*WSIZE);                      // 힙 초기 포인터를 프롤로그 푸터의 위치(프롤로그 블록에 페이로드가 있다면 프롤로그 블록의 페이로드의 위치)로 옮겨 갱신
    last_bp = heap_listp;                         // next-fit을 위한 last_bp 포인터를 힙의 처음으로 바라보게 함(초기화)

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)     // 빈 힙을 CHUNKSIZE 바이트(4096 바이트)로 확장 - 가용 블록을 프롤로그 블록과 에필로그 블록 사이에 생성
        return -1;
    return 0;
}

#elif defined EXPLICIT                                   // EXPLICIT FREE LIST 일 경우의 mm_init
int mm_init(void)
{
    if ((free_listp = mem_sbrk(8 *WSIZE))==(void*)-1)    // free_list 포인터는 가상메모리 최초 설정 후 힙의 첫 주소를 가리킴. 32Byte의 힙 설정
        return -1;                                       // 힙 설정에 실패함을 의미
    PUT(free_listp, 0);                                  // 힙 초기 포인터가 가리키는 위치 즉, 힙의 가장 맨 처음에 0 저장 - 32 byte 힙의 맨 처음 4 byte는 사용하지 않음을 의미
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1));         // 힙 초기 포인터가 가리키는 위치 + 1워드(4 byte) 만큼 간 위치에 프롤로그 헤더(더블 워드, 8 byte 크기만큼) 설정
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1));         // 힙 초기 포인터가 가리키는 위치 + 2워드(8 byte) 만큼 간 위치에 프롤로그 푸터(더블 워드, 8 byte 크기만큼) 설정
    PUT(free_listp + (3*WSIZE), PACK(2*DSIZE, 0));       // 힙 초기 포인터가 가리키는 위치 + 3워드(12 byte) 만큼 간 위치에 가용 블록 헤더(16Byte 크기만큼) 설정
    PUT(free_listp + (4*WSIZE), NULL);                   // 힙 초기 포인터가 가리키는 위치 + 4워드(16 byte) 만큼 간 위치에 NULL 저장(pred가 없으므로 NULL)하여 pred 설정
    PUT(free_listp + (5*WSIZE), NULL);                   // 힙 초기 포인터가 가리키는 위치 + 5워드(20 byte) 만큼 간 위치에 NULL 저장(succ가 없으므로 NULL)하여 succ 설정
    PUT(free_listp + (6*WSIZE), PACK(2*DSIZE, 0));       // 힙 초기 포인터가 가리키는 위치 + 6워드(24 byte) 만큼 간 위치에 가용 블록 헤더(16Byte 크기만큼) 설정
    PUT(free_listp + (7*WSIZE), PACK(0, 1));             // 힙 초기 포인터가 가리키는 위치 + 1워드(4 byte) 만큼 간 위치에 프롤로그 헤더(더블 워드, 8 byte 크기만큼) 설정
    free_listp += 2*DSIZE;                               // implicit에서는 프롤로그 푸터의 위치로 옮겼던 포인터를 첫 번째 가용 블록의 페이로드 부분으로 옮겨 포인터 위치 갱신

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}
#endif

void *mm_malloc(size_t size)
{
    size_t asize;                           // 조정된 블록 사이즈
    size_t extendsize;                      // 만약 맞는 블록이 없으면 힙을 확장하는데, 확장을 얼마나 할 것인가에 대한 크기
    char *bp;

    if (size == 0)                          // 유효하지 않은 사이즈를 무시
        return NULL;

    if (size <= DSIZE)                      // 정렬 조건을 만족하기 위해 블록 사이즈를 조정하는 과정
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {     // free list에서 크기가 맞는 가용 블록 검색 - first, next, best 매크로 설정 가능
        place(bp, asize);                     // find_fit을 통해 찾은 알맞은 위치에 저장할 크기의 블록을 힙에 할당
        last_bp = bp;                         // 할당 이후 last_bp 포인터 갱신
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);       // 맞는 크기가 있는 가용 블록이 없으면, 힙을 확장하고 가용 블록을 할당
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 만약 초기에 설정한 메모리 크기(20MB)보다 넣어야 할 데이터가 크다면, 확장 불가
        return NULL;
    place(bp, asize);                         // 확장된 힙의 처음 부분에 할당하고자 했던 블록 할당
    last_bp = bp;
    return bp;

}

static void *extend_heap(size_t words)       // 힙 확장
{ 
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;      // 정렬을 유지하기 위해 (word * 짝수) 개수 만큼 할당
    if ((long)(bp = mem_sbrk(size)) == -1)                       // 가상메모리의 크기를 넘어가면 확장 불가함
        return NULL;
    
    // 가용 블록의 헤더와 푸터, 에필로그 블록을 초기화
    PUT(HDRP(bp), PACK(size, 0));            // 가용 블록의 헤더
    PUT(FTRP(bp), PACK(size, 0));            // 가용 블록의 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    // 새로운 에필로그 헤더

    return coalesce(bp);                     // 만약 이전 블록이 가용 블록이었으면 통합 수행
}

#if defined IMPLICIT
static void *coalesce(void *bp)                                 // 블록 할당
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));         // 이전 블록의 할당 여부(0, 1)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));         // 다음 블록의 할당 여부(0, 1)
    size_t size = GET_SIZE(HDRP(bp));                           // 현재 주목하고 있는 블록의 사이즈 - 헤더로 포인터를 옮겨 사이즈를 가져옴

    if (prev_alloc && next_alloc) {                             // Case 1 - 해제 하는 순간, 양 옆의 블록이 모두 할당 상태
        return bp;
    }

    else if (prev_alloc && !next_alloc) {                       // Case 2 - 해제 하는 순간, 이전 블록이 할당 상태이고, 다음 블록이 가용 상태
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                  // 통합될 블록의 사이즈 = 해제된 블록의 사이즈 + 다음 볼록의 사이즈
        PUT(HDRP(bp), PACK(size, 0));                           // 해제된 블록의 헤더를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 헤더)
        PUT(FTRP(bp), PACK(size, 0));                           // 해제된 블록의 푸터를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 푸터)
    }

    else if (!prev_alloc && next_alloc) {                       // Case 3 - 해제 하는 순간, 이전 블록이 가용 상태이고, 다음 블록이 할당 상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                  // 통합될 블록의 사이즈 = 해제된 블록의 사이즈 + 이전 볼록의 사이즈
        PUT(FTRP(bp), PACK(size, 0));                           // 헤제된 블록의 푸터를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 푸터)
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                // 해제된 블록의 이전 블록의 헤더를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 헤더)
        bp = PREV_BLKP(bp);                                     // bp를 이전 블록을 가리키게 함 - 그래야 통합된 블록을 가리키게 할 수 있음
    }

    else {                                                      // Case 4 - 해제 하는 순간, 이전과 다음 블록 모두 가용 상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 통합될 블록의 사이즈 = 해제된 블록의 사이즈 + 이전 볼록의 사이즈
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                // 해제된 블록의 이전 블록의 헤더를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 헤더)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                // 해제된 블록의 다음 블록의 푸터를 합쳐진 사이즈 만큼으로 갱신(통합된 가용 블록의 푸터)
        bp = PREV_BLKP(bp);                                     // bp를 이전 블록을 가리키게 함 - 그래야 통합된 블록을 가리키게 할 수 있음
    }

    last_bp = bp;
    return bp;
}
#elif defined EXPLICIT
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 할당 상태 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 할당 상태 저장
    size_t size = GET_SIZE(HDRP(bp));                   //현재 블록 사이즈

    if (prev_alloc && next_alloc)                   /*Case 1 이전 다음 모두 할당*/
    {
        add_free_block(bp);                         //free_list에 추가
        return bp;
    }    

    else if(prev_alloc && !next_alloc){             /*Case 2 이전 할당 & 다음 가용*/
        splice_free_block(NEXT_BLKP(bp));           //가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if(!prev_alloc && next_alloc){             /*Case 3 이전 가용 & 다음 할당*/
        splice_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else{                                           /*Case 4 이전 가용 & 다음 가용*/
        splice_free_block(PREV_BLKP(bp));
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    add_free_block(bp);                             //현재 병합한 가용 블록을 free_list에 추가
    return bp;
}
#endif

// splice_free_block : 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수, LIFO 방식
static void splice_free_block(void *bp)
{
    if (bp == free_listp)                                       // 제거하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        free_listp = GET_SUCC(free_listp);                      // 다음 블록을 리스트의 루트로 변경
        return;
    }
                                                                
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);                      // 이전 블록의 SUCC을 다음 가용 블록의 PRED와 연결
                                            
    if (GET_SUCC(bp) != NULL)                                   // 다음 가용 블록이 있을 경우만 다음 블록의 PRED를 이전 블록으로 변경
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}


// add_free_block : 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수, 할당 블록이 해제되어 가용 상태가 되었을 때 호출
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;    
    if(free_listp != NULL)            
        GET_PRED(free_listp) = bp;  // free_listp였던 블록의 PRED를 추가된 블록으로 연결 
    free_listp = bp;                // 루트를 현재 블록으로 변경
}

void mm_free(void *bp)                                          // 블록 해제
{
    size_t size = GET_SIZE(HDRP(bp));                           // 현재 블록의 크기를 가져옴

    PUT(HDRP(bp), PACK(size, 0));                               // 현재 블록의 헤더를 가용 상태(0)으로 만듦
    PUT(FTRP(bp), PACK(size, 0));                               // 현재 블록의 푸터를 가용 상태(0)으로 만듦
    coalesce(bp);                                               // 해제되었을 때 외부단편화 방지를 위해 블록 통합
}

#if defined IMPLICIT
void *mm_realloc(void *ptr, size_t size)                        // 블록 재할당
{
    void *oldptr = ptr;                                         // 재할당 과정 이전의 포인터를 저장해두기 위해 선언
    void *newptr;                                               // 새로 할당받은 메모리의 포인터 선언

    size_t originsize = GET_SIZE(HDRP(oldptr));                 // 현재 bp가 보고 있는 블록의 크기
    size_t newsize = size + DSIZE;                              // realloc 하고싶은 블록의 크기(헤더, 푸터 포함)
    size_t addSize;                                             // 현재 블록의 크기 + 다음 가용 블록의 크기 - 확장된 크기

    if (newsize <= originsize) {                                // 재할당할 블록의 크기가 현재 블록의 크기보다 작으면 그냥 재할당 하면 됨
        return oldptr;
    }
    else {
        addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));           // 현재 블록의 크기 + 다음 가용 블록의 크기 - 확장된 크기
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize))    // 만약 다음 블록이 가용 상태이고, 재할당할 사이즈가 확장된 크기보다 작을 때

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
            PUT(HDRP(oldptr), PACK(addSize, 1));                            // 기존 블록의 헤더에 확장된 크기만큼 할당
            PUT(FTRP(oldptr), PACK(addSize, 1));                            // 기존 블록의 푸터에 확장된 크기만큼 할당
            return oldptr;                                                  // 기존 블록의 포인터에서 변하지 않음
        }
        else
        {
            newptr = mm_malloc(newsize);                         // 할당하고자 하는 크기로 새롭게 생성된 메모리의 주소를 포인터에 저장
            if (newptr == NULL)                                  // 새로운 메모리 생성이 안되었으면 NULL 반환
                return NULL;
            memcpy(newptr, oldptr, newsize);                     // 재할당된 블록을 가리키는 포인터에 복사할 값을 재할당된 메모리만큼 복사함
            mm_free(oldptr);                                     // 기존 블록 free()
            return newptr;                                       // 새로운 블록 반환
        }
    }
}
#elif defined EXPLICIT
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;                         //이전 포인터
    void *newptr;                               //새로 메모리 할당 포인터

    size_t originsize = GET_SIZE(HDRP(oldptr)); // 원본 사이즈
    size_t newsize = size + DSIZE;              // 새 사이즈 + (헤더와 푸터 고려)
    
    // newsize가 더 작은 경우
    if (newsize <= originsize) {
        return oldptr;                          //기존 메모리 블록 반환 (크기 줄일 필요 없음)
    }
    else {
        // 연속된 블록이 비어있고, 새로운 메모리 블록의 크기가 연속된 블록의 크기보다 작거나 같으면
        // 이전 메모리 블록의 사이즈를 새로운 크기로 설정해준다.
        size_t addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));    
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize)) 
        {
            splice_free_block(NEXT_BLKP(oldptr)); 
            PUT(HDRP(oldptr), PACK(addSize, 1));
            PUT(FTRP(oldptr), PACK(addSize, 1));
            return oldptr;
        }
        else
        {
            newptr = mm_malloc(newsize);    //새로운 메모리 블록 할당
            if (newptr == NULL)
                return NULL;
            memcpy(newptr, oldptr, newsize);    //이전 메모리 블록에서 새로운 메모리 블록으로 데이터를 복사
            mm_free(oldptr);
            return newptr;
        }
    }
}
#endif

// first_fit 구현
#if defined FIRST_FIT
#elif defined IMPLICIT
static void *find_fit(size_t asize)                             
{
    void *bp;                                                   // 탐색을 수행할 bp 선언

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   // first fit이므로 힙의 처음부터 탐색을 수행하고, bp가 에필로그 블록을 만날 때 까지 포인터를 다음 블록으로 옮겨가며 반목
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))      // 만약 탐색한 블록이 가용 상태이고, 할당할 크기가 해당 블록의 크기보다 작으면 찾은 것임
            return bp;
    }
    return NULL;
}

#elif defined EXPLICIT
static void *find_fit(size_t asize)
{
    void *bp = free_listp;

    for(bp = free_listp; bp != NULL; bp = GET_SUCC(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))   
            return bp;
    }
    return NULL;
}
#endif

// next-fit 구현
#if defined NEXT_FIT
#elif defined IMPLICIT
static void *find_fit(size_t asize)
{
    char *bp;                                                                   // 탐색을 위한 bp를 선언

    for (bp = NEXT_BLKP(last_bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   // 마지막 할당된 블록의 다음부터 탐색 수행, 에필로그 블록을 만날 때까지 포인터를 다음 블록으로 옮김
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {            // 만약 탐색한 블록이 가용 상태이고, 할당할 크기가 해당 블록의 크기보다 작으면 찾은 것임
            last_bp = bp;                                                       // 탐색에 성공했으므로 역시 다음 할당할 때를 위해 last_bp 갱신
            return bp;
        }
    }
    for (bp = heap_listp; bp <= last_bp; bp = NEXT_BLKP(bp))                    // 이전의 for문에서 끝까지 탐색했는데 적합한 블록이 나오지 않았을 수 있으므로, 힙의 처음부터 마지막 할당된 블록 전까지 탐색 수행
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}
#endif

// best-fit 구현
#if defined BEST_FIT
#elif defined IMPLICIT
static void *find_fit(size_t asize)
{
    void *bp;                                                                           // 탐색을 위한 포인터 선언                                   
    void *best_bp = NULL;                                                               // 사이즈가 가장 맞는 블록의 포인터를 NULL로 선언
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))                   // first_fit과 마찬가지로 처음에서부터 탐색 시작
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))                      // 만약 탐색한 블록이 가용 상태이고, 할당할 크기가 현재 블록의 크기보다 작으면 찾은 것임
        {
            if (best_bp == NULL || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_bp))) {      // 현재 블록의 크기가 best_bp가 가리키고 있는 블록의 크기보다 작다면 
                best_bp = bp;                                                           // best_bp 갱신 -> best_bp가 NULL이라면(초기화된 상태라면) best_bp가 현재 블록을 가리키게 해야 탐색을 수행할 수 있음
            }
        }
    }
    return best_bp;
}
#endif

#if defined IMPLICIT
static void place(void *bp, size_t asize)                                               // 할당할만한 블록을 찾고 나면, 실제로 할당을 하는 하는 함수
{
    size_t csize = GET_SIZE(HDRP(bp));                                                  // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE))                                                 // 현재 블록과 할당하고 싶은 블록의 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1));                                                  // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        last_bp = bp;
        PUT(HDRP(bp), PACK((csize - asize), 0));                                        // 남은 크기를 다음 블록에 할당하여 가용 블록으로 만듦
        PUT(FTRP(bp), PACK((csize - asize), 0));
        
    }
    else                                                                                // 만약 블록 크기의 차이가 16 이하라면
    {
        PUT(HDRP(bp), PACK(csize, 1));                                                  // 해당 블록 전부 사용하면 됨
        PUT(FTRP(bp), PACK(csize, 1));
        last_bp = NEXT_BLKP(bp);
    }
}

#elif defined EXPLICIT
// place : 할당 요청된 메모리 블록을 할당하고, 필요한 경우 블록을 분할한다.
static void place(void *bp, size_t asize)
{
    splice_free_block(bp);                  //free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp));      //현재 블록의 크기

    if((csize - asize) >= (2*DSIZE))        //차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize,1));       //현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize,1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));    //남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        add_free_block(NEXT_BLKP(bp));      //남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp),PACK(csize,1));        //해당 블록 전부 사용
        PUT(FTRP(bp),PACK(csize,1));    
    }
}

#endif