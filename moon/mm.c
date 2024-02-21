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
    "4-6Team",
    /* First member's full name */
    "SungJun",
    /* First member's email address */
    "ansdj3523@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Habin, ",
    /* Third member's full name (leave blank if none) */
    "SiHyun"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// 할당할 크기 체크
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define WSIZE 4             // 워드 크기
#define DSIZE 8             // 더블 워드 크기
#define CHUNKSIZE (1<<12)   // 초기 힙 크기나 힙이 부족할 때 늘어날 힙 크기 2의12승 -> 4KB

#define MAX(x, y) ((x) > (y) ? (x) : (y))   // x, y 두 값중 더 큰 값 반환
#define PACK(size, alloc) ((size) | (alloc))    // 주소값을 위해 비트연산

#define GET(p)      (*(unsigned int *)(p))          // 주어진 포인터 위치의 워드를 읽는 GET()
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주어진 포인터 위치에 워드를 쓰는 PUT()

#define GET_SIZE(p)     (GET(p) & ~0x7) // 주어진 포인터 위치의 헤더에서 블록 크기를 읽는 GET_SIZE(), ~는 역수 따라서 11111000이 된다.
#define GET_ALLOC(p)    (GET(p) & 0x1)  // 주어진 포인터 위치의 헤더에서 할당 여부를 읽는 GET_ALLOC(), 00000001이 된다.

#define HDRP(bp) ((char *)(bp) - WSIZE) // 현재 블록포인터에서 헤더주소를 계산(한 블록 뒤로 후진)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 현재 블록포인터에서 푸터주소를 계산 (메모리 크기만큼 앞으로 전진하고 두 블록 뒤로 후진)

// 현재 블록포인터에서 다음 블록 주소 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // bp에서 해당 블록크기만큼 이동 후 뒤로 한칸
// 현재 블록포인터에서 이전 블록 주소 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 푸터로 가면 크기를 알 수 있으니 이전의 푸터로 이동

// #define first_fit
// #define next_fit
#define best_fit

// 메모리 할당에 사용할 함수들 선언
static void *heap_listp;
static char *last_bp;
static char *check_bp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
//초기 힙 영역 할당
int mm_init(void)
{
    // char *heap_listp; // 힙의 시작 주소 선언
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) // 힙에 16바이트의 공간 할당
        return -1; // 실패하면 -1 반환
    PUT(heap_listp, 0); // 블록 생성 시 패딩한 첫 시작부분
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 8바이트짜리 프롤로그헤더 생성
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 8바이트짜리 프롤로그푸터 생성
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 헤더를 생성 후 뒤로 밀리는 형태
    heap_listp += (2 * WSIZE); // 프롤로그헤더와 푸터 사이로 포인터 옮기기

    last_bp = heap_listp;

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) // extend heap을 통해 힙을 확장해준다.
        return -1;
    return 0;
}

// 힙의 메모리를 확장
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

    // 크기가 홀수면 +1 추가, 8의 배수를 맞추기 위함
    // 크기가 짝수면 그대로 연산
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if((long)(bp = mem_sbrk(size)) == -1) // 
		return NULL;

	PUT(HDRP(bp), PACK(size, 0)); // Free block header, regular block 첫 부분
	PUT(FTRP(bp), PACK(size, 0)); // Free block footer, regular block 마지막 부분
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header, 블록을 추가했으니 에필로그헤더를 새롭게 위치 조정
    // bp에서 헤더에서 읽은 크기만큼 이동하고 한칸 가면 된다.

	return coalesce(bp); // 이전 블록이 free라면 함수 실행, 함수 재사용을 위해 리턴값 선언
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// 가용 리스트에서 블록할당하기
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 크기 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 크기변수
    char *bp;

    if(size == 0) // 인자로 받은 size가 0이면 NULL 반환
        return NULL;

    if(size <= DSIZE) // 크기가 더블워드보다 작으면
        asize = 2 * DSIZE; // 헤더와 푸터를 포함해서 블록 사이즈를 재조정해야 하기 때문에 더블워드의 2배를 한다.
    else // 더블워드보다 크면
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 8의 배수로 되도록 만들어야 한다.

    if((bp = find_fit(asize)) != NULL) // find_fit한 값이 있다면
    {
        place(bp, asize);
        return bp; // place를 거친 블록의 위치를 반환
    }

    extendsize = MAX(asize, CHUNKSIZE); // 요청된 크기와 초기 힙 크기 중에 더 큰 값 넣기
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) // 워드크기만큼 나눠서 힙 공간 추가 요청
        return NULL; // 실패 시 NULL 반환

    place(bp, asize); // 확장된 상태에서 asize를 넣기
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
// 메모리 할당 해제
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 현재블록의 헤더에서 크기를 받는다.

    PUT(HDRP(bp), PACK(size, 0)); // 헤더를 가용상태로 만든다
    PUT(FTRP(bp), PACK(size, 0)); // 푸터를 가용상태로 만들기

    coalesce(bp);// 이전 블록이 free라면 함수 실행, 함수 재사용을 위해 리턴값 선언
}

// 가용블록 합치는 함수
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록에서 블록의 가용여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록에서 블록의 가용여부 확인
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if(prev_alloc && next_alloc) // case 1) 이전블록과 다음블록이 둘다 할당되어있을 때, 현재블록의 상태는 할당에서 가용으로 변경
    {
        return bp; // 이미 free에서 가용이 되어있으니 따로 free할 필요는 없다.
    }

    else if(prev_alloc && !next_alloc) // case 2) 이전블록은 할당되고, 다음블록은 가용상태일 때, 현재블록은 다음블록과 통합된다.
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음블록의 헤더를 확인해 블록크기만큼 size에 추가한다.
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
    }

    else if(!prev_alloc && next_alloc) // case 3) 이전블록은 가용상태이고 다음블록은 할당되있을 때, 이전블록은 현재블록과 통합된다.
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전블록의 헤더를 확인해 블록크기만큼 size에 추가한다.
        PUT(FTRP(bp), PACK(size, 0)); // 푸터에 조정할 크기로 상태를 바꾼다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 헤더에서 앞블록의 헤더위치로 이동 후 조정한 size 넣기
        bp = PREV_BLKP(bp); // 앞 블록의 헤더로 이동
    }

    else // case 4) 이전블록과 다음블록이 둘다 가용상태일 때, 이전, 현재, 다음 3개 블록을 전부 가용블록으로 통합
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전블록헤더와 다음블록푸터까지로 size를 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전블록의 헤더로 가서 size를 넣는다.
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음블록의 푸터로 가서 size를 넣는다.
        bp = PREV_BLKP(bp); // 이전블록으로 bp를 이동
    }

    last_bp = bp;
    return bp; // 4개 case 중 적용된 값으로 반환
}

static void *find_fit(size_t asize)
{
// first fit
#if defined(first_fit)
    void *bp = mem_heap_lo() + (2 * WSIZE); // 사용가능한 블록주소 계산
    while(GET_SIZE(HDRP(bp)) > 0) // 힙의 모든 블록 순회
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 헤더블록이 할당되지 않았고 그 크기가 요청된 크기보다 크면
            return bp; // 블록의 주소 반환
        
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
    }
    return NULL; // 전부 검사했을 때 조건을 충족하지 않으면 NULL 반환
// next fit
#elif defined(next_fit)
    void *bp;
    for (bp = last_bp; GET_SIZE(HDRP(bp))>0 ; bp = NEXT_BLKP(bp)) // last_bp에서 시작해서 에필로그블록이 보일때까지 반복
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && asize <= GET_SIZE(HDRP(bp))) // 가용상태이고 요청한 크기보다 크거나 같으면
        {
            last_bp = bp; // last_bp를 현재 bp로 업데이트 후 반환
            return bp;
        }
    }
    // 만약 끝까지 갔을 때 가용블럭이 없다면 맨 앞부터 다시 시작
    // 코드는 위와 동일
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
#elif defined(best_fit)
    void *bp = mem_heap_lo() + (2 * WSIZE);// 사용가능한 블록주소 계산
    void *check_size = NULL; // 효율이 좋은 블록주소를 저장

    if(asize == NULL) return NULL; // 요청한게 없으면 NULL 리턴
    while(GET_SIZE(HDRP(bp)) > 0) // 에필로그블록까지 돌면서
    {
        // 가용블록이고 요청크기보다 크거나 같을 때
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            // 첫 블록이거나 현재 크기와 저장해논 크기를 비교해 현재 크기가 더 작으면
            if(!check_size || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(check_size)))
                check_size = bp; // 변수에 현재 블록 담기
        }
        
        bp = NEXT_BLKP(bp); // 다음 블록 이동
    }
    return check_size; // 전부 돌고 효율이 제일 좋은 블록 주소값 반환
#endif
}

// 분할하는 함수
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재블록의 크기

    if((csize - asize) >= (2 * DSIZE)) // 현재블록과 요청한 블록의 크기를 합해도 공간이 남아 가용블록을 만들 수 있는지 확인인
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재블록의 헤더에 요청한 크기와 할당여부를 저장한다.
        PUT(FTRP(bp), PACK(asize, 1)); // 현재블록의 푸터에 요청한 크기와 할당여부를 저장한다.

        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize-asize, 0)); // 블록할당 후 남은 공간에 새로운 가용블록 할당가능한걸 헤더에 표시
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize-asize, 0)); // 블록할당 후 남은 공간에 새로운 가용블록 할당가능한걸 푸터에 표시
    }
    else // 저장공간이 부족하면
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 현재 블록을 할당한다.
        PUT(FTRP(bp), PACK(csize, 1)); // 현재 블록을 할당한다.
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 메모리 재할당을 위한 함수
void *mm_realloc(void *ptr, size_t size)
{
    if(ptr == NULL) // 메모리를 처음 할당하는 경우에는
        return mm_malloc(size); // 인자로 받아온 크기의 메모리를 할당 후 반환

    if(size <= 0) // 메모리를 해제하는 경우에는
    {
        mm_free(ptr); // free함수로 메모리를 해제하고 0 반환
        return 0;
    }

    void *newptr = mm_malloc(size); // 새 메모리블록을 할당한다.
    if(newptr == NULL) // 새 메모리블록 할당에 실패하면 NULL 반환
        return NULL;

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // 현재블록 크기에서 더블워드를 뺀 값이 복사할 크기
    if(size < copySize) // 요청한 크기가 복사할 크기보다 작으면 복사값을 요청값으로 줄인다.
        copySize = size;

    memcpy(newptr, ptr, copySize); // ptr이 가리키는 메모리에서 newptr이 가리키는 메모리로 복사한크기만큼의 데이터를 복사한다.
    mm_free(ptr);  // 기존에 할당되었던 메모리블록을 해제
    return newptr; // 새로 할당받은 메모리 블록의 주소 반환
}