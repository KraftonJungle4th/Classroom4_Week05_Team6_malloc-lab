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
    "Team6",
    /* First member's full name */
    "최하빈",
    /* First member's email address */
    "chabin7181@gmail.com",
    /* Second member's full name (leave blank if none) */
    "문성준 , 이시현 ",
    /* Second member's email address (leave blank if none) */
    "aaaaa@gmail.com"
};

/*힙 메모리 할당 정책*/
#define NEXT_FIT
//#define FIRST_FIT
//#define BEST_FIT

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE   4   /*Word and header/footer size (bytes)*/
#define DSIZE   8   /*Double word size (bytes)*/
#define CHUNKSIZE (1<<12) /*힙 확장을 위한 기본 크기(=초기 빈 블록의 크기) 4096 = 4KB*/    

/*매크로*/
#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))  //크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴 

#define GET(p)      (*(unsigned int *)(p))  //인자 p가 참조하는 워드 읽어서 리턴
#define PUT(p,val)  (*(unsigned int *)(p) = (val))  //인자 p가 가리키는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7) //주소 p에 있는 헤더 또는 풋터의 size 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) //주소 p에 있는 헤더 또는 풋터의 할당 비트 리턴

#define HDRP(bp)    ((char *)(bp) - WSIZE)   //블록 헤더를 가리키는 포인터 리턴
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //블록 풋터를 가리키는 포인터 리턴

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   //다음 블록의 블록 포인터 리턴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   //이전 블록의 블록 포인터 리턴   

static void *heap_listp;
static void *last_bp;   //next fit

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init : 메모리 할당자를 초기화한다.
 */ 
int mm_init(void)
{
    //4워드 빈 가용 리스트 만들 수 있도록 초기화
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;

    PUT(heap_listp, 0);     //정렬 패딩(unused)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); //프롤로그 헤더 8바이트
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); //프롤로그 풋터 8바이트
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //에필로그 블록, 헤더만으로 구성된 크기가 0으로 할당된 블록
    heap_listp += (2*WSIZE);    //프롤로그 블록(힙의 시작점)을 가리킴 -> 힙의 시작 위치 쉽게 알 수 있음

    //힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록 생성(힙 확장) (워드 단위로 변환)
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    last_bp = heap_listp;       //next_fit에서 사용하기 위해 초기 포인터 위치를 넣어준다.
    return 0;
}

/*
 * extend_heap : 힙의 크기를 확장하여 추가적인 메모리 블록을 할당한다.
 */ 
static void *extend_heap(size_t words)  
{
    char *bp;       
    size_t size;

    //홀수이면 +1(패딩)을 해서 짝수(8byte)의 메모리만 할당(반올림) -> 더블 워드 정렬 제한 조건 적용!
    size = (words % 2) ? (words +1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)   //이전 brk(epilogue block 뒤 포인터) 반환
        return NULL;

    PUT(HDRP(bp), PACK(size ,0));   //size만큼의 가용 블럭 헤더 생성
    PUT(FTRP(bp), PACK(size ,0));   //size만큼의 가용 블록 푸터 생성
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); //새로운 에필로그 헤더 생성

    return coalesce(bp);    //이전 힙이 가용 블록이라면 연결 수행
}

/*
 * mm_malloc : 요청한 크기의 메모리 블록을 할당하여 사용자에게 반환한다.
 */ 
void *mm_malloc(size_t size)
{
    size_t asize;     /*조정된 블록 사이즈*/
    size_t extendsize;  /*적합하지 않은 경우, 힙 확장할 사이즈*/
    char *bp;

    if(size == 0)
        return NULL;

    //더블 워드 정렬 제한 조건 만족 위해 더블 워드 단위로 크기 설정
    if(size <= DSIZE)
        asize = 2*DSIZE;    //최소 블록 크기 16바이트 할당(헤더 4 + 푸터 4 + 저장공간 8)
    else    
        asize = ALIGN(size + DSIZE); //8배수로 올림 처리

    //적절한 가용 블록 검색
    if ((bp = find_fit(asize)) !=NULL)
    {
        place(bp,asize);
        last_bp = bp;
        return bp;  //새롭게 할당한 블록 리턴
    }

    //적합한 블록이 없을 경우 힙 확장
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    place(bp,asize);
    last_bp = bp;
    return bp;
}

/*
 * mm_free : 사용자가 할당한 메모리 블록을 해제한다. 
             할당된 블록을 가용 블록 리스트에 추가하여 나중에 재사용할 수 있게 한다.
 */ 
void mm_free(void *bp)      
{
    size_t size = GET_SIZE(HDRP(bp));       //반환하려는 블록의 사이즈

    PUT(HDRP(bp), PACK(size, 0));           //헤더의 할당 비트를 0으로 설정
    PUT(FTRP(bp), PACK(size, 0));           //푸터의 할당 비트를 0으로 설정
    coalesce(bp);       //인접 가용 블록들에 대한 연결 수행
}

/*
 * place : 할당 요청된 메모리 블록을 할당하고, 필요한 경우 블록을 분할한다.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));      //현재 블록의 크기

    if((csize - asize) >= (2*DSIZE))        //차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize,1));       //현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        last_bp = bp;               //next-fit을 위해 분할 이후 그 다음 블록 지정
        PUT(HDRP(bp), PACK(csize-asize, 0));    //남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else
    {
        PUT(HDRP(bp),PACK(csize,1));        //해당 블록 전부 사용
        PUT(FTRP(bp),PACK(csize,1));    
        last_bp = NEXT_BLKP(bp);    //next-fit을 위해 분할 이후 그 다음 블록 지정
    }
}

/*
 * coalesce: 할당되지 않은 블록 주변의 빈 공간을 병합한다. 경계 태그 합치기
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 할당 상태 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 할당 상태 저장
    size_t size = GET_SIZE(HDRP(bp));   //현재 블록 사이즈

    if (prev_alloc && next_alloc)                   /*Case 1 이전 다음 모두 할당*/
    {
        last_bp = bp;
        return bp;
    }    

    else if(prev_alloc && !next_alloc){             /*Case 2 이전 할당 & 다음 가용*/
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if(!prev_alloc && next_alloc){             /*Case 3 이전 가용 & 다음 할당*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    else{                                           /*Case 4 이전 가용 & 다음 가용*/
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    //last_bp가 속해있는 블록이 이전 블록과 합쳐진다면
    //last_bp에 해당하는 블록을 찾아갈 수 없으므로
    //새로 last_bp를 이전 블록 위치로 지정
    last_bp = bp; 
    return bp;
}

/*
 * First Fit: 가용 블록 리스트에서 처음으로 적합한 블록을 찾는다.
 */
#if defined(FIRST_FIT)
static void *find_fit(size_t asize)
{
    /*first fit*/
    void *bp;

    //에필로그 블록의 헤더를 0으로 넣어줬으므로 에필로그 블록을 만날 때까지 탐색을 진행한다.
    for(bp = heap_listp; GET_SIZE(HDRP(bp))> 0; bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))   
            return bp;
    }
    return NULL;

}

/*
 * Next Fit: 마지막으로 할당된 블록에서부터 가용 블록을 찾는다.
 */
#elif defined(NEXT_FIT)
static void *find_fit(size_t asize)
{
    void *bp = last_bp;

    //next_fit 포인터에서 탐색 시작
    for(bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp))> 0; bp =NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_bp = bp;
            return bp;
        }
    }

    //끝까지 갔는데 할당가능한 free block이 없으면 다시 처음부터 last_bp전까지 탐색
    bp = heap_listp;
    while(bp <last_bp)
    {
        bp = NEXT_BLKP(bp);
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}

/*
 * Best Fit: 가용 블록 리스트에서 가장 작은 적합한 블록을 찾는다.
 */
#elif defined(BEST_FIT)
static void *find_fit(size_t asize)
{
    void *bp;
    void *best_fit = NULL;  //가장 적합한 블록 포인터

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {   
            // best_fit이 NULL이거나 현재 검사 중인 bp의 크기가 이전에 찾은 best_fit의 크기보다 작을 때
            if(!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit)))
                best_fit = bp;
        }
    }
    return best_fit;
}
#endif

/*
 * mm_realloc - 가용 블록을 새로운 크기로 재할당한다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; //이전 포인터
    void *newptr;   //새로 메모리 할당 포인터

    size_t originsize = GET_SIZE(HDRP(oldptr)); // 원본 사이즈
    size_t newsize = size + DSIZE;      // 새 사이즈 + (헤더와 푸터 고려)
    
    // newsize가 더 작은 경우
    if (newsize <= originsize) {
        return oldptr;      //기존 메모리 블록 반환 (크기 줄일 필요 없음)
    }
    else {
        // 연속된 블록이 비어있고, 새로운 메모리 블록의 크기가 연속된 블록의 크기보다 작거나 같으면
        // 이전 메모리 블록의 사이즈를 새로운 크기로 설정해준다.
        size_t addSize = originsize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));    
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newsize <= addSize)) 
        {
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

/* 개선된 mm_realloc - 새로 크기를 조정하려는 블록의 다음 블록이 가용 블록이라면 새로 메모리 할당 안해줘도 된다.
                    - 단순히 헤더, 푸터의 사이즈 정보만 갱신해준다.
-----------------------------------------------------------------------------------------------------------*/
/* 기존 mm_realloc - 무조건 새로운 메모리를 할당한 뒤, 데이터를 복사하는 방식
                    -> 반복적인 메모리 할당으로 코드의 효율성이 떨어짐 */

// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;     // 주어진 포인터를 oldptr에 복사.
//     void *newptr;           // 새로운 메모리 블록을 가리킬 포인터
//     size_t copySize;        // 데이터를 복사할 크기

//     /* 새 블록에 할당*/
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//         return NULL;

//     /* 데이터 복사 */
//     copySize =GET_SIZE(HDRP(oldptr));   
//     if (size < copySize)            
//         copySize = size;             

//     memcpy(newptr, oldptr, copySize);   //새 블록으로 데이터 복사 (복사될 대상 메모리 시작 주소, 복사할 원본 메모리 영역 시작 주소, 복사할 사이즈)
//     mm_free(oldptr);            //이전 메모리 블록 해제

//     return newptr;  //새로운 메모리 블록 포인터 반환
// }
