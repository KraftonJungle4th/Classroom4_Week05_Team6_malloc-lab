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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
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

/* Basic constants and macros */
#define WSIZE   4   /*Word and header/footer size (bytes)*/
#define DSIZE   8   /*Double word size (bytes)*/
#define CHUNKSIZE (1<<12) /*Extend heap by this amount (bytes) 4096 = 4KB*/    

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)   ((size) | (alloc))  //크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴 

/*Read and write a word at address p*/
#define GET(p)      (*(unsigned int *)(p))  //인자 p가 참조하는 워드 읽어서 리턴
#define PUT(p,val)  (*(unsigned int *)(p) = (val))  //인자 p가 가리키는 워드에 val 저장

/*Read the size and allocated fields from address p*/
#define GET_SIZE(p) (GET(p) & ~0x7) //주소 p에 있는 헤더 또는 풋터의 size 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) //주소 p에 있는 헤더 또는 풋터의 할당 비트 리턴

/*Given blovk ptr bp, compute address of its header and footer*/
#define HDRP(bp)    ((char *)(bp) - WSIZE)   //블록 헤더를 가리키는 포인터 리턴
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //블록 풋터를 가리키는 포인터 리턴

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   //다음 블록의 블록 포인터 리턴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   //이전 블록의 블록 포인터 리턴   


static char *heap_listp;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //4워드 빈 가용 리스트 생성
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;

    PUT(heap_listp, 0);     //heap_listp가 가리키는 워드에 0 저장
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); //프롤로그 헤더 8바이트
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); //프롤로그 풋터 8바이트
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //에필로그 블록, 헤더만으로 구성된 크기가 0으로 할당된 블록
    heap_listp += (2*WSIZE);    //프롤로그 블록(힙의 시작점)을 가리킴 -> 힙의 시작 위치 쉽게 알 수 있음

    //힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록 생성(워드 단위로 변환)
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

//힙 메모리 확장
static void *extend_heap(size_t words)  
{
    char *bp;
    size_t size;

    //홀수이면 +1(패딩)을 해서 짝수로 만들고 *WSIZE -> 더블워드경계에 맞추어 할당하기 위해
    size = (words % 2) ? (words +1) * WSIZE : words *WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size ,0));   //free block header
    PUT(FTRP(bp), PACK(size ,0));   //free block footer
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); //새로운 에필로그 헤더

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
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
        return bp;
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
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














