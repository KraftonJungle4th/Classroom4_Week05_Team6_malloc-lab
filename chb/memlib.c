/*
 * memlib.c - a module that simulates the memory system.  Needed because it 
 *            allows us to interleave calls from the student's malloc package 
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk;  /* points to first byte of heap , 힙 영역의 시작점*/
static char *mem_brk;        /* points to last byte of heap , 힙 영역의 끝점*/
static char *mem_max_addr;   /* largest legal heap address , 가장 큰 합법적인 힙 주소*/ 

/* 
 * mem_init - initialize the memory system model
 */
void mem_init(void)
{
    /* allocate the storage we will use to model the available VM */
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL) {   //MAX_HEAP 크기(20MB)의 메모리 할당, 메모리 시작 주소 mem_start_brk
	fprintf(stderr, "mem_init_vm: malloc error\n"); 
	exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP;  /* max legal heap address ,힙의 최대 주소(시작 주소 + 20MB) 저장  */
    mem_brk = mem_start_brk;                  /* heap is empty initially , 끝 점을 시작 주소로 설정 */ 
}

/* 
 * mem_deinit - free the storage used by the memory system model
   힙 메모리 해제
 */
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
   힙 메모리 리셋. 특정 테스트를 위해 메모리를 초기 상태로 되돌릴 때 호출
 */
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 * 힙 메모리 확장.
 */
void *mem_sbrk(int incr) 
{
    char *old_brk = mem_brk;

    if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) {    //메모리 부족하거나, 요청한 메모리 크기가 허용 범위를 초과
	errno = ENOMEM;
	fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
	return (void *)-1;      //mem_sbrk함수는 포인터를 반환, -1을 캐스팅하여 포인터 타입으로 변환. 메모리 관련 함수들에서 실패를 나타내는 방식. 이 값은 유효한 메모리 주소가 아님
    }

    mem_brk += incr;        //끝점에 incr 더해서 힙 영역 확장
    return (void *)old_brk; //확장 전의 mem_brk를 반환. 새롭게 할당받은 메모리의 시작 주소를 반환하는 것
}

/*
 * mem_heap_lo - return address of the first heap byte
   힙의 시작 주소 반환
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/* 
 * mem_heap_hi - return address of last heap byte
   힙의 마지막 주소 반환
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
   현재 사용중인 힙 메모리의 크기를 바이트 단위로 반환
 */
size_t mem_heapsize() 
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
   시스템의 페이지 크기를 바이트 단위로 반환
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
