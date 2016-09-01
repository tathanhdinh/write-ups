;; This function implements the insertion sorting algorithm. The prototype of the
;; function is:
;;     void insertion(unsigned int length, uint64_t array[]);
;;
;; We may notice that once the length of the array is known, we can "hard coded" it
;; into the program using self-modifying code. In some case, it can improve the performance
;; of the algorithm.
;;
;; In the main loop "forLoop" of the algorithm, the counter i is compared with the
;; length of the array (see the comparison at "forLoop"). The value of length will
;;  be written directly as an immediate value of the instruction.

global insertion

section .tetrane alloc exec write

insertion:
  ; get runtime address of insertion
  mov eax, [esp]                ; address of next
  mov edx, eax                  ; backup next
  sub eax, 0x5                  ; address of call instruction
  mov eax, dword [eax+0x1]
  add eax, edx                  ; address of called function

  ;; generate length comparison code
  mov ecx, [esp+0x4]
  cmp ecx, 0x7f
  ja longCompare

  mov word [eax+0x33], 0xfa83
  mov byte [eax+0x35], cl

  jmp storeRegs

longCompare:
  mov word [eax+0x33], 0xfa81
  mov dword [eax+0x35], ecx

storeRegs:
  push ebp
  mov ebp, esp                  ; store base stack frame
  pusha

  mov edx, 0x1                  ; i = 1

forLoop:
  db 0xff, 0x20, 0x90, 0x90, 0x87, 0xcb

  je stop

  mov ecx, edx                  ; j = i

whileLoop:
  test ecx, ecx                 ; j > 0
  jz incrI

  mov esi, dword [ebp+0xc]      ; buf
  lea esi, [esi + ecx * 0x4]
  mov ebx, [esi]                ; buf[j]

  cmp [esi - 0x4], ebx          ; buf[j - 1] > buf[j]
  jbe incrI

  ; swapping by xor
  xor ebx, [esi - 0x4]
  xor [esi - 0x4], ebx
  xor ebx, [esi - 0x4]
  mov [esi], ebx

  dec ecx                       ; j--

  jmp whileLoop

incrI:
  inc edx
  jmp forLoop

stop:
  popa
  leave
  ret
