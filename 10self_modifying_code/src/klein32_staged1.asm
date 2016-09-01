;; This function implements the insertion sorting algorithm. The prototype of the
;; function is:
;;     void insertion(unsigned int length, uint64_t array[]);

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

  mov word [eax+0x36], 0xfa83
  mov byte [eax+0x38], cl

  jmp storeRegs

longCompare:
  mov word [eax+0x36], 0xfa81
  mov dword [eax+0x38], ecx

storeRegs:
  push ebp
  mov ebp, esp                  ; store base stack frame
  pusha

  mov edx, 0x1                  ; i = 1

  add eax, 0x48                 ; now ebx is the address of the next buffer (use add before since the result can affect to flags)

forLoop:
  ;; buffer for length comparison code
  db 0xff, 0x20, 0x90, 0x90, 0x89, 0xf9

  mov bx, [eax]
  mov bh, 0x24
  cmovne bx, [eax]
  mov [eax], bx
  ;; buffer for je stop
  db 0x74, 0x00                 ; je $+0x2

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
