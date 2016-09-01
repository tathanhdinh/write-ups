; This program is a direct implementation of the insertion sorting algorithm.

; auto insertion(unsigned int length, uint64_t buf[]) -> void
;   {
;     for (unsigned int i = 1; i < length; ++i) {
;       auto j = i;
;       while (j > 0 && buf[j - 1] > buf[j]) {
;         auto tmp = buf[j]; buf[j] = buf[j - 1]; buf[j - 1] = tmp;
;        j--;
;       }
;     }
;   }


global insertion

section .tetrane alloc exec write

insertion:
  ; get runtime address of insertion
  mov eax, [esp]                ; address of next
  mov edx, eax                  ; backup next
  sub eax, 0x5                  ; address of call instruction
  mov eax, dword [eax+0x1]
  add eax, edx                  ; address of called function

  push ebp
  mov ebp, esp                  ; store base stack frame
  pusha

  mov edx, 0x1                  ; i = 1

forLoop:
  cmp edx, [ebp+0x8]            ; i < length ?
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
