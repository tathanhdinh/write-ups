; This is a direct implementation of the insertion sorting algorithm.

; auto insertion(unsigned int length, int buf[]) -> void
; {
;   for (unsigned int i = 1; i < length; ++i) {
;     auto j = i;
;     while (j > 0 && buf[j - 1] > buf[j]) {
;       auto tmp = buf[j]; buf[j] = buf[j - 1]; buf[j - 1] = tmp;
;      j--;
;     }
;   }
; }


global insertion

section .tetrane alloc exec write

insertion:
  sub rsp, 0x18
  mov qword [rsp], 0x1

forLoop:
  cmp [rsp], rdi                ; i < length
  je stop

  mov rax, qword [rsp]
  mov qword [rsp + 0x8], rax    ; j = i

whileLoop:
  test rax, rax                 ; j > 0
  jz incrI

  ; mov rdx, [rsp + 0x8]
  lea rax, [rsi + rax * 0x8]
  mov rdx, [rax]                ; tmp = buf[j]

  cmp [rax - 0x8], rdx          ; buf[j - 1] > buf[j]
  jbe incrI

  mov rcx, [rax - 0x8]
  mov [rax], rcx                ; buf[j] = buf[j - 1]
  mov [rax - 0x8], rdx          ; buf[j - 1] = tmp

  dec qword [rsp + 0x8]         ; j--
  mov rax, [rsp + 0x8]

  jmp whileLoop

incrI:
  inc qword [rsp]
  jmp forLoop

stop:
  add rsp, 0x18
  ret
