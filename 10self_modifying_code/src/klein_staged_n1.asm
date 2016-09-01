global insertion

section .tetrane alloc exec write

insertion:
  mov r11, 0x1                  ; i = 1

  ; concretize length
  mov byte [rel forLoop + 3], dil
  mov eax, [rel forLoop + 3]
  cmp edi, 0x7f
  cmovg eax, edi
  mov [rel forLoop + 3], eax

forLoop:
  cmp r11, 0x0
  mov rax, rax                  ; a buffer of 3 bytes in case of edi is greater than 0x7f

  mov eax, 0xda894d90
  mov ecx, 0xc03148c3
  cmove eax, ecx
  mov [rel $ + 6], eax

  resb 4                        ; a buffer of 4 bytes to write code

whileLoop:
  test r10, r10                 ; j > 0?
  jz incrI

  lea rax, [rsi + r10 * 0x8]
  mov r9, [rax]                 ; tmp = buf[j]

  cmp [rax - 0x8], r9           ; buf[j - 1] > buf[j]?
  mov cx, 0x1076
  mov r8w, 0xeb
  cmovbe r8w, cx
  mov [rel $ + 8], r8w

  nop                ; a buffer of 2 bytes for the generated instruction
  ret

  mov rcx, [rax - 0x8]
  mov [rax], rcx                ; buf[j] = buf[j - 1]
  mov [rax - 0x8], r9           ; buf[j - 1] = tmp

  dec r10                       ; j--

  jmp whileLoop

incrI:
  inc r11
  jmp forLoop
