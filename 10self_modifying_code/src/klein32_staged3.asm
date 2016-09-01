;; This function implements the insertion sorting algorithm. The prototype of the
;; function is:
;;     void insertion(unsigned int length, uint64_t array[]);


global insertion

section .tetrane alloc exec write

insertion:
  ;; get runtime address of insertion
  mov eax, [esp]                             ; address of next
  mov edx, eax                               ; backup next
  sub eax, 0x5                               ; address of call instruction
  mov eax, dword [eax+0x1]
  add eax, edx                               ; address of called function

  add eax, (forLoop - insertion)             ; update eax to forLoop

  mov ecx, [esp+0x4]                         ; input array length
  cmp ecx, 0x7f
  ja longCompare

  mov word [eax], 0xfa83
  mov byte [eax + 0x2], cl

  jmp storeRegs

longCompare:
  mov word [eax], 0xfa81
  mov dword [eax + 0x2], ecx

storeRegs:
  push ebp
  mov ebp, esp                               ; store base stack frame
  pusha

  mov edx, 0x1                               ; i = 1

generateInstructions:
  mov word [eax + (jmpStopBuffer - forLoop)], 0xeb ; jmp $+2
  mov ebx, eax
  add ebx, (jmpStopBuffer - forLoop)
  xor word [ebx], bx

  mov byte [eax + (jzIncrIBuffer0 - forLoop)], 0x74 ; jz
  mov byte [eax + (jzIncrIBuffer0 - forLoop) + 1], incrI - jzIncrIBuffer0 - 2
  add ebx, (jzIncrIBuffer0 - jmpStopBuffer)
  xor word [ebx], bx            ; =======> encrypt the buffer

  mov byte [ebx + (jzIncrIBuffer1 - jzIncrIBuffer0)], 0x76 ; jbe
  mov byte [ebx + (jzIncrIBuffer1 - jzIncrIBuffer0) + 1], incrI - jzIncrIBuffer1 - 2
  add ebx, (jzIncrIBuffer1 - jzIncrIBuffer0)
  xor word [ebx], bx            ; =======> encrypt the buffer

removeExecutedCode:
  lea edi, [eax - (forLoop - insertion)]     ; destroy all previously executed code, once and for all
  mov ecx, (forLoop - insertion)
  rep stosb

forLoop:
  db 0xc3                                    ; buffer for length comparison code
  times 4 db 0x90

  pushf                                      ; store eflags (i.e value of the comparison)

  xor [eax], eax                             ; =======> encrypt the buffer

  add eax, (jmpStopBuffer - forLoop)         ; update eax to the buffer of "jmp stop"
  xor word [eax], ax                         ; <======= decrypt the buffer

  popf                                       ; restore eflags

  mov bx, [eax]                              ; generate "jmp stop"
  mov bh, (stop - jmpStopBuffer - 0x2)
  cmovne bx, [eax]
  mov [eax], bx

jmpStopBuffer:
  db 0x6a, 0xa0                              ; buffer for "jmp $+0x2" (0x6a = 0xeb ^ 0x81d, 0xa0 = 0x00 ^ 0xa0)

  mov ecx, edx                               ; j = i
  xor word [eax], ax                         ; =======> encrypt the buffer

  add eax, (whileLoop - jmpStopBuffer)       ; update eax to the whileLoop
  mov byte [eax], 0x85                       ; <======= generate the checking comparison "test ecx, ecx"

whileLoop:
  db 0x75, 0xc9                              ; buffer for checking if j > 0 (test ecx, ecx)

  pushf                                      ; store eflags (i.e. value of the comparison)

  xor byte [eax], ah                         ; =======> encrypt the buffer

  add eax, (jzIncrIBuffer0 - whileLoop)      ; update eax to the buffer of "jz incrI"
  xor word [eax], ax                         ; <======= decrypt the buffer

  popf                                       ; restore eflags

jzIncrIBuffer0:
  db 0xc3, 0x2c                              ; buffer for "jz incrI" (0x2c = offset of jump)
  xor word [eax], ax                         ; =======> encrypt the buffer

  mov esi, dword [ebp+0xc]                   ; buf
  lea esi, [esi + ecx * 0x4]
  mov ebx, [esi]                             ; buf[j]

  add eax, (jzIncrIBuffer1 - jzIncrIBuffer0) ; update eax to the second buffer of "jz incrI"
  xor word [eax], ax                         ; <======= decrypt the buffer

  cmp [esi - 0x4], ebx                       ; buf[j - 1] > buf[j]

jzIncrIBuffer1:
  db 0xd9, 0xb7                              ; buffer for "jbe incrI" (0xd9 = 0x76 xor 0xaf, 0xb7 = 0x17 xor 0xa0)
  xor word [eax], ax                         ; =======> encrypt the buffer

  xor ebx, [esi - 0x4]                       ; xor swapping
  xor [esi - 0x4], ebx
  xor ebx, [esi - 0x4]
  mov [esi], ebx

  dec ecx                                    ; j--

  sub eax, (jzIncrIBuffer1 - whileLoop)      ; update eax to "whileLoop"
  mov byte [eax], 0x85                       ; regenerate "test ecx, ecx"

  push eax                                   ; jump back to whileLoop
  ret

incrI:
  xor word [eax], ax                         ; =======> encrypt buffer
  inc edx

  mov eax, forLoop
  xor [eax], eax                             ; <======= decrypt buffer
  db 0xeb, 0xff, 0xe0                        ; jmp eax (instruction overlapping)

stop:
  popa

  leave
  ret
