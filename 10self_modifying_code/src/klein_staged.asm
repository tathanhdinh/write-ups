;; This function implements the insertion sorting algorithm. The prototype of the
;; function is:
;;     void insertion(unsigned int length, uint64_t array[]);
;;
;; We may notice that once the length of the array is known, we can "hard coded" it
;; into the program using self-modifying code. In some case, it can improve the performance
;; of the algorithm.
;;
;; In the main loop "forLoop" of the algorithm, the counter (which is stored in "r11")
;; is compared with the length of the array (see the comparison at "forLoop"). The value of
;; length will be written directly as an immediate value of the instruction.
;;
;; Following x86-64 ABI on Linux, the first argument (i.e. the length of the array) is
;; passed through "edi". The 5 instructions before "forLoop" will overwrite the immediate
;; value in "cmp r11, 0x0"

global insertion

section .tetrane alloc exec write

insertion:
  mov r11, 0x1                  ; i = 1

  ;; concretize length
  mov byte [rel forLoop + 3], dil
  mov eax, [rel forLoop + 3]
  cmp edi, 0x7f
  cmovg eax, edi
  mov [rel forLoop + 3], eax

forLoop:
  cmp r11, 0x0
  mov rax, rax                  ; a buffer of 3 bytes in case of edi is greater than 0x7f

  je stop

  mov r10, r11                  ; j = i

whileLoop:
  test r10, r10                 ; j > 0?
  jz incrI

  lea rax, [rsi + r10 * 0x8]
  mov r9, [rax]                 ; tmp = buf[j]

  cmp [rax - 0x8], r9           ; buf[j - 1] > buf[j]?
  jbe incrI

  mov rcx, [rax - 0x8]
  mov [rax], rcx                ; buf[j] = buf[j - 1]
  mov [rax - 0x8], r9           ; buf[j - 1] = tmp

  dec r10                       ; j--

  jmp whileLoop

incrI:
  inc r11
  jmp forLoop

stop:
  ret
