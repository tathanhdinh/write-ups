<!-- Title: Unfolding obfuscated code with Reven (part 2) -->
<!-- Date: 2016-12-06 17:25 -->
<!-- Tags: reverse engineering, deobfuscation, ctf -->
<!-- Category: Technical -->
<!-- Author: tdta -->
<!-- Slug: reversing-f4b-challenge-part1 -->

  Last time, by abstracting the binary from the runtime effect of the first virtual machine, we have reduced it to a **semantically equivalent** program with a simpler control flow graph. This graph has its unique *entry point* as the basic block starting at `0x402048`, whereas ones at `0x4023d4` and at `0x40266e` are  *exit points* corresponding to the case where the program prints `Yes!` and `Nop!`.

## Loops analysis ##

  It is quite direct to identify [natural loops](https://en.wikipedia.org/wiki/Control_flow_graph) this graph. Indeed, the entry point block is also the root of the *dominator tree*; there are *back-edges*, e.g. from the basic block starting at `0x402460` to the entry point, or from one at `0x402513` to the entry point, etc. These back edges form natural loops which have a common *header* (that is the entry point), then can be combined into a single natural loop. There are also some *nested loops*, e.g. one having the basic block `0x4044d6` as its header and `0x404331 -> 0x4044d6` as its back-edge.

  Since the program terminates by calling `ExitProcess` either at the block `0x4023d4` or `0x40266e` (respectively for `Nop` or `Yes!`), also the exit block (i.e. one at `0x40235`) *post-dominates* these terminating blocks. That means we can "add" two pseudo back-edges `0x4023d4 -> 0x402048` and `0x40266e -> 0x402048` without changing the semantics of the program. Consequently, the program can be interpreted as a single "high-level" `while (true)` loop, with several loops nested within.

  <!-- **Remark:** -->
  <!-- Some properties about the dominance relation between basic blocks can be quickly checked on Reven-Axion. For example, the block `0x403048` is an immediate dominator of `0x404563` then their number of occurrences on the trace must be the same; indeed this number is `178217` for each, this corresponds also to the number of iterations of the outer-most loop. Or the blocks `0x402058` and `0x402096` have the unique post dominator `0x404563` then their sum of occurrences must equal to the number of occurrences of `0x404563`. -->

  The program is "just" a loop, would life be easy from now, huh?. Not this time, unfortunately. Welcome to the world of bit-level and multi-process virtual machines.

## Reversing the second virtual machine ##

  We can quickly recognize a "pattern" in the loop. There are "high" blocks, i.e. ones starting at `0x402048`, `0x404563`, `0x402058`, `0x4046a8`, `0x40207f`, `0x402081` and `0x402096`, which seems to be used to extract some value into `ebx`. Next, there are tests on `ebx` with some constants (e.g. at `0x4020d3`, `0x4020c7`, etc.), and depending on the results of tests, there are corresponding "low" blocks, (e.g. at `0x4022f8`, `0x4023de`, `0x40217b`, `0x402486`, .etc) which seems to do the real things.

  This pattern suggests us to think of a **virtual machine** with switch-based dispatcher again: the higher blocks might correspond with the dispatcher whereas the lower ones might correspond with opcodes.

### Dispatcher ###

  Let's consider the higher basic blocks and their control flow, consisting of in the following control flow graph. They form a [region](http://digital.cs.usu.edu/~allan/AdvComp/Notes/controld/controld.html) whose the header is the block at `0x402048`, there is even a unique exit block at `0x402096`. This is an useful property since we can safely isolate the [data-flow analysis](https://en.wikipedia.org/wiki/Data-flow_analysis) on these blocks from other parts of the program.

  <a name="dispatchercfg">
  ![Dispatcher](images/f4b_vm1_dispatcher.svg)
  </a>
  
  **Remark:**
  *for comprehension purpose, we have omitted `nop`(s) from basic blocks; the instruction `test ebx, ...` is split from the exit block, so it is not included in the region. We have added also a "pseudo" back-edge from the lowest block to the entry point to imply that the dispatcher is executed through a loop.*

  Indeed, we observe that this region accesses `5` different memory addresses: `0x403041` (byte access), `0x403ca7` (byte access), `0x403042` (word access), `0x40268b` (double word access). Moreover, a simple [liveness analysis](https://en.wikipedia.org/wiki/Live_variable_analysis) shows that all accessed registers are *dead* before entering the header block; except `ebx`, they are also *dead* when going out the exit block. Consequently, the region is completely "parameterized" by values at these memory addresses.

#### Bit-level access ####

  To recover the semantics of the region, we notice an interesting pattern in the exit block (which occurs also at lower basic blocks, e.g. at `0x4023de`, `0x4022f8`, etc). That is the following sequence of instruction:

    mov ebx, dword ptr [eax+0x40268b]  ; ebx = address of a byte array
    mov ax, word ptr [0x403042]        ; eax = a bit-level offset
    xor edx, edx
    mov ecx, 0x8
    div ecx                            ; eax = eax / 8 (byte-level offset)
    add ebx, eax                       ; ebx = address of the element at this offset in the array
    mov ebx, dword ptr [ebx]           ; get the dword at this address
    bswap ebx                          ; most significant byte of ebx becomes the byte at the address
    mov cl, dl                         ; note: edx = eax % 8 (bit-level remainder)
    shl ebx, cl                        ; remove remainder bits and round ebx
    
  As explained in the comments above, given some offset `i` in bits, the sequence extracts a `dword` in a byte array from the **bit-offset** `i`, the extracted value is rounded to `2^(i % 8)`. 
  
  This bit-level data extracting pattern is repeated at other blocks, the control flow is diverted by `test ebx, ...` instructions depending on the extracted value. More concretely, for each "kind" of the extracted data, there is a unique corresponding operator that is consisted in a single block (e.g. ones at `0x402250`, `0x40263c`, etc.), or in several blocks (e.g. one consisted of blocks at `0x404d6`, `0x402572`, `0x402573`, `0x404331`, etc.). That is a "strong" indication of a virtual machine.
  
  
<!-- #### Multitasking virtual machine #### -->
#### Opcode tables ####

  We now examine the array where bit-level data is extracted (i.e. the opcode table). First, noticing that the bit-offset is typed as `word` value at `0x403042`. Moreover, the address of the opcode table is indexed by `eax` in a `dword` array at `0x40268b`:
  
    0x4020a0  mov ebx, dword ptr [eax+0x40268b]
    
  whereas `eax` is calculated by:
  
    0x402096  movzx eax, byte ptr [0x403ca7]
    0x40209d  shl eax, 0x2
    
  Examining on REVEN-Axion the [memory access](#memaccess403ca0) at `0x403ca7`, we observe that the `byte` value stored at this address is *periodically increased* from `0` to `6` (we call it opcode table `ID`):
  
    0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4,...
  
  <a name="memaccess403ca7">
  ![Memory access at `0x403ca7`](images/proc_time_slice_counter.png)
  </a>
  
  and when examining corresponding `dword`(s) starting at `0x40268b`, we receive the following values:
  
    0x403c32, 0x40365b, 0x403056, 0x403598, 0x403121, 0x403d88, 0x403000
  
  <a name="opcodetable">
  ![Opcode tables](images/opcode_tables.png)
  </a>
  
  each is the base address of an opcode table, so we get `7` different tables!!! Well, a virtual machine with multiple opcode tables, that's nice :-)
  
  **Remark:**
  The periodic increment from `0` to `6` of the opcode table index can be also *verified* by observing the following slice obtained by statically [slicing](https://en.wikipedia.org/wiki/Program_slicing) the [dispatcher](#dispatchercfg) with respect to the point of interest at `0x402096` and the value of `eax`.
  
  <a name="opcodetableslice">
  ![Slice of the dispatchercfg](images/f4b_opcode_table_slice.svg)
  </a>
  
#### Instruction pointers ####
  
  As examined [above](#bit-level-access), in extracting data at each opcode table, the bit-level offset is read as a `word` at `0x403042`:
  
    0x4020a6  mov ax, word ptr [0x403042]
    
  moreover, we observe that this value is indexed also by the ID of the opcode table in a `word` array at `0x403048`:
  
    0x402081  mov byte ptr [0x403ca7], al      ; table ID
    0x402086  shl eax, 0x1
    0x402088  mov bx, word ptr [eax+0x403048]  ; bit-level offset
    0x40208f  mov word ptr [0x403042], bx
    
  Also, this is nothing surprising (the dispatcher is not obfuscated, fortunately :-)) that this offset is updated back to the array by:
  
    0x40205f  movzx eax, byte ptr [0x403ca7]   ; table ID
    0x402066  mov bx, word ptr [0x403042]      ; bit-level offset
    0x40206d  movzx ecx, al
    0x402070  shl cl, 0x1
    0x402072  mov word ptr [ecx+0x403048], bx  ; update
  
  So for each opcode table ID, we have a pair of `(opcode table, bit-level offset)`. Noticing that each offset can be interpreted as the "instruction pointer" of a virtual machine, that means there are indeed `7` **concurrent virtual machines** (corresponding with `ID`(s) from `0` to `6`), each has its own code and instruction pointer, and they share the same dispatcher and opcode handlers.
  
#### Multitasking ####

  We notice that if the value of `al` at the instruction at `0x404568` is not `5` then the bit-level offset (i.e. the instruction pointer) is not extracted (resp. updated) from (resp. to) the instruction pointer table (i.e. `word` array at `0x403048`), it is simply increased when extracting data from the corresponding opcode table. Since `al` is assigned by the `byte` value at `0x403041`, slicing the dispatcher with respect to this `byte`, we have the following control flow graph:
  
  ![VM's time slicing](images/f4b_vm_time_slice.svg)
  
  We need understand how virtual machines switch execution. Considering first the instructions at `0x402048`, `0x40204d` and `0x40204d` in the [previous slice](#opcodetableslice), if the value of `al` at `0x404568` is not `5` then 
  
  In summary, we have the following pseudo-code illustrating the semantics of the region:
  
    let opcode_extract (time_slice: uint8 byref) (proc_id: uint8 byref) (proc_ip: uint16 byref) ()


