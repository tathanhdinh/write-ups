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

  Let's consider the higher basic blocks and their control flow, consisting of in the following control flow graph (for comprehension purpose, we have omitted `nop` instructions, also we have split the basic block), they form a [region](http://digital.cs.usu.edu/~allan/AdvComp/Notes/controld/controld.html) whose the header is the block at `0x402048`, there is even a unique exit block at `0x402096`. This is an useful property since we can safely isolate the [data-flow analysis](https://en.wikipedia.org/wiki/Data-flow_analysis) on these blocks from other parts of the program.

  <a name="dispatchercfg">
  ![Dispatcher](images/f4b_vm1_dispatcher.svg)
  </a>
  
  **Remark:**
  *for comprehension purpose, we have omitted `nop`(s) from basic blocks; also the instruction `test ebx, ...` is split from the exit block, so it is not included in the region*

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
  
  
#### Multitasking virtual machine ####

  This bit-level data extracting sequence above is repeated at lower blocks, and the control flow is diverted by `test ebx, ...` instructions depending on the extracted value. More concretely, for each "kind" of the extracted data, there is a unique corresponding operator that is consisted in a single block (e.g. ones at `0x402250`, `0x40263c`, etc.), or in several blocks (e.g. one consisted of blocks at `0x404d6`, `0x402572`, `0x402573`, `0x404331`, etc.)
  
  Noticing that the bit-offset is stored as a `word` value at `0x403042`. Moreover, the base address of the array where the data at a given bit-offset is extracted is indexed by `eax` in a `dword` array at `0x40268b`:
  
    0x4020a0  mov ebx, dword ptr [eax+0x40268b]
    
  whereas `eax` is calculated by:
  
    0x402096  movzx eax, byte ptr [0x403ca0]
    0x40209d  shl eax, 0x2
    
  Examining on REVEN-Axion the [memory access](#memaccess403ca0) at `0x403ca7`, we observe that the `byte` value stored at this address is *periodically increased* from `0` to `6`. This fact is statically verified by observing the increment of `al` at `0x4046a8` on the [control flow graph](#dispatchercfg) of the dispatcher.
  
  <a name="memaccess403ca7">
  ![Memory access at `0x403ca7`](images/proc_time_slice_counter.png)
  </a>
  
  In summary, we have the following pseudo-code illustrating the semantics of the region:
  
    let opcode_extract (time_slice: uint8 byref) (proc_id: uint8 byref) (proc_ip: uint16 byref) ()

[1]: Aho, A. V. et al. Compilers: Principles, Techniques, and Tools, 3rd Edition.
