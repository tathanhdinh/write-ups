# Deobfuscating an _onion_ obfuscated challenge with REVEN

  The binary `F4b_XOR_W4kfu` proposed in the CTF of Grehack 2015, it is also the code reversing challenge of the highest point over all categories (cryptography, exploit, reverse engineering, etc). The challenge is heavily obfuscated, the obfuscation techniques implemented are novel and interesting.
  
  This is the first article of a series where we introduce our ongoing work in developing an *automated code deobfuscation* system using the *symbolic execution* framework REVEN. Since our approach is **operational** (i.e. we still need some information about how the obfuscation techniques are implemented) this article presents what we have discovered in reversing `F4b_XOR_W4kfu`.
  
  *To the our best knowledge, most approaches in binary code deobfuscation are operational, fully denotational approach only works in very strict cases. As a direct consequence of [Rice's theorem](https://en.wikipedia.org/wiki/Rice%27stheorem), learning general programs simply from input/output relation is a well-known undecidable problem. Even for much more restricted contexts, static analysis is [proven to be NP-hard](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.35.2337) for [smartly obfuscated](https://www.cs.ucsb.edu/~chris/research/doc/acsac07limits.pdf) programs. Recent [semantics-based](https://www.cs.arizona.edu/people/debray/Publications/ccs-unvirtualize.pdf) approaches are intrinsically [operational](http://static.usenix.org/event/woot09/tech/full_papers/rolles.pdf); though [some](https://cs.arizona.edu/~debray/Publications/ccs2015-symbolic.pdf) are considered [generic](https://www.cs.arizona.edu/people/debray/Publications/generic-deobf.pdf), they work only on simple cases of very specific obfuscation techniques. However, special classes of loop-free programs can be efficiently [synthesized](http://people.eecs.berkeley.edu/~sseshia/pubdir/synth-icse10.pdf) from input/output with helps of SMT solvers.*
  
## Introduction
  
  `F4b_XOR_W4kfu.exe` is a 32 bits PE binary, without any fancy GUI, it asks for a password from the standard input and then prints `Nop!` or `Yes!`. The mission is to find out the good password (one that makes the program print `Yes!`).
  
    ./F4b_XOR_W4kfu.exe 
    Welcome!
    Password? 1234aqzert
    Nop!⏎
  
  The program uses several obfuscation techniques to prevent itself from being analyzed. First, its execution traces are extremely long (the challenge sacrifices performance a lot for the obfuscation purpose) because of a [code decryption/re-encryption](https://www.cosic.esat.kuleuven.be/wissec2006/papers/3.pdf) mechanism and of a [nested multiprocess virtual machine](https://aspire-fp7.eu/spro/wp-content/uploads/SPRO2015_Workshop_Talk_V2.pdf) execution model. Second, the "input related" instructions are not local, they instead spread out (extremely long) traces; the password checking algorithm is "mostly" constant time. Last but not least, most instructions of the binary are encrypted, they are decrypted just before executing and are immediately reencrypted later (so we cannot "unpack" it in classical sense). 
  
  These properties make difficult for direct dynamic/static analysis and for concolic execution. Low-hanging fruit attacks, e.g. black-box attack on counting number of executed instructions, seems not feasible.

### REVEN - a very short introduction

  REVEN Axion is a framework which does *system-level symbolic execution*,  enriched by code analysis plugins interacting with the core using Python or C/C++ API. One of the essential differences between REVEN and other symbolic execution engines is that it does symbolic execution for *all execution threads* presenting on the system, from ring 0 to ring 3. 
  
  In a basic reversing engineering task, we start by creating a *scenario* which executes the "need to be examined binary" in a virtual machine; the result of the scenario will be used in further analysis. For example, in case of `F4b_XOR_W4kfu` we create a scenario which executes the binary with some input flag, the scenario terminates when the binary stops.
  <!-- by printing output string `Nop!`. -->
  
  Basically, REVEN is rather a dynamic analysis tool, it has not yet advanced static analysis features (control-flow analysis, etc) that we may normally observe in the "de facto" reverse code engineering IDA Pro, but we can *synchronize* between REVEN and IDA Pro using [qb-sync](https://github.com/quarkslab/qb-sync) to combine the strength of both.

  ![Binary analysis with REVEN](./reven_basic_gui.png)
  
  The REVEN-Axion [document](http://doc.tetrane.com/latest/) describes in detail how to create a binary analysis [scenario](http://doc.tetrane.com/latest/scenario_creation.html), the configuration guide for REVEN's addons, included qb-sync, can be referenced [here](http://doc.tetrane.com/latest/gui_addons.html).
  
## Reversing

  An advantage of REVEN is that it captures all executed instructions, it is virtually immune from anti-debugging tricks that might be applied, so every "hidden" activities are disclosed clearly under REVEN. Since a scenario is system-wide, the executed instructions come from all executing threads on the system;  but in this case we are interested in instructions of the binary only, we select instructions executed by `F4b_XOR_W4kfu.exe`, the result is equivalent with the execution trace of the program.
  
  The first thing we can observe is the binary starts executing from the instruction at the address `0x402000`, this is also the entry point of the program, we can easily recheck this fact with IDA Pro.
  
    objdump -f F4b_XOR_W4kfu.exe 
    
      F4b_XOR_W4kfu.exe:     format de fichier pei-i386
      architecture: i386, fanions 0x00000102:
      EXEC_P, D_PAGED
      adresse de départ 0x00402000

  The behaviors of first several instructions disassembled by `objdump` can be easily interpreted by REVEN. For example, the instructions at `0x402008` and `0x402013` are calls to `GetStdHandle`, one at `0x40202c` calls `WriteFile`, and one at `0x402042` calls `ReadFile`, that indeed corresponds to the step of print the strings `Welcome!` and `Password? `, then reads password from the standard input.

    objdump -d --start-address=0x402000 F4b_XOR_W4kfu.exe
    
    F4b_XOR_W4kfu.exe:     format de fichier pei-i386
    
    
    Déassemblage de la section .text :
    
    00402000 <.text>:
      402000:       55                      push   %ebp
      402001:       89 e5                   mov    %esp,%ebp
      402003:       83 ec 0c                sub    $0xc,%esp
      402006:       6a f5                   push   $0xfffffff5
      402008:       ff 15 69 10 40 00       call   *0x401069
      40200e:       89 45 fc                mov    %eax,-0x4(%ebp)
      402011:       6a f6                   push   $0xfffffff6
      402013:       ff 15 69 10 40 00       call   *0x401069
      402019:       89 45 f8                mov    %eax,-0x8(%ebp)
      40201c:       6a 00                   push   $0x0
      40201e:       8d 45 f4                lea    -0xc(%ebp),%eax
      402021:       50                      push   %eax
      402022:       6a 14                   push   $0x14
      402024:       68 84 31 40 00          push   $0x403184
      402029:       ff 75 fc                pushl  -0x4(%ebp)
      40202c:       ff 15 71 10 40 00       call   *0x401071
      402032:       6a 00                   push   $0x0
      402034:       8d 45 f4                lea    -0xc(%ebp),%eax
      402037:       50                      push   %eax
      402038:       6a 18                   push   $0x18
      40203a:       68 98 31 40 00          push   $0x403198
      40203f:       ff 75 f8                pushl  -0x8(%ebp)
      402042:       ff 15 6d 10 40 00       call   *0x40106d
      402048:       a0 41 30 40 00          mov    0x403041,%al
      40204d:       fe c0                   inc    %al
      40204f:       90                      nop
      402050:       90                      nop
      402051:       90                      nop
      402052:       90                      nop
      402053:       e8 a8 1f 00 00          call   0x404000
      402058:       78 b3                   js     0x40200d
      40205a:       f6 29                   imulb  (%ecx)
      ...

### Code decryption/re-encryption mechanism
    
  The behaviors above are not really interesting, which really attracts our attention is the instruction at `0x402058` since REVEN informs that there is an *execution after write* at this address (this feature comes from the plugin `execution-after-write detection` which should be enabled before analyzing the scenario): that means this instruction are overwritten before being executed. The static disassemble result of `objdump` says that this instruction is `js 0x40200d`, but it is not correct, the actually executed instruction is `xor eax, eax` which can be observed directly from REVEN.
  
  ![Execution after write](./reven_exec_after_write.png)
  
  By comparing the static disassemble result and the actually executed trace, we observe that there are no other overwritten instructions until the `call` at `0x402053`, so the instructions following this call must have overwritten the instruction at `0x402058`
