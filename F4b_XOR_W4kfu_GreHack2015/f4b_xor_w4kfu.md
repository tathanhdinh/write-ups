# Deobfuscating an _onion_ obfuscated challenge with REVEN

  The binary `F4b_XOR_W4kfu` proposed in the CTF of Grehack 2015, it is the code reversing challenge of the highest point over all categories (cryptography, exploit, reverse engineering, etc). We think one of the reasons for which the challenge is worth this point is because it is heavily obfuscated, the obfuscation techniques implemented are novel and interesting.
  
  This is the first article of a series where we introduce our ongoing work in developing an automated deobfuscation system using the *symbolic execution* framework REVEN. Since our approach is *operational*[^fn1], namely we still need some information about how the obfuscation techniques are implemented, in this article we present what we discovered in reversing `F4b_XOR_W4kfu`.
  
## Introduction
  
  `F4b_XOR_W4kfu.exe` is a 32 bits PE binary, without any fancy GUI, it asks for a password from the standard input and then prints `Nop!` or `Yes!`. The mission is to find out the good password (one that makes the program print `Yes!`).
  
    ./F4b_XOR_W4kfu.exe 
    Welcome!
    Password? 1234aqzert
    Nop!⏎
  
  The program uses several obfuscation techniques to prevent itself from being analyzed. First, its execution traces are extremely long (the challenge sacrifices performance a lot for the obfuscation purpose) because of a *code decryption/re-encryption* mechanism and of a *nested multiprocess virtual machine* execution model. Second, the "input related" instructions spread out (extremely long) traces, the password checking algorithm is "mostly" constant time.
  
  Last but not least, most instructions of the binary are encrypted, they are decrypted just before executing and are immediately reencrypted later (so we cannot "unpack" it using traditional approaches). These properties make difficult for direct dynamic/static analysis and for concolic execution.
  
  [^fn1]: As far as we know, all current binary code deobfuscation approaches are operational. As a direct result of Rice's theorem, learning general programs simply from *input/output* is a well-known undecidable problem. Even for much more restricted contexts, static analysis is [proven to be NP-hard](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.35.2337) for [smartly obfuscated](https://www.cs.ucsb.edu/~chris/research/doc/acsac07_limits.pdf) programs.

#### REVEN - a very short introduction

  REVEN Axion is a framework which does *system-level symbolic execution*,  enriched by code analysis plugins interacting with the core using Python or C/C++ API. One of the essential differences between REVEN and other symbolic execution engines is that it does symbolic execution for *all execution threads* presenting on the system, from ring $0$ to ring $3$. 
  
  In a basic reversing engineering task, we start by creating a *scenario* which executes the "need to be examined binary" in a virtual machine; the result of the scenario will be used in further analysis. For example, in case of `F4b_XOR_W4kfu` we create a scenario which executes the binary with some input flag, the scenario terminates when the binary stop by printing output string `Nop!`.

  ![Binary analysis with REVEN]
  (./reven_basic_gui.png)
  
## Execution trace

  An advantage of REVEN is that it captures all executed instructions of the binary, it is virtually immune from anti-debugging tricks that may be applied, so every "hidden" activities are disclosed clearly under REVEN. Since a scenario is system-wide, the executed instructions come from all executing threads on the system;  but in this case we are interested in instructions of the binary only, we select instructions executed by `F4b_XOR_W4kfu.exe`, the result is equivalent with the execution trace of the program.
  
  The first thing we can observe is the binary starts executing from the instruction at the address `0x402000`, this is also the entry point of the program, we can check this fact using `objdump`:
  
    objdump -f F4b_XOR_W4kfu.exe 
    
      F4b_XOR_W4kfu.exe:     format de fichier pei-i386
      architecture: i386, fanions 0x00000102:
      EXEC_P, D_PAGED
      adresse de départ 0x00402000

  The behaviors of first several instructions disassembled by `objdump` can be easily interpreted by REVEN. For example, the instruction at `0x402008` is a call to `GetStdHandle`, one 

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

  
