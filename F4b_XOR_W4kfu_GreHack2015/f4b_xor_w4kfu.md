# Deobfuscating an _onion_ obfuscated challenge with REVEN

  We present a code reverse engineering task with our product Reven. The binary examined here is `F4b_XOR_W4kfu`, it is also the challenge of the highest point over all categories (cryptography, exploit, reverse engineering, etc) in the [Grehack 2015's CTF](https://grehack.fr/2015/ctf). The binary is heavily obfuscated, but the obfuscation techniques implemented are novel and interesting.
  
  This is the first article of a series where we introduce our ongoing work in developing an *automated code deobfuscation* system using the *symbolic execution* framework of REVEN. Since our approach is **operational** (i.e. we require some information about how the obfuscation techniques are implemented) this article presents technical details that we discovered in reversing `F4b_XOR_W4kfu`.
  
  *To the our best knowledge, most approaches in binary code deobfuscation are operational, fully denotational approach works in very strict cases only. As a direct consequence of [Rice's theorem](https://en.wikipedia.org/wiki/Rice%27stheorem), learning general programs simply from input/output relation is a well-known undecidable problem. Even for much more restricted contexts, static analysis is [proven to be NP-hard](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.35.2337) for [smartly obfuscated](https://www.cs.ucsb.edu/~chris/research/doc/acsac07limits.pdf) programs. Recent [semantics-based](https://www.cs.arizona.edu/people/debray/Publications/ccs-unvirtualize.pdf) approaches are intrinsically [operational](http://static.usenix.org/event/woot09/tech/full_papers/rolles.pdf); though [some](https://cs.arizona.edu/~debray/Publications/ccs2015-symbolic.pdf) are considered [generic](https://www.cs.arizona.edu/people/debray/Publications/generic-deobf.pdf), they work only on simple cases of very specific obfuscation techniques. However, special classes of loop-free programs can be efficiently [synthesized](http://people.eecs.berkeley.edu/~sseshia/pubdir/synth-icse10.pdf) from input/output with helps of SMT solvers.*
  
## Introduction
  
  `F4b_XOR_W4kfu.exe` is a 32 bits PE binary, without any fancy GUI, it asks for a password from the standard input and then prints `Nop!` or `Yes!`. The mission is to find out the good password (one that makes the program print `Yes!`).
  
    ./F4b_XOR_W4kfu.exe 
    Welcome!
    Password? 1234aqzert
    Nop!⏎
  
  The program uses several **obfuscation** techniques to prevent itself from being analyzed. *First*, its execution traces are extremely long taking consideration that the program is *just* a CTF challenge (after receiving the input, there are 2.716.465.511 instructions executed until the first comparison of the password checking procedure), this is because of a [code decryption/re-encryption](https://www.cosic.esat.kuleuven.be/wissec2006/papers/3.pdf) mechanism and of a [nested multiprocess virtual machine](https://aspire-fp7.eu/spro/wp-content/uploads/SPRO2015_Workshop_Talk_V2.pdf) execution model.
  
  *Second*, the "input related" instructions in a trace are not local, they instead spread out the long trace, that makes difficult to figure out how the input password is manipulated and checked; moreover the password checking algorithm is "mostly" constant time. *Last but not least*, most instructions of the binary are encrypted, they are decrypted just before executing and are immediately reencrypted later, so we cannot [unpack](http://s3.eurecom.fr/docs/oakland15_packing.pdf) it in the [classical sense](http://ftp.cs.wisc.edu/paradyn/papers/Roundy12Packers.pdf). 
  
  These properties make difficult for direct dynamic/concolic/static analysis. Low-hanging fruit approaches, e.g. black-box attack on counting number of executed instructions, seems not feasible: until the first "input sensitive" comparison, there is  volume of more than 2.7 billion instructions must be passed.

### Reven - a very short introduction

  Basically, REVEN Axion is a **system-level symbolic execution** engine,  enriched by code analysis plugins interacting with the core using Python or C/C++ API. One of the essential differences between Reven and other engines is that it does symbolic execution for *all execution threads* presenting on the system, from ring 0 to ring 3. 
  
  In a basic reversing engineering task with Reven, we start by creating a **scenario** which executes the binary in consideration in a virtual machine; the result of the scenario will be used in further analysis. For example, in case of `F4b_XOR_W4kfu` we create a scenario which executes the binary with some input flag, the scenario terminates when the binary stops.
  
  ![Binary analysis with Reven](./reven_basic_gui.png)
  
  An advantage of Reven is that it **computes** all instructions being executed, it is immune from anti-debugging/anti-instrumenting tricks that might be applied. But symbolically executed instructions come from all executing threads on the system since a *scenario is system-wide*; but we can always filter instructions executed by the examined binary, the result is somehow equivalent with the execution trace.
  
  The symbolic execution approach of Reven is different from approaches of debuggers and [dynamic](http://www.dynamorio.org/) [binary](https://software.intel.com/en-us/articles/pin-a-dynamic-binary-instrumentation-tool) [instrumentation](http://valgrind.org/) [tools](http://www.frida.re/) where instructions are still executed on the real hardware, that is still a rich source for [escaping tricks](https://recon.cx/2012/schedule/attachments/42_FalconRiva_2012.pdf) which exploit [nontransparent effects](https://www.blackhat.com/docs/us-14/materials/us-14-Li-Defeating-The-Transparency-Feature-Of-DBI.pdf) of DBI.
  
  
#### Synchronization with IDA Pro
  Reven is rather a dynamic analysis tool, it has not yet advanced static analysis features (control-flow analysis, etc) that we may normally observe in other tools, but we can **synchronize** between Reven and IDA Pro (as a "de-facto" reverse code engineering tool) using [qb-sync](https://github.com/quarkslab/qb-sync) to combine the strength of both.
  
  *The REVEN-Axion [document](http://doc.tetrane.com/latest/) describes in detail how to create a binary analysis [scenario](http://doc.tetrane.com/latest/scenariocreation.html). The configuration guide for REVEN's addons, included qb-sync, can be referenced [here](http://doc.tetrane.com/latest/guiaddons.html).*
  
## Reversing
  
  The first thing we can observe is the binary starts executing from the instruction at the address `0x402000`, this is also the entry point of the program, we can easily recheck this fact with IDA Pro. The behaviors of several first instructions are not really interesting, as we can both check using Reven or IDA Pro, for example, the instructions at `0x402008` and `0x402013` are calls to `GetStdHandle`, one at `0x40202c` calls `WriteFile`, and one at `0x402042` calls `ReadFile`, that indeed corresponds to the step of print the strings `Welcome!` and `Password? `, then reads password from the standard input.
  
  ![Synchronization between REVEN-Axion and IDA Pro](./reven_sync_idapro.png)

### Code decryption/re-encryption mechanism
    
  The behaviors above are not really interesting, which really attracts our attention is the instruction at `0x402058` since REVEN informs that there is an *execution after write* at this address (this feature comes from the plugin `execution-after-write detection` which should be enabled before analyzing the scenario): that means this instruction are overwritten before being executed. The static disassemble result of `objdump` says that this instruction is `js 0x40200d`, but it is not correct, the actually executed instruction is `xor eax, eax` which can be observed directly from REVEN.
  
  ![Decrypted code](./)
  
  ![Execution after write](./reven_exec_after_write.png)
  
  By comparing the static disassemble result and the actually executed trace, we observe that there are no other overwritten instructions until the `call` at `0x402053`, so the instructions following this call must have overwritten the instruction at `0x402058`
