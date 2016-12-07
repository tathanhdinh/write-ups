Title: Unfolding obfuscated code with Reven (part 2)
Date: 2016-12-06 17:25
Tags: reverse engineering, deobfuscation, ctf
Category: Technical
Author: tdta
Slug: reversing-f4b-challenge-part1

  In the previous article, we have obtained a control flow graph of the challenge resulted in abstracting the runtime effect of the first machine. The basic block starting at `0x402048` is the *entry point*, whereas the basic blocks at `0x4023d4` and at `0x40266e` are the *exit points* corresponding to the case the program prints `Yes!` and `Nop!`.

## Loops analysis ##

  It is quite direct to recognize [natural loops][1] in this graph. Indeed, the entry point basic block is also the root of the dominator tree; there are *back edges*, for example, from the basic block starting at `0x402460` to the entry point, or from one at `0x402513` to the entry point, etc. These back edges from natural loops which have a common header, which is the entry point basic block, then can be combined into a single natural loop. There are also some *nested loops*

[1]: sdfds "sdf"

