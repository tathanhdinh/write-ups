using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
//using UnicornManaged;
//using Gee.External.Capstone;

namespace emuTracer
{
  class Program
  {
    static void Main(string[] args)
    {
      using (var uce = new UnicornManaged.Unicorn(UnicornManaged.Const.Common.UC_ARCH_X86, UnicornManaged.Const.Common.UC_MODE_32))
      using (var disasm = Gee.External.Capstone.CapstoneDisassembler.CreateX86Disassembler(Gee.External.Capstone.DisassembleMode.Bit32))
      {
        // memory mapping
        uce.MemMap(0x804a117, 2 * 1024 * 1024, UnicornManaged.Const.Common.UC_PROT_ALL);

        // initialize registers
      }
    }
  }
}
