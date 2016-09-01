// using System;

namespace ch12
{
  struct Gadget
  {
    public ELFSharp.ELF.ELF<uint> ElfReader;
    public uint Address;
    public uint Length;
    public byte[] Signature;
    public byte[] Content;


    public Gadget(uint offset, ELFSharp.ELF.ELF<uint> elfReader)
    {
      ElfReader = elfReader;

      // default assignment
      Address = 0x0;
      Length = 0x0;
      Signature = new byte[0];
      Content = new byte[0];

      var segments = ElfReader.Segments;
      foreach (var seg in segments)
      {
        var segBaseAddress = seg.Address;
        var segSize = seg.Size;

        // System.Console.WriteLine("segment address: 0x{0:x}, length: {1:d} bytes", segBaseAddress, segSize);

        if (offset >= segBaseAddress && offset < segBaseAddress + segSize)
        {
          var segContent = seg.GetContents();
          Address = System.BitConverter.ToUInt32(segContent, System.Convert.ToInt32(offset - segBaseAddress));
          Length = System.BitConverter.ToUInt32(segContent, System.Convert.ToInt32(offset + sizeof(uint) - segBaseAddress));
          Signature = new byte[12];
          System.Array.Copy(segContent, System.Convert.ToInt32(offset + sizeof(uint) + sizeof(uint) - segBaseAddress), Signature, 0, 0xc);
          break;
        }
      }

      if (Address != 0x0U) {
        foreach (var seg in segments) {
          var segBaseAddress = seg.Address;
          var segSize = seg.Size;

          if (Address >= segBaseAddress && Address < segBaseAddress + segSize) {
            var segContent = seg.GetContents();

            Content = new byte[Length];
            System.Array.Copy(segContent, Address - segBaseAddress, Content, 0, Length);
          }
        }
      }
      else throw new System.IndexOutOfRangeException("Gadget cannot found");

      if (Content.Length == 0) throw new System.IndexOutOfRangeException("Cannot read gadget content");
    }

    public void MixWithPassword(byte[] password)
    {
      var passwdIdx = 0;
      for (var i = 0; i < Content.Length; i++) {
        if (passwdIdx == password.Length) passwdIdx = 0;
        Content[i] = (byte)((Content[i] ^ password[passwdIdx]) - 0xaa);
        passwdIdx++;
      }
    }

		public byte[] GetSelfEncryptedArray()
		{
      // zeroing initVector
      var initVector = new byte[0xc];
      System.Array.Clear(initVector, 0, 0xc);

      var vectorIdx = 0;
      foreach (var byteValue in Content) {
        if (vectorIdx == 0xc) vectorIdx = 0x0;

        initVector[vectorIdx] ^= byteValue;

        vectorIdx++;
      }

      return initVector;
		}

    public void FindPassword()
    {
      // password as 12 bitvectors of 8 bits
      var z3Ctxt = new Microsoft.Z3.Context();
      // var bv8Sort = z3Ctxt.MkBitVecSort(8);
      Microsoft.Z3.BitVecExpr[] passwords = new Microsoft.Z3.BitVecExpr[0xc];
      for (var i = 0; i < passwords.Length; i++) {
        var passwordNameI = "password" + i.ToString();
        // passwords[i] = z3Ctxt.MkConst(passwordNameI, bv8Sort);
        passwords[i] = z3Ctxt.MkBVConst(passwordNameI, 8);
      }

      var gadgetSymbolicContent = new Microsoft.Z3.BitVecExpr[Content.Length];
      for (var i = 0; i < Content.Length; i++) {
        gadgetSymbolicContent[i] = z3Ctxt.MkBV(Content[i], 8);
      }

      // calculate gadget's symbolic content in mixing with the password
      var passwdIdx = 0;
      for (var i = 0; i < Content.Length; ++i) {
        if (passwdIdx == 0xc) passwdIdx = 0;
        gadgetSymbolicContent[i] = z3Ctxt.MkBVSub(z3Ctxt.MkBVXOR(gadgetSymbolicContent[i],
                                                                 passwords[passwdIdx]), z3Ctxt.MkBV(0xaaU, 8));
        passwdIdx++;
      }

      // calculate self-encrypted vector
      var encryptedVector = new Microsoft.Z3.BitVecExpr[0xc];
      for (var i = 0; i < 0xc; ++i) {
        encryptedVector[i] = z3Ctxt.MkBV(0x0U, 8);
      }
      var vectorIdx = 0;
      foreach (var bv in gadgetSymbolicContent) {
        if (vectorIdx == 0xc) vectorIdx = 0x0;
        encryptedVector[vectorIdx] = z3Ctxt.MkBVXOR(encryptedVector[vectorIdx], bv);
        vectorIdx++;
      }

      // generate conditions
      var bvConds = new Microsoft.Z3.BoolExpr[0xc];
      for (var i = 0; i < 0xc; ++i) {
        bvConds[i] = z3Ctxt.MkEq(encryptedVector[i], z3Ctxt.MkBV(Signature[i], 8));
      }
      // bvConds.Aggregate(z3Ctxt.MkAnd);

      // var aggrCond = z3Ctxt.MkAnd(bvConds);
      var z3Solver = z3Ctxt.MkSolver("QF_ABV");
      z3Solver.Assert(bvConds);

      System.Console.WriteLine(z3Solver.Check());
    }
  };

  class Program
  {
    private static Gadget[] Gadgets;

    private static void extractGadget(string fileName)
    {
      var elfReader = ELFSharp.ELF.ELFReader.Load<uint>(fileName);
      Gadgets = new Gadget[]
      {
        new Gadget(0x8056427U, elfReader), new Gadget(0x805643bU, elfReader), new Gadget(0x805644f, elfReader)
      };
    }

    public static void Main (string[] args)
    {
      if (args.Length < 1) {
        System.Console.WriteLine("Please give the input binary in the command line (e.g. ./ch12.exe inputFile)");
      }
      else {
        var fileName = args[0];
        System.Console.WriteLine("Input file: %s", args[0]);
        extractGadget(fileName);

        foreach (var gadget in Gadgets)
        {
          System.Console.WriteLine("address: 0x{0:x}, length: 0x{1:x}", gadget.Address, gadget.Length);

          // foreach (var byteValue in gadget.Content) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }
          // System.Console.WriteLine();

          // var encryptedArray = gadget.GetSelfEncryptedArray();
          // foreach (var byteValue in encryptedArray) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }

          // var password = new byte[] { 'a', 'z', 'e', 'r', 't', 'y' };
          gadget.MixWithPassword(System.Text.Encoding.ASCII.GetBytes("azerty"));
          // foreach (var byteValue in gadget.Content) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }

          var mixSignature = gadget.GetSelfEncryptedArray();
          foreach (var byteValue in mixSignature) {
            System.Console.Write("{0:x2} ", byteValue);
          }

//          gadget.FindPassword();

          System.Console.WriteLine();
        }

        // var elfReader32 = ELFSharp.ELF.ELFReader.Load<uint>(args[0]);
        // var segments = elfReader32.Segments;
        // foreach (var seg in segments) {
        //   System.Console.WriteLine("segment {0}: 0x{1:x}, 0x{2:x}", seg.Type.ToString(), seg.Address, seg.Offset);
        // }

        // var sections = elfReader32.Sections;
        // foreach (var sec in sections) {
        //   System.Console.WriteLine("section {0}", sec.Name);
        // }
      }
    }
  }
}
