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

    public void MixWithPassword(string password)
    {
      // var passwordArray System.Text.Encoding.ASCII.GetBytes(samplePassword)
      var passwdIdx = 0;
      for (var i = 0; i < Content.Length; i++) {
        if (passwdIdx == password.Length) passwdIdx = 0;
        Content[i] = (byte)((Content[i] ^ password[passwdIdx]) - 0xaaU);
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

    public void FindPassword(uint passwordLength)
    {
      // password as bitvectors of 8 bits
      var z3Ctxt = new Microsoft.Z3.Context();
      Microsoft.Z3.BitVecExpr[] passwords = new Microsoft.Z3.BitVecExpr[passwordLength];
      for (var i = 0; i < passwordLength; i++) {
        var passwordNameI = "password" + i.ToString();
        passwords[i] = z3Ctxt.MkBVConst(passwordNameI, 8);
      }

      var gadgetSymbolicContent = new Microsoft.Z3.BitVecExpr[Content.Length];
      for (var i = 0; i < Content.Length; i++) {
        gadgetSymbolicContent[i] = z3Ctxt.MkBV(Content[i], 8);
      }

      // calculate gadget's symbolic content in mixing with the password
      var passwdIdx = 0;
      for (var i = 0; i < Content.Length; ++i) {
        if (passwdIdx == passwordLength) passwdIdx = 0;

        gadgetSymbolicContent[i] = z3Ctxt.MkBVSub(z3Ctxt.MkBVXOR(gadgetSymbolicContent[i], passwords[passwdIdx]),
          z3Ctxt.MkBV(0xaaU, 8));

        // System.Console.WriteLine("{0}", gadgetSymbolicContent[i].ToString());
        passwdIdx++;
      }

      // calculate self-scrambing vector
      var encryptedVector = new Microsoft.Z3.BitVecExpr[0xc];
      for (var i = 0; i < 0xc; ++i) {
        encryptedVector[i] = z3Ctxt.MkBV(0x0U, 8);
      }
      var vectorIdx = 0;
      foreach (var bv in gadgetSymbolicContent) {
        if (vectorIdx == 0xc) vectorIdx = 0x0;
        encryptedVector[vectorIdx] = z3Ctxt.MkBVXOR(encryptedVector[vectorIdx], bv);
        // System.Console.WriteLine("{0}", encryptedVector[vectorIdx].ToString());
        vectorIdx++;
      }

      // generate conditions
      var bvCheckingConds = new Microsoft.Z3.BoolExpr[0xc];
      for (var i = 0; i < 0xc; ++i) {
        bvCheckingConds[i] = z3Ctxt.MkEq(encryptedVector[i], z3Ctxt.MkBV(Signature[i], 8));
        // System.Console.WriteLine("{0}", bvCheckingConds[i].ToString());
      }
      // bvConds.Aggregate(z3Ctxt.MkAnd);

      var asciiConds = new Microsoft.Z3.BoolExpr[passwordLength];
      for (var i = 0; i < asciiConds.Length; ++i) {
        asciiConds[i] = z3Ctxt.MkAnd(z3Ctxt.MkBVUGE(passwords[i], z3Ctxt.MkBV(0x21, 8)),
          z3Ctxt.MkBVULE(passwords[i], z3Ctxt.MkBV(0x7e, 8)));
        // System.Console.WriteLine("{0}", asciiConds[i].ToString());
      }

      var allConds = new Microsoft.Z3.BoolExpr[bvCheckingConds.Length + asciiConds.Length];
      System.Array.Copy(bvCheckingConds, allConds, bvCheckingConds.Length);
      System.Array.Copy(asciiConds, 0, allConds, bvCheckingConds.Length, asciiConds.Length);

      // System.Console.WriteLine("{0}", z3Ctxt.MkAdd(allConds));

      // System.Console.WriteLine("condition expression: {0}", allConds.ToString());

      // var aggrCond = z3Ctxt.MkAnd(bvConds);
      var z3Solver = z3Ctxt.MkSolver("QF_BV");
      z3Solver.Assert(allConds);

      var gadgetSmtFile = new System.IO.StreamWriter(Address.ToString() + ".smt2");
      gadgetSmtFile.WriteLine("(set-logic QF_BV)");
      gadgetSmtFile.WriteLine("(set-info :smt-lib-version 2.0)");
      gadgetSmtFile.WriteLine(z3Solver.ToString());
      gadgetSmtFile.WriteLine("(check-sat)");
      gadgetSmtFile.Close();

      // System.Console.WriteLine("{0}", z3Solver.ToString());

      // var result = z3Solver.Check();
      // System.Console.WriteLine("{0}", result);
      // if (System.String.Equals(result, "UNSATISFIABLE", System.StringComparison.OrdinalIgnoreCase) return;
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
      if (args.Length < 2)
      {
        System.Console.WriteLine("Not correct syntax (e.g. ./ch12.exe samplePassword passwordLength)");
      }
      else
      {
        var samplePassword = args[0];
        var passwordLength = System.Convert.ToUInt32(args[1]);

        System.Console.WriteLine("Sample password: {0}", samplePassword);
        System.Console.WriteLine("Try with password length: {0}", passwordLength);
        System.Console.WriteLine();

        extractGadget("ch12");

        //extractGadget("ch12");

        foreach (var gadget in Gadgets)
        {
          System.Console.WriteLine("address: 0x{0:x}, length: 0x{1:x}", gadget.Address, gadget.Length);
          System.Console.Write("signature: ");
          foreach (var byteValue in gadget.Signature)
          {
            System.Console.Write("{0:x2} ", byteValue);
          }
          System.Console.WriteLine();

          // foreach (var byteValue in gadget.Content) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }
          // System.Console.WriteLine();

          // var encryptedArray = gadget.GetSelfEncryptedArray();
          // foreach (var byteValue in encryptedArray) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }

          // var password = new byte[] { 'a', 'z', 'e', 'r', 't', 'y' };
          // gadget.MixWithPassword(System.Text.Encoding.ASCII.GetBytes(samplePassword));
          // gadget.MixWithPassword(samplePassword);
          // foreach (var byteValue in gadget.Content) {
          //   System.Console.Write("{0:x2} ", byteValue);
          // }

          // var mixSignature = gadget.GetSelfEncryptedArray();
          // System.Console.Write("scrambled: ");
          // foreach (var byteValue in mixSignature)
          // {
          //  System.Console.Write("{0:x2} ", byteValue);
          // }
          // System.Console.WriteLine();

          gadget.FindPassword(passwordLength);

          // System.Console.WriteLine();
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