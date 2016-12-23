using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace f4b_xor_w4kfu_keygen
{
  class Program
  {
    static Microsoft.Z3.BitVecExpr[] process0(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] passwords)
    {
      var output = new Microsoft.Z3.BitVecExpr[6];
      uint[] addConst = { 0x550342b8, 0xe3348f8b, 0x58c85bdd, 0x7406e41c, 0x72ece789, 0xefa2f7ec };

      for (var i = 0; i < 6; i++)
      {
        output[i] = z3Ctxt.MkBVAdd(passwords[i], z3Ctxt.MkBV(addConst[i], 32));
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr[] process1(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] passwords)
    {
      var output = passwords.ToArray();
      uint[] loopCounts = { 0x36d, 0x305, 0x1e6, 0x1d5, 0xcc, 0x25d };
      uint[] xorConsts = { 0x6dc555e2, 0x668471f5, 0x21f8a104, 0x0d665e60, 0x69fd3480, 0xe4b8c392 };
      uint[] rolOffsets = { 0x1f, 0x13, 0x10, 0x1a, 0x7, 0x12 };

      for (var i = 0; i < 6; i++)
      {
        output[i] = z3Ctxt.MkBVXOR(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
        output[i] = z3Ctxt.MkBVRotateLeft(rolOffsets[i], output[i]); 
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr[] process2(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] passwords)
    {
      var output = passwords.ToArray();
      uint[] loopCounts = { 0x6e, 0x20d, 0x1d7, 0x318, 0x2b, 0x234 };
      uint[] xorConsts = { 0xecf6d571, 0xec829194, 0x5c167e65, 0x3950cc83, 0x604dc3f2, 0x0b3799a2 };
      uint[] rorOffsets = { 0xe, 0x10, 0xd, 0x1e, 0x1, 0x19 };

      for (var i = 0; i < 6; i++)
      {
        for (var j = 0; j < loopCounts[i]; j++)
        {
          output[i] = z3Ctxt.MkBVXOR(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
          output[i] = z3Ctxt.MkBVRotateRight(rorOffsets[i], output[i]);
        }
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr bit_reverse(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr bitVector)
    {
      bitVector = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0xaaaaaaaa, 32)), z3Ctxt.MkBV(1, 32)),
                                       z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0x55555555, 32)), z3Ctxt.MkBV(1, 32)));
      bitVector = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0xcccccccc, 32)), z3Ctxt.MkBV(2, 32)),
                                   z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0x33333333, 32)), z3Ctxt.MkBV(2, 32)));
      bitVector = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0xf0f0f0f0, 32)), z3Ctxt.MkBV(4, 32)),
                                   z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0x0f0f0f0f, 32)), z3Ctxt.MkBV(4, 32)));
      bitVector = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0xff00ff00, 32)), z3Ctxt.MkBV(8, 32)),
                                   z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bitVector, z3Ctxt.MkBV(0x00ff00ff, 32)), z3Ctxt.MkBV(8, 32)));
      return z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(bitVector, z3Ctxt.MkBV(16, 32)),
                           z3Ctxt.MkBVSHL(bitVector, z3Ctxt.MkBV(16, 32)));
    }

    static Microsoft.Z3.BitVecExpr[] process3(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] passwords)
    {
      var output = passwords.ToArray();
      uint[] loopCounts = { 0x28, 0x14b, 0xcd, 0x3a, 0x178, 0x35e };

      for (var i = 0; i < 6; i++)
      {
        if (loopCounts[i] % 2 != 0)
        {
          output[i] = bit_reverse(ref z3Ctxt, output[i]);
        }
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr[] process4(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] output1, Microsoft.Z3.BitVecExpr[] output2)
    {
      //passwords[0] = z3Ctxt.MkBVXOR()
      var output = new Microsoft.Z3.BitVecExpr[6];
      uint[] rolOffsets = { 0x0, 0x1a, 0x8, 0xd, 0x10, 0x1e };
      for (var i = 0; i < 6; i++) 
      {
        output[i] = z3Ctxt.MkBVXOR(output2[i], z3Ctxt.MkBVRotateLeft(rolOffsets[i], output1[i]));
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr[] process5(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] output2, Microsoft.Z3.BitVecExpr[] output3)
    {
      var output = new Microsoft.Z3.BitVecExpr[6];
      for (var i = 0; i < 6; i++) 
      {
        output[i] = z3Ctxt.MkBVXOR(bit_reverse(ref z3Ctxt, output3[i]), output2[i]);
      }

      return output;
    }

    static Microsoft.Z3.BitVecExpr[] process6(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] output4, Microsoft.Z3.BitVecExpr[] output5)
    {
      var output = new Microsoft.Z3.BitVecExpr[6];
      for (var i = 0; i < 6; i++)
      {
        output[i] = bit_reverse(ref z3Ctxt, z3Ctxt.MkBVXOR(output5[i], z3Ctxt.MkBVRotateLeft(0x17, output4[i])));
      }

      return output;
    }

    static void Main(string[] args)
    {
      var z3Ctxt = new Microsoft.Z3.Context();

      var passwords = new Microsoft.Z3.BitVecExpr[6];
      for (var i = 0; i < passwords.Length; i++)
      {
        passwords[i] = z3Ctxt.MkBVConst("password" + i.ToString(), 32);
      }

      passwords = process0(ref z3Ctxt, passwords);
      var output1 = process1(ref z3Ctxt, passwords);
      var output2 = process2(ref z3Ctxt, passwords);
      var output3 = process3(ref z3Ctxt, passwords);
      var output4 = process4(ref z3Ctxt, output1, output2);
      var output5 = process5(ref z3Ctxt, output2, output3);
      var output6 = process6(ref z3Ctxt, output4, output5);

      var checkingConds = new Microsoft.Z3.BoolExpr[6];
      uint[] compareConstants = { 0x73ae5f50, 0xbd2b6a91, 0x3e4e9687, 0xbcfaadcc, 0xcd2ca810, 0x9d26237e };
      for (var i = 0; i < 6; i++) 
      {
        checkingConds[i] = z3Ctxt.MkEq(output6[i], z3Ctxt.MkBV(compareConstants[i], 32));
      }

      var asciiConds = new Microsoft.Z3.BoolExpr[6, 4];
      for (var i = 0; i < 4; i++)
      {
        
      }
    }
  }
}
