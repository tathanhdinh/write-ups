using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace oneway
{
  class Program
  {
    private static void FindPassword(uint passwordLength)
    {
      var z3Ctxt = new Microsoft.Z3.Context();

      var passwordChars = new Microsoft.Z3.BitVecExpr[passwordLength];
      var asciiConds = new Microsoft.Z3.BoolExpr[passwordLength];
      for (var i = 0; i < passwordLength; i++)
      {
        passwordChars[i] = z3Ctxt.MkBVConst("password" + i.ToString(), 32);
        asciiConds[i] = z3Ctxt.MkAnd(z3Ctxt.MkBVUGE(passwordChars[i], z3Ctxt.MkBV(0x21, 32)), 
                                     z3Ctxt.MkBVULE(passwordChars[i], z3Ctxt.MkBV(0x7e, 32)));
      }

      //var accum = z3Ctxt.MkBV(0xdefec8ed, 32);
      Microsoft.Z3.BitVecExpr accum = z3Ctxt.MkBV(0xdefec8ed, 32);
      //var accum = z3Ctxt.MkBV()
      //var accum = z3Ctxt.MkBVConst("accumulator", 32);
      //var initCond = z3Ctxt.MkEq(accum, z3Ctxt.MkBV(0xdefec8ed, 32));

      foreach (var passChar in passwordChars)
      {
        accum = z3Ctxt.MkBVAdd(z3Ctxt.MkBVXOR(z3Ctxt.MkBVAdd(accum, passChar),
                                              z3Ctxt.MkBVSub(accum, passChar)), accum);
        accum = z3Ctxt.MkBVRotateLeft(8, accum);
      }
      var finalCond = z3Ctxt.MkEq(accum, z3Ctxt.MkBV(0xa2edc5c4, 32));

      var z3Solver = z3Ctxt.MkSolver("QF_BV");
      //z3Solver.Assert(new[] { initCond, finalCond });
      var allConds = new Microsoft.Z3.BoolExpr[passwordLength + 1];
      asciiConds.CopyTo(allConds, 0);
      allConds[passwordLength] = finalCond;
      z3Solver.Assert(allConds);

      var result = z3Solver.Check();
      Console.Write("{0}", result.ToString());
      if (result == Microsoft.Z3.Status.SATISFIABLE)
      {
        Console.Write("\nPassword: ");
        var model = z3Solver.Model;
        foreach (var passChar in passwordChars)
        {
          var passCharVal = Convert.ToUInt32(model.Evaluate(passChar).ToString());
          Console.Write("{0}", Convert.ToChar(passCharVal));
        }
      }
    }
    static void Main(string[] args)
    {
      if (args.Length < 1)
      {
        Console.WriteLine("Please give some length for the password. (e.g. oneway.exe some_length)");
      } 
      else
      {
        var passwordLength = System.Convert.ToUInt32(args[0]);
        Console.Write("Try with password length: {0}... ", passwordLength);
        FindPassword(passwordLength);
      }
    }
  }
}

// found passwords
// 1-7, 10: none
// 8:  xxEP_HH4
// 9:  J!Q!`P`0@
// 11: #!ih*I~LPz"
// 12: y_a/dk!Lb"-g
// 13: S(!fpP&2hIQ}'
// 14: A!?(*>`"(y@2ax
// 15: oF?&x}hA:`?p0}X
// 16: .!`&JD"Y?<1$x|\q
// 17: )!A,`0*Dl@a81@0?(
// 19: x!`sX"P@x"v'p3}>^dp
// 18: p!(|_FxXx@|x&x^2Hi
// 20: @!#R@!(`x|~LI`~hX)(a