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
				for (var j = 0; j < loopCounts[i]; j++)
				{
					output[i] = z3Ctxt.MkBVXOR(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
					output[i] = z3Ctxt.MkBVRotateLeft(rolOffsets[i], output[i]);
				}
				//output[i] = z3Ctxt.MkBVXOR(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
				//output[i] = z3Ctxt.MkBVRotateLeft(rolOffsets[i], output[i]);
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
					//output[i] = z3Ctxt.MkBVXOR(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
					output[i] = z3Ctxt.MkBVSub(output[i], z3Ctxt.MkBV(xorConsts[i], 32));
					output[i] = z3Ctxt.MkBVRotateRight(rorOffsets[i], output[i]);
				}
			}

			return output;
		}

		static Microsoft.Z3.BitVecExpr bit_reverse(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr bitVector)
		{
			var bv = bitVector;
			var const1 = z3Ctxt.MkBV(1, 32); var const2 = z3Ctxt.MkBV(2, 32);
			var const4 = z3Ctxt.MkBV(4, 32); var const8 = z3Ctxt.MkBV(8, 32); var const16 = z3Ctxt.MkBV(16, 32);

			bv = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0xaaaaaaaa, 32)), const1),
				z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0x55555555, 32)), const1));

			bv = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0xcccccccc, 32)), const2),
				z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0x33333333, 32)), const2));

			bv = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0xf0f0f0f0, 32)), const4),
				z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0x0f0f0f0f, 32)), const4));

			bv = z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0xff00ff00, 32)), const8),
				z3Ctxt.MkBVSHL(z3Ctxt.MkBVAND(bv, z3Ctxt.MkBV(0x00ff00ff, 32)), const8));

			return z3Ctxt.MkBVOR(z3Ctxt.MkBVLSHR(bv, const16),
				z3Ctxt.MkBVSHL(bv, const16));
		}

		static Microsoft.Z3.BitVecExpr[] process3(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] passwords)
		{
			var output = passwords.ToArray();
			uint[] loopCounts = { 0x28, 0x14b, 0xcd, 0x3a, 0x178, 0x35e };
			uint[] xorAddConsts = { 0x8fd5c5bd, 0x1f817abb, 0xe8504430, 0xa6258a12, 0x90bf3d8b, 0xc350be97 };

			for (var i = 0; i < 6; i++)
			{
				//if (loopCounts[i] % 2 != 0)
				//{
				//  output[i] = bit_reverse(ref z3Ctxt, output[i]);
				//}
				var constBv = z3Ctxt.MkBV(xorAddConsts[i], 32);
				for (var j = 0; j < loopCounts[i]; j++)
				{
					output[i] = bit_reverse(ref z3Ctxt, output[i]);
					output[i] = z3Ctxt.MkBVXOR(output[i], constBv);
					output[i] = z3Ctxt.MkBVAdd(output[i], constBv);
				}
			}

			return output;
		}

		// process4
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

		// process5
		static Microsoft.Z3.BitVecExpr[] process5(ref Microsoft.Z3.Context z3Ctxt, Microsoft.Z3.BitVecExpr[] output2, Microsoft.Z3.BitVecExpr[] output3)
		{
			var output = new Microsoft.Z3.BitVecExpr[6];
			for (var i = 0; i < 6; i++)
			{
				output[i] = z3Ctxt.MkBVXOR(bit_reverse(ref z3Ctxt, output3[i]), output2[i]);
			}

			return output;
		}

		// process6
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
			var z3Solver = z3Ctxt.MkSolver("QF_BV");

			var passwords = new Microsoft.Z3.BitVecExpr[6];
			for (var i = 0; i < passwords.Length; i++)
			{
				passwords[i] = z3Ctxt.MkBVConst("passwords" + i.ToString(), 32);
			}

			var asciiConds = new Microsoft.Z3.BoolExpr[6, 4];
			var minCharBv = z3Ctxt.MkBV(0x21, 8);
			var maxCharBv = z3Ctxt.MkBV(0x7e, 8);
			for (var p = 0; p < 6; p++)
			{
				for (uint i = 0; i < 4; i++)
				{
					var charOfPassword = z3Ctxt.MkExtract(i * 8 + 7, i * 8, passwords[p]);
					asciiConds[p, i] = z3Ctxt.MkAnd(new Microsoft.Z3.BoolExpr[]{ z3Ctxt.MkBVUGE(charOfPassword, minCharBv),
						z3Ctxt.MkBVULE(charOfPassword, maxCharBv) });
				}
			}

			var output0 = process0(ref z3Ctxt, passwords); // ok

			//var tmpCond = z3Ctxt.MkEq(output0[0], z3Ctxt.MkBV(0xa262730b, 32));
			//z3Solver.Assert(tmpCond);

			//Console.WriteLine("{0}", passwords[0].ToString());

			var output1 = process1(ref z3Ctxt, output0); // ok

			//var tmpCond = z3Ctxt.MkEq(output1[0], z3Ctxt.MkBV(0xd9ef05ab, 32));
			//z3Solver.Assert(tmpCond);

			//Console.WriteLine("{0}", output1[0].ToString());
			//Console.WriteLine("{0}", output1[1].ToString());

			var output2 = process2(ref z3Ctxt, output0); // ok

			//var tmpCond = z3Ctxt.MkEq(output2[0], z3Ctxt.MkBV(0x5c793783, 32));
			//z3Solver.Assert(tmpCond);

			//var result = z3Solver.Check();
			//Console.WriteLine("{0}", result.ToString());
			//if (result == Microsoft.Z3.Status.SATISFIABLE)
			//{
			//  Console.Write("Password: ");
			//  var model = z3Solver.Model;
			//  Console.Write("0x{0:x}", System.Convert.ToUInt32(model.Evaluate(passwords[0]).ToString()));
			//}

			var output3 = process3(ref z3Ctxt, output0); // ok

			//var tmpCond = z3Ctxt.MkEq(output3[0], z3Ctxt.MkBV(0x2a918342, 32));
			//z3Solver.Assert(tmpCond);

			var output4 = process4(ref z3Ctxt, output1, output2); // ok

			// var tmpCond = z3Ctxt.MkEq(output4[0], z3Ctxt.MkBV(0x85963228, 32));
			// z3Solver.Assert(tmpCond);

			var output5 = process5(ref z3Ctxt, output2, output3); // ok

			// var tmpCond = z3Ctxt.MkEq(output5[0], z3Ctxt.MkBV(0x1eb8bed7, 32));
			// z3Solver.Assert(tmpCond);

			var output6 = process6(ref z3Ctxt, output4, output5); // ok

			var checkingConds = new Microsoft.Z3.BoolExpr[6];
			uint[] compareConstants = { 0x73ae5f50, 0xbd2b6a91, 0x3e4e9687, 0xbcfaadcc, 0xcd2ca810, 0x9d26237e };
			for (var i = 0; i < 6; i++)
			{
				checkingConds[i] = z3Ctxt.MkEq(output6[i], z3Ctxt.MkBV(compareConstants[i], 32));
			}

			var password0Conds = new Microsoft.Z3.BoolExpr[1 + 4];
			password0Conds[0] = checkingConds[0];
			for (var i = 0; i < 4; i++)
			{
				password0Conds[i + 1] = asciiConds[0, i];
			}
			// z3Solver.Assert(password0Conds);

			var password1Conds = new Microsoft.Z3.BoolExpr[1 + 4];
			password1Conds[0] = checkingConds[1];
			for (var i = 0; i < 4; i++) 
			{
				password1Conds[i + 1] = asciiConds[1, i];
			}
			// z3Solver.Assert(password1Conds);

			var password2Conds = new Microsoft.Z3.BoolExpr[1 + 4];
			password2Conds[0] = checkingConds[2];
			for (var i = 0; i < 4; i++)
			{
				password2Conds[i + 1] = asciiConds[2, i];
			}
			// z3Solver.Assert(password2Conds);

			var password3Conds = new Microsoft.Z3.BoolExpr[1 + 4];
			password3Conds[0] = checkingConds[3];
			for (var i = 0; i < 4; i++)
			{
				password3Conds[i + 1] = asciiConds[3, i];
			}
			z3Solver.Assert(password3Conds);

			// var allConds = new Microsoft.Z3.BoolExpr[6 + 24];
			// var idx = 0;
			// foreach (var cond in checkingConds)
			// {
			//  allConds[idx] = cond;
			//  idx++;
			// }
			// foreach (var cond in asciiConds)
			// {
			//  allConds[idx] = cond;
			//  idx++;
			// }

			//z3Solver.Assert(checkingConds[0]);
			// z3Solver.Assert(allConds);

			//Console.WriteLine("{0}", z3Solver.ToString());

			//var uniqueConds = z3Ctxt.MkAnd(allConds);
			//var uniqueConds = z3Ctxt.MkAnd(password0Conds);
			System.IO.File.WriteAllText(@"passwords3_constraints.smt2", "(set-logic QF_BV)\n(set-info :smt-lib-version 2.0)\n(set-option :produce-models true)\n\n");
			System.IO.File.AppendAllText(@"passwords3_constraints.smt2", z3Solver.ToString());
			System.IO.File.AppendAllText(@"passwords3_constraints.smt2", "\n(check-sat)\n");
			// System.IO.File.AppendAllText(@"passwords_constraints.smt2", "(get-value (passwords0))\n");
			System.IO.File.AppendAllText(@"passwords3_constraints.smt2", "(get-value (passwords3))\n");
			// System.IO.File.AppendAllText(@"passwords_constraints.smt2", "(get-value (passwords2))\n");
			// System.IO.File.AppendAllText(@"passwords_constraints.smt2", "(get-value (passwords3))\n");
			// System.IO.File.AppendAllText(@"passwords_constraints.smt2", "(get-value (passwords4))\n");
			// System.IO.File.AppendAllText(@"passwords_constraints.smt2", "(get-value (passwords5))\n");

			//Console.WriteLine("{0}", "looking for the passwords[0]...");
			//var result = z3Solver.Check();
			//Console.WriteLine("{0}", result.ToString());

			//Console.WriteLine("{0}", checkingConds[0].ToString());

			// if (result == Microsoft.Z3.Status.SATISFIABLE) 
			// {

			// }
		}
	}
}