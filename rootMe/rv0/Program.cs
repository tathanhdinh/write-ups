using System;

namespace rv0
{
	class MainClass
	{
		public static void Main (string[] args)
		{
			if (args.Length == 0) {
				System.Console.WriteLine("Please give an input argument. (e.g. ./rv0 input_argument)");
			}
			else {
				var accValue = 0xdefec8edU;
				var inputArg = args[0];
				foreach (var c in inputArg) {
					var cUint = Convert.ToUInt32(c);
					accValue = ((accValue + cUint) ^ (accValue - cUint)) + accValue;
					// System.Console.WriteLine("accValue = 0x{0:x} (before rotate)", accValue);
					accValue = (accValue << 8) | (accValue >> 24);					
				}
				System.Console.WriteLine("accValue = 0x{0:x}", accValue);
				System.Console.WriteLine("{0:s}", (accValue == 0xa2edc5c4U) ? "Bravo, you got the key!!!" : "Try again, please :-)"); 
			}
		}
	}
}
