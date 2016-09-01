namespace readelf
{
	class MainClass
	{
		public static void Main (string[] args)
		{
			var shouldParseSections = false;
			var shouldParseSegments = false;
			var fileName = "";

			var options = new Mono.Options.OptionSet {
				{ "f|file", "input ELF file", fileOpt => fileName = fileOpt },
				{ "segs|segments", "parse segments", segOpt => shouldParseSegments = (segOpt != null) },
				{ "secs|sections", "parse sections", secOpt => shouldParseSections = (secOpt != null) }
			};

			// Console.WriteLine ("Hello World!");
			var fileList = options.Parse(args);

			if (fileList.Count == 0) {
				System.Console.WriteLine("please give an input ELF file");
			}
			else {
				fileName = fileList[0];
				var elfReader = ELFSharp.ELF.ELFReader.Load(fileName);
				
				// parse segments
				if (shouldParseSegments) {
          var segments = elfReader.Segments;
					var segmentNumber = 0;
					foreach (var seg in segments) {
						System.Console.WriteLine("segment {0}", seg.Type.ToString());
						segmentNumber++;
					}
					System.Console.WriteLine("{0} segment parsed.", segmentNumber);
				}

				// parse sections
				if (shouldParseSections) {
					var sections = elfReader.Sections;
					var sectionNumber = 0;
					foreach (var sec in sections) {
						System.Console.WriteLine("section {0}", sec.Name);
						sectionNumber++;
					}
					System.Console.WriteLine("{0} section parsed.", sectionNumber);
				}
			}
		}
	}
}
