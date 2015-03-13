package Semant;

import java.io.PrintWriter;

import Parse.Parse;

public class Main {

	public static void main(String argv[]) {

		for (int i = 0; i < argv.length; ++i) {
			String filename = "/Users/jack/Git/CSC4351P3/src/test.tig";
			if (argv.length > 1)
				System.out.println("***Processing: " + filename);
			Parse parse = new Parse(filename);
			Semant semant = new Semant(parse.errorMsg);
			semant.transProg(parse.absyn);
			PrintWriter writer = new PrintWriter(System.out);
			Absyn.Print printer = new Absyn.Print(writer);
			printer.prExp(parse.absyn, 0);
			writer.println();
			writer.flush();
		}
	}
}
