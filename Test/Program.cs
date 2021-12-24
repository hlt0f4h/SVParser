using Antlr4.Runtime;
using Antlr4.Runtime.Tree;
using System;
using System.IO;
using System.Security;

namespace Test {
    class Program {

        static AntlrInputStream ais;
        static CommonTokenStream cts;
        static SVLexer lexer;
        static SVParser parser;
        static ParserRuleContext prc;

        static void Main(string[] args) {
            try {
                if (args.Length == 1) {
                    // Single module
                    ais = new AntlrInputStream(new StreamReader(args[0]));
                    Console.Error.WriteLine("lex...");
                    lexer = new SVLexer(ais);
                    cts = new CommonTokenStream(lexer);
                    cts.Fill();

                    Console.Error.WriteLine("parse...");
                    parser = new SVParser(cts);
                    prc = parser.source_text();

                    Console.Error.WriteLine("output...");
                    PrintSyntaxTree(prc, 0);
                } else {
                    Console.WriteLine("Usage:");
                    Console.WriteLine("  SVTest <inputfile>");
                }
                
            } catch (Exception ex) {
                Console.Error.WriteLine("Error: " + ex.Message);
            }
        }
        
        static private void PrintSyntaxTree(IParseTree p, int level) {
            string s = p.GetType().ToString();
            if (p is ErrorNodeImpl) {
                //
            } else if (p is TerminalNodeImpl) {
                Console.WriteLine("<Terminal>" + SecurityElement.Escape(p.GetText()) + "</Terminal>");
            } else {
                string tag = s.Substring(s.IndexOf('+') + 1).Replace("Context", "");
                Console.Write("<" + tag);
                if (p.ChildCount > 0) {
                    Console.Write(">");
                    for (int i = 0; i < p.ChildCount; i++) {
                        PrintSyntaxTree(p.GetChild(i), level + 1);
                    }
                    Console.Write("</" + tag + ">");
                } else {
                    Console.Write(" />");
                }
            }
        }
    }
}
