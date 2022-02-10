using Antlr4.Runtime;
using Antlr4.Runtime.Tree;
using System;
using System.IO;
using System.Security;

namespace SVTest {
    class Program {

        static AntlrInputStream ais;
        static CommonTokenStream cts;
        static SVLexer lexer;
        static SVParser parser;
        static ParserRuleContext prc;
        static int errCount = 0;

        static void Main(string[] args) {
            try {
                if (args.Length > 0) {
                    string fn;
                    if (args[0] == "-q") {
                        fn = args[1];
                    } else {
                        fn = args[0];
                    }
                    ais = new AntlrInputStream(new StreamReader(fn));

                    Console.Error.WriteLine("lex...");
                    lexer = new SVLexer(ais);
                    cts = new CommonTokenStream(lexer);
                    cts.Fill();
                    
                    Console.Error.WriteLine("parse...");
                    parser = new SVParser(cts);
                    prc = parser.source_text();
                    
                    if (args[0] != "-q") {
                        Console.Error.WriteLine("output...");
                        PrintTokens(cts);
                        PrintSyntaxTree(prc, 0);
                    } else {
                        CheckSyntaxTree(prc, 0);
                    }

                } else {
                    Console.WriteLine("Usage:");
                    Console.WriteLine("  SVTest <inputfile>");
                }
                
            } catch (Exception ex) {
                Console.Error.WriteLine("Error: " + ex.Message);
            }

            if (errCount > 0) {
                Console.Error.WriteLine("Error: " + errCount + " syntax error found.");
                Environment.Exit(-1);
            }
        }
        
        static private void PrintTokens(CommonTokenStream cts) {
            foreach (IToken tk in cts.GetTokens()) {
                Console.WriteLine("//" + SVLexer.DefaultVocabulary.GetSymbolicName(tk.Type) + "  " + tk.Text);
            }
        }

        static private void PrintSyntaxTree(IParseTree p, int level) {
            string s = p.GetType().ToString();
            if (p is ErrorNodeImpl) {
                errCount++;
            } else if (p is TerminalNodeImpl) {
                Console.WriteLine("<Terminal type=\"" + SVLexer.DefaultVocabulary.GetSymbolicName(((TerminalNodeImpl) p).Payload.Type) + "\">" + SecurityElement.Escape(p.GetText()) + "</Terminal>");
            } else {
                
                if (p.ChildCount > 0) {
                    string tag = s.Substring(s.IndexOf('+') + 1).Replace("Context", "");
                    Console.Write("<" + tag + ">");
                    for (int i = 0; i < p.ChildCount; i++) {
                        PrintSyntaxTree(p.GetChild(i), level + 1);
                    }
                    Console.Write("</" + tag + ">");
                }
            }
        }

        static private void CheckSyntaxTree(IParseTree p, int level) {
            string s = p.GetType().ToString();
            if (p is ErrorNodeImpl) {
                errCount++;
            } else if (p.ChildCount > 0) {
                for (int i = 0; i < p.ChildCount; i++) {
                    CheckSyntaxTree(p.GetChild(i), level + 1);
                }
            }
        }
    }
}
