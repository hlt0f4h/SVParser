# SVParser

SystemVerilog Lexer and Parser created by ANTLR4.

Note:
  - This version has not been fully tested, and does not properly support IEEE 1800-2017.
  - I'm using Visual Studio Express 2017 for Windows Desktop (C#) and Antlr4 NuGet package v4.6.6.

Known Issues:
  - SVLexer
    - Does not support macros, compiler directives, system tasks.
	
  - SVParser
    - There are still many syntaxes that cannot be parsed correctly.
      The results of running the following tests in a my local environment were 84% (883/1046).
      https://github.com/chipsalliance/sv-tests/tree/master/tests
