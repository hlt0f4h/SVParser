# SVParser

SystemVerilog Lexer and Parser created by ANTLR4.

Note:
  - This version has not been fully tested, and does not properly support IEEE 1800-2017.
  - I'm using Visual Studio Express 2017 for Windows Desktop (C#) and Antlr4 NuGet package v4.6.6.

Known Issues:
  - SVLexer [#00]
    - If there is a comment start immediately after the colon of the ternary operator (e.g. "X <= A ? B :/* comment */ C;"), it will fail.
    - Does not support macros, compiler directives, system tasks.
	
  - SVParser [#00]
    - The following syntax is not supported:
	    - 6.24 Casting (cast, constant_cast)
	    - 20.11 Elaboration system tasks ($fatal, $error,...)
	    - 29 User-defined primitives (primitive)
	    - 31 Timing checks ($setup, $hold, ...)
	    - method_call_root ::= primary
