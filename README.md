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
      The results of running the following tests in a my local environment were 85% (898/1046).
      https://github.com/chipsalliance/sv-tests/tree/master/tests

History:
  - [#00] 2018-12-19
    - Initial release.
  - [#01] 2022-01-22 (84%)
    - Support UDP.
    - Support left recursion in some expressions.
    - Renamed lexical terms for ease of color coding in the editor.
  - [#02] 2022-04-19 (85%)
    - Fix handling of spaces between radix and numbers.
    - Fix erroneous definition of unbased_unsized_literal.
    - Fix handling of identifiers or reserved words 'sample'.
