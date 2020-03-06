/*
 * IEEE 1800-2017 SystemVerilog
 * Lexer Rule
 *
 * [#00] 2018-12-19
 *
 * https://github.com/hlt0f4h/SVParser
 */

lexer grammar SVLexer;

// String
String_literal
  :  '"' SCharSequence? '"'
  ;

fragment SCharSequence
  :  SChar+
  ;

fragment SChar
  :  ~["\\\r\n]
  |  EscapeSequence
  |  '\\\n'   // Added line
  |  '\\\r\n' // Added line
  ;

fragment EscapeSequence
  :  SimpleEscapeSequence
  |  OctalEscapeSequence
  |  HexadecimalEscapeSequence
  |  UniversalCharacterName
  ;

fragment SimpleEscapeSequence
  :  '\\' ['"?abfnrtv\\]
  ;

fragment OctalEscapeSequence
  :  '\\' Octal_digit
  |  '\\' Octal_digit Octal_digit
  |  '\\' Octal_digit Octal_digit Octal_digit
  ;

fragment HexadecimalEscapeSequence
  :  '\\x' Hex_digit+
  ;

fragment UniversalCharacterName
  :  '\\u' Hex_digit Hex_digit Hex_digit Hex_digit
  |  '\\U' Hex_digit Hex_digit Hex_digit Hex_digit Hex_digit Hex_digit Hex_digit Hex_digit
  ;

// Compiler Directive
Compiler_directive
  : '`' .*? '\r'? '\n' -> channel (HIDDEN)
  ;

// Keyword
K_DL_root            : '$root'              ;
K_DL_unit            : '$unit'              ;
/*
K_DL_error           : '$error'             ;
K_DL_fatal           : '$fatal'             ;
K_DL_fullskew        : '$fullskew'          ;
K_DL_hold            : '$hold'              ;
K_DL_info            : '$info'              ;
K_DL_nochange        : '$nochange'          ;
K_DL_period          : '$period'            ;
K_DL_recovery        : '$recovery'          ;
K_DL_recrem          : '$recrem'            ;
K_DL_removal         : '$removal'           ;
K_DL_setup           : '$setup'             ;
K_DL_setuphold       : '$setuphold'         ;
K_DL_skew            : '$skew'              ;
K_DL_timeskew        : '$timeskew'          ;
K_DL_warning         : '$warning'           ;
K_DL_width           : '$width'             ;
*/
System_tf_identifier
  :  S_DL Any_Alpha_Num_Bar_Dol ( Any_Alpha_Num_Bar_Dol )*
  ;

K_begin              : 'begin'              ;
K_case               : 'case'               ;
K_casex              : 'casex'              ;
K_casez              : 'casez'              ;
K_checker            : 'checker'            ;
K_class              : 'class'              ;
K_clocking           : 'clocking'           ;
K_config             : 'config'             ;
K_covergroup         : 'covergroup'         ;
K_end                : 'end'                ;
K_endcase            : 'endcase'            ;
K_endchecker         : 'endchecker'         ;
K_endclass           : 'endclass'           ;
K_endclocking        : 'endclocking'        ;
K_endconfig          : 'endconfig'          ;
K_endfunction        : 'endfunction'        ;
K_endgenerate        : 'endgenerate'        ;
K_endgroup           : 'endgroup'           ;
K_endinterface       : 'endinterface'       ;
K_endmodule          : 'endmodule'          ;
K_endpackage         : 'endpackage'         ;
K_endprimitive       : 'endprimitive'       ;
K_endprogram         : 'endprogram'         ;
K_endproperty        : 'endproperty'        ;
K_endsequence        : 'endsequence'        ;
K_endspecify         : 'endspecify'         ;
K_endtable           : 'endtable'           ;
K_endtask            : 'endtask'            ;
K_function           : 'function'           ;
K_generate           : 'generate'           ;
K_interface          : 'interface'          ;
K_module             : 'module'             ;
K_package            : 'package'            ;
K_primitive          : 'primitive'          ;
K_program            : 'program'            ;
K_property           : 'property'           ;
K_sequence           : 'sequence'           ;
K_specify            : 'specify'            ;
K_table              : 'table'              ;
K_task               : 'task'               ;

K_DPI_C              : 'DPI-C'              ;
K_DPI                : 'DPI'                ;
K_PATHPULSE_DL       : 'PATHPULSE$'         ;
K_1step              : '1step'              ;
K_accept_on          : 'accept_on'          ;
K_alias              : 'alias'              ;
K_always             : 'always'             ;
K_always_comb        : 'always_comb'        ;
K_always_ff          : 'always_ff'          ;
K_always_latch       : 'always_latch'       ;
K_assert             : 'assert'             ;
K_assign             : 'assign'             ;
K_assume             : 'assume'             ;
K_before             : 'before'             ;
K_bind               : 'bind'               ;
K_bins               : 'bins'               ;
K_binsof             : 'binsof'             ;
K_break              : 'break'              ;
K_cell               : 'cell'               ;
K_constraint         : 'constraint'         ;
K_continue           : 'continue'           ;
K_cover              : 'cover'              ;
K_coverpoint         : 'coverpoint'         ;
K_cross              : 'cross'              ;
K_deassign           : 'deassign'           ;
K_default            : 'default'            ;
K_defparam           : 'defparam'           ;
K_design             : 'design'             ;
K_disable            : 'disable'            ;
K_dist               : 'dist'               ;
K_do                 : 'do'                 ;
K_else               : 'else'               ;
K_event              : 'event'              ;
K_eventually         : 'eventually'         ;
K_expect             : 'expect'             ;
K_export             : 'export'             ;
K_extends            : 'extends'            ;
K_extern             : 'extern'             ;
K_first_match        : 'first_match'        ;
K_for                : 'for'                ;
K_force              : 'force'              ;
K_foreach            : 'foreach'            ;
K_forever            : 'forever'            ;
K_fork               : 'fork'               ;
K_forkjoin           : 'forkjoin'           ;
K_global             : 'global'             ;
K_if                 : 'if'                 ;
K_iff                : 'iff'                ;
K_ifnone             : 'ifnone'             ;
K_ignore_bins        : 'ignore_bins'        ;
K_illegal_bins       : 'illegal_bins'       ;
K_implements         : 'implements'         ;
K_implies            : 'implies'            ;
K_import             : 'import'             ;
K_include            : 'include'            ;
K_initial            : 'initial'            ;
K_inside             : 'inside'             ;
K_instance           : 'instance'           ;
K_intersect          : 'intersect'          ;
K_join               : 'join'               ;
K_join_any           : 'join_any'           ;
K_join_none          : 'join_none'          ;
K_let                : 'let'                ;
K_liblist            : 'liblist'            ;
K_library            : 'library'            ;
K_local_CO_CO        : 'local::'            ;
K_macromodule        : 'macromodule'        ;
K_matches            : 'matches'            ;
K_modport            : 'modport'            ;
K_nettype            : 'nettype'            ;
K_new                : 'new'                ;
K_nexttime           : 'nexttime'           ;
K_noshowcancelled    : 'noshowcancelled'    ;
K_option             : 'option'             ;
K_priority           : 'priority'           ;
K_pulsestyle_ondetect: 'pulsestyle_ondetect';
K_pulsestyle_onevent : 'pulsestyle_onevent' ;
K_rand               : 'rand'               ;
K_randc              : 'randc'              ;
K_randcase           : 'randcase'           ;
K_randomize          : 'randomize'          ;
K_randsequence       : 'randsequence'       ;
K_reject_on          : 'reject_on'          ;
K_release            : 'release'            ;
K_repeat             : 'repeat'             ;
K_restrict           : 'restrict'           ;
K_return             : 'return'             ;
K_s_always           : 's_always'           ;
K_s_eventually       : 's_eventually'       ;
K_s_nexttime         : 's_nexttime'         ;
K_s_until            : 's_until'            ;
K_s_until_with       : 's_until_with'       ;
K_sample             : 'sample'             ;
K_showcancelled      : 'showcancelled'      ;
K_soft               : 'soft'               ;
K_solve              : 'solve'              ;
K_specparam          : 'specparam'          ;
K_std_CO_CO          : 'std::'              ;
K_strong             : 'strong'             ;
K_super              : 'super'              ;
K_sync_accept_on     : 'sync_accept_on'     ;
K_sync_reject_on     : 'sync_reject_on'     ;
K_this               : 'this'               ;
K_throughout         : 'throughout'         ;
K_timeprecision      : 'timeprecision'      ;
K_timeunit           : 'timeunit'           ;
K_type_option        : 'type_option'        ;
K_typedef            : 'typedef'            ;
K_unique             : 'unique'             ;
K_unique0            : 'unique0'            ;
K_until              : 'until'              ;
K_until_with         : 'until_with'         ;
K_untyped            : 'untyped'            ;
K_use                : 'use'                ;
K_wait               : 'wait'               ;
K_wait_order         : 'wait_order'         ;
K_weak               : 'weak'               ;
K_while              : 'while'              ;
K_wildcard           : 'wildcard'           ;
K_with               : 'with'               ;
K_within             : 'within'             ;

// Type
T_automatic          : 'automatic'          ;
T_bit                : 'bit'                ;
T_byte               : 'byte'               ;
T_chandle            : 'chandle'            ;
T_const              : 'const'              ;
T_context            : 'context'            ;
T_edge               : 'edge'               ;
T_enum               : 'enum'               ;
T_final              : 'final'              ;
T_genvar             : 'genvar'             ;
T_highz0             : 'highz0'             ;
T_highz1             : 'highz1'             ;
T_inout              : 'inout'              ;
T_input              : 'input'              ;
T_int                : 'int'                ;
T_integer            : 'integer'            ;
T_interconnect       : 'interconnect'       ;
T_large              : 'large'              ;
T_local              : 'local'              ;
T_localparam         : 'localparam'         ;
T_logic              : 'logic'              ;
T_longint            : 'longint'            ;
T_medium             : 'medium'             ;
T_negedge            : 'negedge'            ;
T_null               : 'null'               ;
T_output             : 'output'             ;
T_packed             : 'packed'             ;
T_parameter          : 'parameter'          ;
T_posedge            : 'posedge'            ;
T_protected          : 'protected'          ;
T_pull0              : 'pull0'              ;
T_pull1              : 'pull1'              ;
T_pure               : 'pure'               ;
T_real               : 'real'               ;
T_realtime           : 'realtime'           ;
T_ref                : 'ref'                ;
T_reg                : 'reg'                ;
T_scalared           : 'scalared'           ;
T_shortint           : 'shortint'           ;
T_shortreal          : 'shortreal'          ;
T_signed             : 'signed'             ;
T_small              : 'small'              ;
T_static             : 'static'             ;
T_string             : 'string'             ;
T_strong0            : 'strong0'            ;
T_strong1            : 'strong1'            ;
T_struct             : 'struct'             ;
T_supply0            : 'supply0'            ;
T_supply1            : 'supply1'            ;
T_tagged             : 'tagged'             ;
T_time               : 'time'               ;
T_tri                : 'tri'                ;
T_tri0               : 'tri0'               ;
T_tri1               : 'tri1'               ;
T_triand             : 'triand'             ;
T_trior              : 'trior'              ;
T_trireg             : 'trireg'             ;
T_type               : 'type'               ;
T_union              : 'union'              ;
T_unsigned           : 'unsigned'           ;
T_uwire              : 'uwire'              ;
T_var                : 'var'                ;
T_vectored           : 'vectored'           ;
T_virtual            : 'virtual'            ;
T_void               : 'void'               ;
T_wand               : 'wand'               ;
T_weak0              : 'weak0'              ;
T_weak1              : 'weak1'              ;
T_wire               : 'wire'               ;
T_wor                : 'wor'                ;

// Keyword
K_and                : 'and'                ;
K_buf                : 'buf'                ;
K_bufif0             : 'bufif0'             ;
K_bufif1             : 'bufif1'             ;
K_cmos               : 'cmos'               ;
K_nand               : 'nand'               ;
K_nmos               : 'nmos'               ;
K_nor                : 'nor'                ;
K_not                : 'not'                ;
K_notif0             : 'notif0'             ;
K_notif1             : 'notif1'             ;
K_or                 : 'or'                 ;
K_pmos               : 'pmos'               ;
K_pulldown           : 'pulldown'           ;
K_pullup             : 'pullup'             ;
K_rcmos              : 'rcmos'              ;
K_rnmos              : 'rnmos'              ;
K_rpmos              : 'rpmos'              ;
K_rtran              : 'rtran'              ;
K_rtranif0           : 'rtranif0'           ;
K_rtranif1           : 'rtranif1'           ;
K_tran               : 'tran'               ;
K_tranif0            : 'tranif0'            ;
K_tranif1            : 'tranif1'            ;
K_xnor               : 'xnor'               ;
K_xor                : 'xor'                ;

// Symbol
S_SQ                 : '\''                 ;
S_MI                 : '-'                  ;
S_MI_MI              : '--'                 ;
S_EX                 : '!'                  ;
S_EX_EQ              : '!='                 ;
S_EX_EQ_QU           : '!=?'                ;
S_EX_EQ_EQ           : '!=='                ;
S_SH                 : '#'                  ;
S_SH_0               : '#0'                 ;
S_SH_SH              : '##'                 ;
S_SH_MI_SH           : '#-#'                ;
S_SH_SH_LK_AS_RK     : '##[*]'              ;
S_SH_SH_LK_PL_RK     : '##[+]'              ;
S_SH_EQ_SH           : '#=#'                ;
S_DL                 : '$'                  ;
S_PE                 : '%'                  ;
S_PE_EQ              : '%='                 ;
S_AN                 : '&'                  ;
S_AN_AN              : '&&'                 ;
S_AN_AN_AN           : '&&&'                ;
S_AN_EQ              : '&='                 ;
S_LM                 : '('                  ;
S_LM_AS              : '(*'                 ;
S_LM_AS_RM           : '(*)'                ;
S_RM                 : ')'                  ;
S_AS                 : '*'                  ;
S_AS_RM              : '*)'                 ;
S_AS_AS              : '**'                 ;
S_AS_CO_CO_AS        : '*::*'               ;
S_AS_EQ              : '*='                 ;
S_AS_RB              : '*>'                 ;
S_CM                 : ','                  ;
S_DT                 : '.'                  ;
S_DT_AS              : '.*'                 ;
S_DV                 : '/'                  ;
S_DV_EQ              : '/='                 ;
S_CO                 : ':'                  ;
S_MI_CO              : '-:'                 ;
S_CO_DV              : ':/' ~'/'            ;
S_CO_CO              : '::'                 ;
S_CO_EQ              : ':='                 ;
S_SC                 : ';'                  ;
S_QU                 : '?'                  ;
S_AT                 : '@'                  ;
S_AT_AS              : '@*'                 ;
S_AT_AT              : '@@'                 ;
S_AT_AT_LM           : '@@('                ;
S_LK                 : '['                  ;
S_LK_AS              : '[*'                 ;
S_LK_AS_RK           : '[*]'                ;
S_LK_PL_RK           : '[+]'                ;
S_LK_EQ              : '[='                 ;
S_LK_MI_RB           : '[->'                ;
S_RK                 : ']'                  ;
S_XO                 : '^'                  ;
S_XO_NE              : '^~'                 ;
S_XO_EQ              : '^='                 ;
S_UB                 : '_'                  ;
S_LN                 : '{'                  ;
S_SQ_LN              : '\'{'                ;
S_OR                 : '|'                  ;
S_OR_OR              : '||'                 ;
S_OR_EQ              : '|='                 ;
S_OR_EQ_RB           : '|=>'                ;
S_OR_MI_RB           : '|->'                ;
S_RN                 : '}'                  ;
S_NE                 : '~'                  ;
S_NE_AN              : '~&'                 ;
S_NE_OR              : '~|'                 ;
S_NE_XO              : '~^'                 ;
S_PL                 : '+'                  ;
S_PL_CO              : '+:'                 ;
S_PL_PL              : '++'                 ;
S_PL_EQ              : '+='                 ;
S_LB                 : '<'                  ;
S_LB_LB              : '<<'                 ;
S_LB_LB_LB           : '<<<'                ;
S_LB_LB_LB_EQ        : '<<<='               ;
S_LB_LB_EQ           : '<<='                ;
S_LB_EQ              : '<='                 ;
S_LB_MI_RB           : '<->'                ;
S_EQ                 : '='                  ;
S_MI_EQ              : '-='                 ;
S_EQ_EQ              : '=='                 ;
S_EQ_EQ_QU           : '==?'                ;
S_EQ_EQ_EQ           : '==='                ;
S_EQ_RB              : '=>'                 ;
S_RB                 : '>'                  ;
S_MI_RB              : '->'                 ;
S_RB_EQ              : '>='                 ;
S_RB_RB              : '>>'                 ;
S_MI_RB_RB           : '->>'                ;
S_RB_RB_EQ           : '>>='                ;
S_RB_RB_RB           : '>>>'                ;
S_RB_RB_RB_EQ        : '>>>='               ;

// Number
Decimal_base_number
  : Decimal_base Unsigned_number
  | Decimal_base X_digit ( S_UB )*
  | Decimal_base Z_digit ( S_UB )*
  ;

Binary_base_number
  : Binary_base Binary_value
  ;

Octal_base_number
  : Octal_base Octal_value
  ;

Hex_base_number
  : Hex_base Hex_value
  ;

Exp_number
  : Unsigned_number ( S_DT Unsigned_number )? Exp ( Sign )? Unsigned_number
  ;

Fixed_point_number
  : Unsigned_number S_DT Unsigned_number
  ;

Unsigned_number
  :  Decimal_digit ( S_UB | Decimal_digit )*
  ;

fragment Sign
  :  S_PL | S_MI
  ;

fragment Exp
  :  'e' | 'E'
  ;

fragment Binary_value
  :  Binary_xz_digit ( S_UB | Binary_xz_digit )*
  ;

fragment Octal_value
  :  Octal_xz_digit ( S_UB | Octal_xz_digit )*
  ;

fragment Hex_value
  :  Hex_xz_digit ( S_UB | Hex_xz_digit )*
  ;

fragment Decimal_base
  :  S_SQ ( 's' | 'S' )? 'd'
  |  S_SQ ( 's' | 'S' )? 'D'
  ;

fragment Binary_base
  :  S_SQ ( 's' | 'S' )? 'b'
  |  S_SQ ( 's' | 'S' )? 'B'
  ;

fragment Octal_base
  :  S_SQ ( 's' | 'S' )? 'o'
  |  S_SQ ( 's' | 'S' )? 'O'
  ;

fragment Hex_base
  :  S_SQ ( 's' | 'S' )? 'h'
  |  S_SQ ( 's' | 'S' )? 'H'
  ;

fragment Decimal_digit
  :  '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
  ;

fragment Binary_xz_digit
  :  X_digit | Z_digit | '0' | '1'
  ;

fragment Octal_xz_digit
  :  X_digit | Z_digit | Octal_digit
  ;

fragment Octal_digit
  :  '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7'
  ;

fragment Hex_xz_digit
  :  X_digit | Z_digit | Hex_digit
  ;

fragment Hex_digit
  :  '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'A' | 'B' | 'C' | 'D' | 'E' | 'F'
  ;

fragment X_digit
  :  'x' | 'X'
  ;

fragment Z_digit
  :  'z' | 'Z' | S_QU
  ;

Unbased_unsized_literal
  :  '\'0' | '\'1' | '\'z_or_x'
  ;

// Time
Time_literal
  :  Unsigned_number Time_unit
  |  Fixed_point_number Time_unit
  ;

fragment Time_unit
  :  's' | 'ms' | 'us' | 'ns' | 'ps' | 'fs'
  ;

// Identifier
Simple_identifier
  :   Any_Alpha_Bar ( Any_Alpha_Num_Bar_Dol )*
  ;

Escaped_identifier
  :  '\\' ( Any_printable_ASCII_character_except_white_space )*
  ;

fragment Any_Alpha_Bar
  :  [a-zA-Z_]
  ;

fragment Any_Alpha_Num_Bar
  :  [a-zA-Z0-9_]
  ;

fragment Any_Alpha_Num_Bar_Dol
  :  [a-zA-Z0-9_$]
  ;

fragment Any_printable_ASCII_character_except_white_space
  : ~[ \r\t\n]
  ;
/*
fragment Any_ASCII_Characters
  :  ('\u0021'..'\u007E')+
  ;
*/
White_space
  : [ \t\n\r] + -> channel (HIDDEN)
  ;

Block_comment
  : '/*' .*? '*/' -> channel (HIDDEN)
  ;

One_line_comment
  : '//' .*? '\r'? '\n' -> channel (HIDDEN)
  ;
