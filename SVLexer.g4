/*
 * IEEE 1800-2017 SystemVerilog
 * Lexer Rule
 *
 * [#01] 2022-01-22
 *
 * https://github.com/hlt0f4h/SVParser
 */

lexer grammar SVLexer;

channels {
  COMMENTS_CH
}

// String literal
L_String
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
  
// Macro Keywords
Compiler_directive
  : '`' .*? '\r'? '\n' -> channel (HIDDEN)
  ;
/*
M___FILE__           : '`__FILE__'            ;
M___LINE__           : '`__LINE__'            ;
M_begin_keywords     : '`begin_keywords'      ;
M_cell_define        : '`cell_define'         ;
M_default_nettype    : '`default_nettype'     ;
M_define             : '`define'              ;
M_else               : '`else'                ;
M_elsif              : '`elsif'               ;
M_end_cell_define    : '`end_cell_define'     ;
M_end_keywords       : '`end_keywords'        ;
M_endif              : '`endif'               ;
M_ifdef              : '`ifdef'               ;
M_ifndef             : '`ifndef'              ;
M_include            : '`include'             ;
M_line               : '`line'                ;
M_nounconnected_drive: '`nounconnected_drive' ;
M_pragma             : '`pragma'              ;
M_timescale          : '`timescale'           ;
M_unconnected_drive  : '`unconnected_drive'   ;
M_undef              : '`undef'               ;
M_undefineall        : '`undefineall'         ;
I_Text_macro
  :  S_BQ Any_Alpha_Bar ( Any_Alpha_Num_Bar_Dol )*
  |  S_BQ '\\' ( Any_printable_ASCII_character_except_white_space )*
  ;
*/

// System task Keywords
D_root            : '$root'                ;
D_unit            : '$unit'                ;
D_error           : '$error'               ;
D_fatal           : '$fatal'               ;
D_fullskew        : '$fullskew'            ;
D_hold            : '$hold'                ;
D_info            : '$info'                ;
D_nochange        : '$nochange'            ;
D_period          : '$period'              ;
D_recovery        : '$recovery'            ;
D_recrem          : '$recrem'              ;
D_removal         : '$removal'             ;
D_setup           : '$setup'               ;
D_setuphold       : '$setuphold'           ;
D_skew            : '$skew'                ;
D_timeskew        : '$timeskew'            ;
D_warning         : '$warning'             ;
D_width           : '$width'               ;
I_System_tf
  :  S_DL Any_Alpha_Num_Bar_Dol ( Any_Alpha_Num_Bar_Dol )*
  ;

// Block Keywords
B_begin              : 'begin'              ;
B_case               : 'case'               ;
B_casex              : 'casex'              ;
B_casez              : 'casez'              ;
B_checker            : 'checker'            ;
B_class              : 'class'              ;
B_clocking           : 'clocking'           ;
B_config             : 'config'             ;
B_covergroup         : 'covergroup'         ;
B_end                : 'end'                ;
B_endcase            : 'endcase'            ;
B_endchecker         : 'endchecker'         ;
B_endclass           : 'endclass'           ;
B_endclocking        : 'endclocking'        ;
B_endconfig          : 'endconfig'          ;
B_endfunction        : 'endfunction'        ;
B_endgenerate        : 'endgenerate'        ;
B_endgroup           : 'endgroup'           ;
B_endinterface       : 'endinterface'       ;
B_endmodule          : 'endmodule'          ;
B_endpackage         : 'endpackage'         ;
B_endprimitive       : 'endprimitive'       ;
B_endprogram         : 'endprogram'         ;
B_endproperty        : 'endproperty'        ;
B_endsequence        : 'endsequence'        ;
B_endspecify         : 'endspecify'         ;
B_endtask            : 'endtask'            ;
B_function           : 'function'           ;
B_generate           : 'generate'           ;
B_interface          : 'interface'          ;
B_macromodule        : 'macromodule'        ;
B_module             : 'module'             ;
B_package            : 'package'            ;
B_primitive          : 'primitive'          ;
B_program            : 'program'            ;
B_property           : 'property'           ;
B_sequence           : 'sequence'           ;
B_specify            : 'specify'            ;
B_table              : 'table'              -> mode(UDP);
B_task               : 'task'               ;

// Statement Keywords
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

// Type Keywords
T_automatic          : 'automatic'          ;
T_bit                : 'bit'                ;
T_byte               : 'byte'               ;
T_chandle            : 'chandle'            ;
T_const              : 'const'              ;
T_context            : 'context'            ;
T_edge               : 'edge'               -> pushMode(EDGE);
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

// Other keyword
O_and                : 'and'                ;
O_buf                : 'buf'                ;
O_bufif0             : 'bufif0'             ;
O_bufif1             : 'bufif1'             ;
O_cmos               : 'cmos'               ;
O_nand               : 'nand'               ;
O_nmos               : 'nmos'               ;
O_nor                : 'nor'                ;
O_not                : 'not'                ;
O_notif0             : 'notif0'             ;
O_notif1             : 'notif1'             ;
O_or                 : 'or'                 ;
O_pmos               : 'pmos'               ;
O_pulldown           : 'pulldown'           ;
O_pullup             : 'pullup'             ;
O_rcmos              : 'rcmos'              ;
O_rnmos              : 'rnmos'              ;
O_rpmos              : 'rpmos'              ;
O_rtran              : 'rtran'              ;
O_rtranif0           : 'rtranif0'           ;
O_rtranif1           : 'rtranif1'           ;
O_tran               : 'tran'               ;
O_tranif0            : 'tranif0'            ;
O_tranif1            : 'tranif1'            ;
O_xnor               : 'xnor'               ;
O_xor                : 'xor'                ;

N_Unbased_unsized
  : '\'0' | '\'1' | '\'z_or_x'
  ;

// Symbols
S_BQ				 : '`'                  ;
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
S_CO_DV              : ':/' ~[/*]           ;
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
N_Dec
  : Decimal_base N_Unsigned
  | Decimal_base X_digit ( S_UB )*
  | Decimal_base Z_digit ( S_UB )*
  ;

N_Bin
  : Binary_base Binary_value
  ;

N_Oct
  : Octal_base Octal_value
  ;

N_Hex
  : Hex_base Hex_value
  ;

N_Exp
  : N_Unsigned ( S_DT N_Unsigned )? Exp ( Sign )? N_Unsigned
  ;

N_Fix
  : N_Unsigned S_DT N_Unsigned
  ;

N_Unsigned
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
 
fragment Z
  :  'z' | 'Z'
  ;

fragment X
  :  'x' | 'X'
  ;

// Time literal
L_Time
  :  N_Unsigned Time_unit
  |  N_Fix Time_unit
  ;

fragment Time_unit
  :  's' | 'ms' | 'us' | 'ns' | 'ps' | 'fs'
  ;

// Identifier
I_Escaped
  :  '\\' ( Any_printable_ASCII_character_except_white_space )*
  ;

I_Simple
  :  Any_Alpha_Bar ( Any_Alpha_Num_Bar_Dol )*
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
  
// White Space
// Numbers can be aligned with spaces
WS
  : [ \t\n\r]+ -> skip
  ;

// Comments
C_Block
  : '/*' .*? '*/' -> channel(COMMENTS_CH)
  ;

C_Line
  : '//' .*? '\r'? '\n' -> channel(COMMENTS_CH)
  ;
  
//------------------------------------------------------------------
mode UDP;

S_Level
  :  '0' | '1' | 'X' | 'x' | '?' | 'b' | 'B'
  ;

S_Edge
  :  'r' | 'R' | 'f' | 'F' | 'p' | 'P' | 'n' | 'N' | '*'
  ;

S_CO_EDGE : ':' ;
S_SC_EDGE : ';' ;
S_LM_EDGE : '(' ;
S_RM_EDGE : ')' ;
S_MI_EDGE : '-' ;

B_endtable
  : 'endtable' -> mode(DEFAULT_MODE) ;
  
WS_UDP
  : [ \t\n\r]+ -> skip
  ;

C_Block_UDP
  : '/*' .*? '*/' -> channel(COMMENTS_CH)
  ;

C_Line_UDP
  : '//' .*? '\r'? '\n' -> channel(COMMENTS_CH)
  ;

//------------------------------------------------------------------
mode EDGE;

S_ZO_OZ
  : '01' | '10'
  ;

S_Z_O
  :  '0' | '1'
  ;

S_Z_X
  :  'z' | 'Z' | 'x' | 'X'
  ;

S_CM_EDGE
  : ','
  ;

S_RK_EDGE
  : ']' -> popMode
  ;
  
S_ID_EDGE
  : . -> more, popMode
  ;
  
WS_EDGE
  : [ \t\n\r]+ -> skip
  ;

C_Block_EDGE
  : '/*' .*? '*/' -> channel(COMMENTS_CH)
  ;

C_Line_EDGE
  : '//' .*? '\r'? '\n' -> channel(COMMENTS_CH)
  ;
  