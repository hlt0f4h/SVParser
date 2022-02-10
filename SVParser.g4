/*
 * IEEE 1800-2017 SystemVerilog
 * Parser Rule
 *
 * [#01] 2022-01-22
 *
 * https://github.com/hlt0f4h/SVParser
 */

parser grammar SVParser;

options {
	tokenVocab=SVLexer;
}


// A.1.2 SystemVerilog source text

source_text
  :   ( timeunits_declaration )? ( description )* EOF
  ;

description 
  :  module_declaration
  |  udp_declaration
  |  interface_declaration
  |  program_declaration
  |  package_declaration
  |  ( attribute_instance )* package_item
  |  ( attribute_instance )* bind_directive
  |  config_declaration
  ;

module_nonansi_header 
  :  ( attribute_instance )* module_keyword ( lifetime )? module_identifier ( package_import_declaration )* ( parameter_port_list )? list_of_ports S_SC
  ;

module_ansi_header 
  :  ( attribute_instance )* module_keyword ( lifetime )? module_identifier ( package_import_declaration )* ( parameter_port_list )? ( list_of_port_declarations )? S_SC
  ;

module_declaration 
  :  module_nonansi_header ( timeunits_declaration )? ( module_item )* B_endmodule ( S_CO module_identifier )?
  |  module_ansi_header ( timeunits_declaration )? ( non_port_module_item )* B_endmodule ( S_CO module_identifier )?
  |  ( attribute_instance )* module_keyword ( lifetime )? module_identifier S_LM S_DT_AS S_RM S_SC ( timeunits_declaration )? ( module_item )* B_endmodule ( S_CO module_identifier )?
  |  K_extern module_nonansi_header
  |  K_extern module_ansi_header
  ;

module_keyword
  :  B_module | B_macromodule
  ;

interface_declaration 
  :  interface_nonansi_header ( timeunits_declaration )? ( interface_item )* B_endinterface ( S_CO interface_identifier )?
  |  interface_ansi_header ( timeunits_declaration )? ( non_port_interface_item )* B_endinterface ( S_CO interface_identifier )?
  |  ( attribute_instance )* B_interface interface_identifier S_LM S_DT_AS S_RM S_SC ( timeunits_declaration )? ( interface_item )* B_endinterface ( S_CO interface_identifier )?
  |  K_extern interface_nonansi_header
  |  K_extern interface_ansi_header
  ;

interface_nonansi_header 
  :  ( attribute_instance )* B_interface ( lifetime )? interface_identifier ( package_import_declaration )* ( parameter_port_list )? list_of_ports S_SC
  ;

interface_ansi_header 
  :  ( attribute_instance )* B_interface ( lifetime )? interface_identifier ( package_import_declaration )* ( parameter_port_list )? ( list_of_port_declarations )? S_SC
  ;

program_declaration 
  :  program_nonansi_header ( timeunits_declaration )? ( program_item )* B_endprogram ( S_CO program_identifier )? 
  |  program_ansi_header ( timeunits_declaration )? ( non_port_program_item )* B_endprogram ( S_CO program_identifier )?
  |  ( attribute_instance )* B_program program_identifier S_LM S_DT_AS S_RM S_SC ( timeunits_declaration )? ( program_item )* B_endprogram ( S_CO program_identifier )?
  |  K_extern program_nonansi_header
  |  K_extern program_ansi_header
  ;

program_nonansi_header 
  :  ( attribute_instance )* B_program ( lifetime )? program_identifier ( package_import_declaration )* ( parameter_port_list )? list_of_ports S_SC
  ;

program_ansi_header 
  :  ( attribute_instance )* B_program ( lifetime )? program_identifier ( package_import_declaration )* ( parameter_port_list )? ( list_of_port_declarations )? S_SC
  ;

checker_declaration 
  :  B_checker checker_identifier ( S_LM ( checker_port_list )? S_RM )? S_SC ( ( attribute_instance )* checker_or_generate_item )* B_endchecker ( S_CO checker_identifier )?
  ;

class_declaration 
  :   ( T_virtual )? B_class ( lifetime )? class_identifier ( parameter_port_list )? ( K_extends class_type ( S_LM list_of_arguments S_RM )? )? ( K_implements interface_class_type ( S_CM interface_class_type )* )? S_SC ( class_item )* B_endclass ( S_CO class_identifier )?
  ;

interface_class_type
  :  ps_class_identifier ( parameter_value_assignment )?
  ;

interface_class_declaration 
  :  B_interface B_class class_identifier ( parameter_port_list )? ( K_extends interface_class_type ( S_CM interface_class_type )* )? S_SC ( interface_class_item )* B_endclass ( S_CO class_identifier )?
  ;

interface_class_item 
  :  type_declaration
  |  ( attribute_instance )* interface_class_method
  |  local_parameter_declaration S_SC
  |  parameter_declaration S_SC
  |  S_SC
  ;

interface_class_method 
  :  T_pure T_virtual method_prototype S_SC
  ;

package_declaration 
  :  ( attribute_instance )* B_package ( lifetime )? package_identifier S_SC ( timeunits_declaration )? ( ( attribute_instance )* package_item )* B_endpackage ( S_CO package_identifier )?
  ;

timeunits_declaration 
  :  K_timeunit L_Time ( S_DV L_Time )? S_SC
  |  K_timeprecision L_Time S_SC
  |  K_timeunit L_Time S_SC K_timeprecision L_Time S_SC
  |  K_timeprecision L_Time S_SC K_timeunit L_Time S_SC
  ;

// A.1.3 Module parameters and ports

parameter_port_list 
  :  S_SH S_LM list_of_param_assignments ( S_CM parameter_port_declaration )* S_RM
  |  S_SH S_LM parameter_port_declaration ( S_CM parameter_port_declaration )* S_RM
  |  S_SH S_LM S_RM
  ;

parameter_port_declaration 
  :  parameter_declaration
  |  local_parameter_declaration
  |  data_type list_of_param_assignments
  |  T_type list_of_type_assignments
  ;

list_of_ports
  :  S_LM port ( S_CM port )* S_RM
  ;

list_of_port_declarations
  :  S_LM ( ( attribute_instance )* ansi_port_declaration ( S_CM ( attribute_instance )* ansi_port_declaration )* )? S_RM
  ;

port_declaration 
  :  ( attribute_instance )* inout_declaration
  |  ( attribute_instance )* input_declaration
  |  ( attribute_instance )* output_declaration
  |  ( attribute_instance )* ref_declaration
  |  ( attribute_instance )* interface_port_declaration
  ;

port 
  :   ( port_expression )?
  |  S_DT port_identifier S_LM ( port_expression )? S_RM
  ;

port_expression 
  :  port_reference
  |  S_LN port_reference ( S_CM port_reference )* S_RN
  ;

port_reference 
  :  port_identifier constant_select
  ;

port_direction
  :  T_input | T_output | T_inout | T_ref
  ;

net_port_header
  :   ( port_direction )? net_port_type
  ;

variable_port_header
  :   ( port_direction )? variable_port_type
  ;

interface_port_header 
  :  interface_identifier ( S_DT modport_identifier )?
  |  B_interface ( S_DT modport_identifier )?
  ;

ansi_port_declaration 
  :   ( net_port_header | interface_port_header )? port_identifier ( unpacked_dimension )* ( S_EQ constant_expression )?
  |   ( variable_port_header )? port_identifier ( variable_dimension )* ( S_EQ constant_expression )?
  |   ( port_direction )? S_DT port_identifier S_LM ( expression )? S_RM
  ;

// A.1.4 Module items

//[Mod]
elaboration_system_task 
  :  D_fatal ( S_LM N_Unsigned ( S_CM list_of_arguments )? S_RM )? S_SC
  |  D_error ( S_LM ( list_of_arguments )? S_RM )? S_SC
  |  D_warning ( S_LM ( list_of_arguments )? S_RM )? S_SC
  |  D_info ( S_LM ( list_of_arguments )? S_RM )? S_SC
  ;

module_common_item 
  :  module_or_generate_item_declaration
  |  interface_instantiation
  |  program_instantiation
  |  assertion_item
  |  bind_directive
  |  continuous_assign
  |  net_alias
  |  initial_construct
  |  final_construct
  |  always_construct
  |  loop_generate_construct
  |  conditional_generate_construct
  |  elaboration_system_task
  ;

module_item 
  :  port_declaration S_SC
  |  non_port_module_item
  ;

module_or_generate_item 
  :  ( attribute_instance )* parameter_override
  |  ( attribute_instance )* gate_instantiation
  |  ( attribute_instance )* udp_instantiation
  |  ( attribute_instance )* module_instantiation
  |  ( attribute_instance )* module_common_item
  ;

module_or_generate_item_declaration 
  :  package_or_generate_item_declaration
  |  genvar_declaration
  |  clocking_declaration
  |  K_default B_clocking clocking_identifier S_SC
  |  K_default K_disable K_iff expression_or_dist S_SC
  ;

non_port_module_item 
  :  generate_region
  |  module_or_generate_item
  |  specify_block
  |  ( attribute_instance )* specparam_declaration
  |  program_declaration
  |  module_declaration
  |  interface_declaration
  |  timeunits_declaration
  ;

parameter_override
  :  K_defparam list_of_defparam_assignments S_SC
  ;

bind_directive
  :  K_bind bind_target_scope ( S_CO bind_target_instance_list )? bind_instantiation S_SC
  |  K_bind bind_target_instance bind_instantiation S_SC
  ;

bind_target_scope 
  :  module_identifier
  |  interface_identifier
  ;

bind_target_instance 
  :  hierarchical_identifier constant_bit_select
  ;

bind_target_instance_list 
  :  bind_target_instance ( S_CM bind_target_instance )*
  ;

bind_instantiation 
  :  program_instantiation
  |  module_instantiation
  |  interface_instantiation
  |  checker_instantiation
  ;

// A.1.5 Configuration source text

config_declaration 
  :  B_config config_identifier S_SC ( local_parameter_declaration S_SC )* design_statement ( config_rule_statement )* B_endconfig ( S_CO config_identifier )?
  ;

design_statement
  :  K_design ( ( library_identifier S_DT )? cell_identifier )* S_SC
  ;

config_rule_statement 
  :  default_clause liblist_clause S_SC
  |  inst_clause liblist_clause S_SC
  |  inst_clause use_clause S_SC
  |  cell_clause liblist_clause S_SC
  |  cell_clause use_clause S_SC
  ;

default_clause
  :  K_default
  ;

inst_clause
  :  K_instance inst_name
  ;

inst_name
  :  topmodule_identifier ( S_DT instance_identifier )*
  ;

cell_clause
  :  K_cell ( library_identifier S_DT )? cell_identifier
  ;

liblist_clause
  :  K_liblist ( library_identifier )*
  ;

use_clause
  :  K_use ( library_identifier S_DT )? cell_identifier ( S_CO B_config )?
  |  K_use named_parameter_assignment ( S_CM named_parameter_assignment )* ( S_CO B_config )?
  |  K_use ( library_identifier S_DT )? cell_identifier named_parameter_assignment ( S_CM named_parameter_assignment )* ( S_CO B_config )?
  ;

// A.1.6 Interface items

interface_or_generate_item 
  :  ( attribute_instance )* module_common_item
  |  ( attribute_instance )* extern_tf_declaration
  ;

extern_tf_declaration 
  :  K_extern method_prototype S_SC
  |  K_extern K_forkjoin task_prototype S_SC
  ;

interface_item 
  :  port_declaration S_SC
  |  non_port_interface_item
  ;

non_port_interface_item 
  :  generate_region
  |  interface_or_generate_item
  |  program_declaration
  |  modport_declaration
  |  interface_declaration
  |  timeunits_declaration
  ;

// A.1.7 Program items

program_item 
  :  port_declaration S_SC
  |  non_port_program_item
  ;

non_port_program_item 
  :  ( attribute_instance )* continuous_assign
  |  ( attribute_instance )* module_or_generate_item_declaration
  |  ( attribute_instance )* initial_construct
  |  ( attribute_instance )* final_construct
  |  ( attribute_instance )* concurrent_assertion_item
  |  timeunits_declaration
  |  program_generate_item
  ;

program_generate_item
  :  loop_generate_construct
  |  conditional_generate_construct
  |  generate_region
  |  elaboration_system_task
  ;

// A.1.8 Checker items

checker_port_list 
  :  checker_port_item ( S_CM checker_port_item )*
  ;

checker_port_item 
  :  ( attribute_instance )* ( checker_port_direction )? property_formal_type formal_port_identifier ( variable_dimension )* ( S_EQ property_actual_arg )?
  ;

checker_port_direction 
  :  T_input | T_output
  ;

checker_or_generate_item 
  :  checker_or_generate_item_declaration
  |  initial_construct
  |  always_construct
  |  final_construct
  |  assertion_item
  |  continuous_assign
  |  checker_generate_item
  ;

checker_or_generate_item_declaration 
  :   ( K_rand )? data_declaration
  |  function_declaration
  |  checker_declaration
  |  assertion_item_declaration
  |  covergroup_declaration
  |  genvar_declaration
  |  clocking_declaration
  |  K_default B_clocking clocking_identifier S_SC
  |  K_default K_disable K_iff expression_or_dist S_SC
  |  S_SC
  ;

checker_generate_item
  :  loop_generate_construct
  |  conditional_generate_construct
  |  generate_region
  |  elaboration_system_task
  ;

// A.1.9 Class items

class_item 
  :  ( attribute_instance )* class_property
  |  ( attribute_instance )* class_method
  |  ( attribute_instance )* class_constraint
  |  ( attribute_instance )* class_declaration
  |  ( attribute_instance )* covergroup_declaration
  |  local_parameter_declaration S_SC
  |  parameter_declaration S_SC
  |  S_SC
  ;

class_property 
  :  ( property_qualifier )* data_declaration
  |  T_const ( class_item_qualifier )* data_type const_identifier ( S_EQ constant_expression )? S_SC
  ;

class_method 
  :  ( method_qualifier )* task_declaration
  |  ( method_qualifier )* function_declaration
  |  T_pure T_virtual ( class_item_qualifier )* method_prototype S_SC
  |  K_extern ( method_qualifier )* method_prototype S_SC
  |  ( method_qualifier )* class_constructor_declaration
  |  K_extern ( method_qualifier )* class_constructor_prototype
  ;

class_constructor_prototype 
  :  B_function K_new ( S_LM ( tf_port_list )? S_RM )? S_SC
  ;

class_constraint 
  :  constraint_prototype
  |  constraint_declaration
  ;

class_item_qualifier
  :  T_static
  |  T_protected
  |  T_local
  ;

property_qualifier
  :  random_qualifier
  |  class_item_qualifier
  ;

random_qualifier
  :  K_rand
  |  K_randc
  ;

method_qualifier
  :   ( T_pure )? T_virtual
  |  class_item_qualifier
  ;

method_prototype 
  :  task_prototype
  |  function_prototype
  ;

class_constructor_declaration 
  :  B_function ( class_scope )? K_new ( S_LM ( tf_port_list )? S_RM )? S_SC ( block_item_declaration )* ( K_super S_DT K_new ( S_LM list_of_arguments S_RM )? S_SC )? ( function_statement_or_null )* B_endfunction ( S_CO K_new )?
  ;

// A.1.10 Constraints

constraint_declaration
  :   ( T_static )? K_constraint constraint_identifier constraint_block
  ;

constraint_block
  :  S_LN ( constraint_block_item )* S_RN
  ;

constraint_block_item 
  :  K_solve solve_before_list K_before solve_before_list S_SC
  |  constraint_expression
  ;

solve_before_list
  :  constraint_primary ( S_CM constraint_primary )*
  ;

constraint_primary
  :   ( implicit_class_handle S_DT | class_scope )? hierarchical_identifier select
  ;

constraint_expression 
  :   ( K_soft )? expression_or_dist S_SC
  |  uniqueness_constraint S_SC
  |  expression S_MI_RB constraint_set
  |  K_if S_LM expression S_RM constraint_set ( K_else constraint_set )?
  |  K_foreach S_LM ps_or_hierarchical_array_identifier S_LK loop_variables S_RK S_RM constraint_set
  |  K_disable K_soft constraint_primary S_SC
  ;

uniqueness_constraint 
  :  K_unique S_LN open_range_list S_RN
  ;

constraint_set 
  :  constraint_expression
  |  S_LN ( constraint_expression )* S_RN
  ;

dist_list
  :  dist_item ( S_CM dist_item )*
  ;

dist_item
  :  value_range ( dist_weight )?
  ;

dist_weight 
  :  S_CO_EQ expression
  |  S_CO_DV expression
  ;

constraint_prototype
  :  ( constraint_prototype_qualifier )? ( T_static )? K_constraint constraint_identifier S_SC
  ;

constraint_prototype_qualifier
  :  K_extern | T_pure
  ;

extern_constraint_declaration 
  :   ( T_static )? K_constraint class_scope constraint_identifier constraint_block
  ;

identifier_list
  :  identifier ( S_CM identifier )*
  ;

// A.1.11 Package items

package_item 
  :  package_or_generate_item_declaration
  |  anonymous_program
  |  package_export_declaration
  |  timeunits_declaration
  ;

package_or_generate_item_declaration 
  :  net_declaration
  |  data_declaration
  |  task_declaration
  |  function_declaration
  |  checker_declaration
  |  dpi_import_export
  |  extern_constraint_declaration
  |  class_declaration
  |  class_constructor_declaration
  |  local_parameter_declaration S_SC
  |  parameter_declaration S_SC
  |  covergroup_declaration
  |  assertion_item_declaration
  |  S_SC
  ;

anonymous_program
  :  B_program S_SC ( anonymous_program_item )* B_endprogram
  ;

anonymous_program_item 
  :  task_declaration
  |  function_declaration
  |  class_declaration
  |  covergroup_declaration
  |  class_constructor_declaration
  |  S_SC
  ;

// A.2 Declarations
// A.2.1 Declaration types
// A.2.1.1 Module parameter declarations

local_parameter_declaration 
  :  T_localparam data_type_or_implicit list_of_param_assignments
  |  T_localparam T_type list_of_type_assignments
  ;

parameter_declaration 
  :  T_parameter data_type_or_implicit list_of_param_assignments
  |  T_parameter T_type list_of_type_assignments
  ;

specparam_declaration 
  :  K_specparam ( packed_dimension )? list_of_specparam_assignments S_SC
  ;

// A.2.1.2 Port declarations

inout_declaration 
  :  T_inout net_port_type list_of_port_identifiers
  ;

input_declaration 
  :  T_input net_port_type list_of_port_identifiers
  |  T_input variable_port_type list_of_variable_identifiers
  ;

output_declaration 
  :  T_output net_port_type list_of_port_identifiers
  |  T_output variable_port_type list_of_variable_port_identifiers
  ;

interface_port_declaration 
  :  interface_identifier list_of_interface_identifiers
  |  interface_identifier S_DT modport_identifier list_of_interface_identifiers
  ;

ref_declaration
  :  T_ref variable_port_type list_of_variable_identifiers
  ;

// A.2.1.3 Type declarations

data_declaration 
  :   ( T_const )? ( T_var )? ( lifetime )? data_type_or_implicit list_of_variable_decl_assignments S_SC
  |  type_declaration
  |  package_import_declaration
  |  net_type_declaration
  ;

package_import_declaration 
  :  K_import package_import_item ( S_CM package_import_item )* S_SC
  ;

package_import_item 
  :  package_identifier S_CO_CO identifier
  |  package_identifier S_CO_CO S_AS
  ;

package_export_declaration 
  :  K_export S_AS_CO_CO_AS S_SC
  |  K_export package_import_item ( S_CM package_import_item )* S_SC
  ;

genvar_declaration
  :  T_genvar list_of_genvar_identifiers S_SC
  ;

net_declaration
  :  net_type ( drive_strength | charge_strength )? ( T_vectored | T_scalared )? data_type_or_implicit ( delay3 )? list_of_net_decl_assignments S_SC
  |  net_type_identifier ( delay_control )? list_of_net_decl_assignments S_SC
  |  T_interconnect implicit_data_type ( S_SH delay_value )? net_identifier ( unpacked_dimension )* ( S_CM net_identifier ( unpacked_dimension )* )? S_SC
  ;

type_declaration 
  :  K_typedef data_type type_identifier ( variable_dimension )* S_SC
  |  K_typedef interface_instance_identifier constant_bit_select S_DT type_identifier type_identifier S_SC
  |  K_typedef ( T_enum | T_struct | T_union | B_class | B_interface B_class )? type_identifier S_SC
  ;

net_type_declaration 
  :  K_nettype data_type net_type_identifier ( K_with ( package_scope | class_scope )? tf_identifier )? S_SC
  |  K_nettype ( package_scope | class_scope )? net_type_identifier net_type_identifier S_SC
  ;

lifetime
  :  T_static | T_automatic
  ;

// A.2.2 Declaration data types
// A.2.2.1 Net and variable types

casting_type
  :  simple_type | constant_primary | signing | T_string | T_const
  ;

//[mod]
casting_type_t
  :  simple_type | signing | T_string | T_const
  ;

data_type 
  :  integer_vector_type ( signing )? ( packed_dimension )*
  |  integer_atom_type ( signing )?
  |  non_integer_type
  |  struct_union ( T_packed ( signing )? )? S_LN struct_union_member ( struct_union_member )* S_RN ( packed_dimension )*
  |  T_enum ( enum_base_type )? S_LN enum_name_declaration ( S_CM enum_name_declaration )* S_RN ( packed_dimension )*
  |  T_string
  |  T_chandle
  |  T_virtual ( B_interface )? interface_identifier ( parameter_value_assignment )? ( S_DT modport_identifier )?
  |   ( class_scope | package_scope )? type_identifier ( packed_dimension )*
  |  class_type
  |  K_event
  |  ps_covergroup_identifier
  |  type_reference
  ;

data_type_or_implicit 
  :  data_type
  |  implicit_data_type
  ;

implicit_data_type
  :   ( signing )? ( packed_dimension )*
  ;

enum_base_type 
  :  integer_atom_type ( signing )?
  |  integer_vector_type ( signing )? ( packed_dimension )?
  |  type_identifier ( packed_dimension )?
  ;

enum_name_declaration 
  :  enum_identifier ( S_LK integral_number ( S_CO integral_number )? S_RK )? ( S_EQ constant_expression )?
  ;

class_scope
  :  class_type S_CO_CO
  ;

class_type 
  :  ps_class_identifier ( parameter_value_assignment )? ( S_CO_CO class_identifier ( parameter_value_assignment )? )*
  ;

integer_type
  :  integer_vector_type | integer_atom_type
  ;

integer_atom_type
  :  T_byte | T_shortint | T_int | T_longint | T_integer | T_time
  ;

integer_vector_type
  :  T_bit | T_logic | T_reg
  ;

non_integer_type
  :  T_shortreal | T_real | T_realtime
  ;

net_type
  :  T_supply0 | T_supply1 | T_tri | T_triand | T_trior | T_trireg | T_tri0 | T_tri1 | T_uwire | T_wire | T_wand | T_wor
  ;

net_port_type 
  :   ( net_type )? data_type_or_implicit
  |  net_type_identifier
  |  T_interconnect implicit_data_type
  ;

variable_port_type
  :  var_data_type
  ;

var_data_type
  :  data_type | T_var data_type_or_implicit
  ;

signing
  :  T_signed | T_unsigned
  ;

simple_type
  :  integer_type | non_integer_type | ps_type_identifier | ps_parameter_identifier
  ;

struct_union_member
  :  ( attribute_instance )* ( random_qualifier )? data_type_or_void list_of_variable_decl_assignments S_SC
  ;

data_type_or_void
  :  data_type | T_void
  ;

struct_union
  :  T_struct | T_union ( T_tagged )?
  ;

type_reference 
  :  T_type S_LM expression S_RM
  |  T_type S_LM data_type S_RM
  ;

// A.2.2.2 Strengths

drive_strength 
  :  S_LM strength0 S_CM strength1 S_RM
  |  S_LM strength1 S_CM strength0 S_RM
  |  S_LM strength0 S_CM T_highz1 S_RM
  |  S_LM strength1 S_CM T_highz0 S_RM
  |  S_LM T_highz0 S_CM strength1 S_RM
  |  S_LM T_highz1 S_CM strength0 S_RM
  ;

strength0
  :  T_supply0 | T_strong0 | T_pull0 | T_weak0
  ;

strength1
  :  T_supply1 | T_strong1 | T_pull1 | T_weak1
  ;

charge_strength
  :  S_LM T_small S_RM | S_LM T_medium S_RM | S_LM T_large S_RM
  ;

// A.2.2.3 Delays

delay3
  :  S_SH delay_value | S_SH S_LM mintypmax_expression ( S_CM mintypmax_expression ( S_CM mintypmax_expression )? )? S_RM
  ;

delay2
  :  S_SH delay_value | S_SH S_LM mintypmax_expression ( S_CM mintypmax_expression )? S_RM
  ;

delay_value 
  :  N_Unsigned
  |  real_number
  |  ps_identifier
  |  L_Time
  |  K_1step
  ;

// A.2.3 Declaration lists

list_of_defparam_assignments
  :  defparam_assignment ( S_CM defparam_assignment )*
  ;

list_of_genvar_identifiers
  :  genvar_identifier ( S_CM genvar_identifier )*
  ;

list_of_interface_identifiers
  :  interface_identifier ( unpacked_dimension )* ( S_CM interface_identifier ( unpacked_dimension )* )*
  ;

list_of_net_decl_assignments
  :  net_decl_assignment ( S_CM net_decl_assignment )*
  ;

list_of_param_assignments
  :  param_assignment ( S_CM param_assignment )*
  ;

list_of_port_identifiers
  :  port_identifier ( unpacked_dimension )* ( S_CM port_identifier ( unpacked_dimension )* )*
  ;

list_of_udp_port_identifiers
  :  port_identifier ( S_CM port_identifier )*
  ;

list_of_specparam_assignments
  :  specparam_assignment ( S_CM specparam_assignment )*
  ;

list_of_tf_variable_identifiers
  :  port_identifier ( variable_dimension )* ( S_EQ expression )? ( S_CM port_identifier ( variable_dimension )* ( S_EQ expression )? )*
  ;

list_of_type_assignments
  :  type_assignment ( S_CM type_assignment )*
  ;

list_of_variable_decl_assignments
  :  variable_decl_assignment ( S_CM variable_decl_assignment )*
  ;

list_of_variable_identifiers
  :  variable_identifier ( variable_dimension )* ( S_CM variable_identifier ( variable_dimension )* )*
  ;

list_of_variable_port_identifiers
  :  port_identifier ( variable_dimension )* ( S_EQ constant_expression )? ( S_CM port_identifier ( variable_dimension )* ( S_EQ constant_expression )? )*
  ;

// A.2.4 Declaration assignments

defparam_assignment
  :  hierarchical_parameter_identifier S_EQ constant_mintypmax_expression
  ;

net_decl_assignment
  :  net_identifier ( unpacked_dimension )* ( S_EQ expression )?
  ;

param_assignment 
  :  parameter_identifier ( unpacked_dimension )* ( S_EQ constant_param_expression )?
  ;

specparam_assignment 
  :  specparam_identifier S_EQ constant_mintypmax_expression
  |  pulse_control_specparam
  ;

type_assignment 
  :  type_identifier ( S_EQ data_type )?
  ;

pulse_control_specparam 
  :  K_PATHPULSE_DL S_EQ S_LM reject_limit_value ( S_CM error_limit_value )? S_RM
  |  K_PATHPULSE_DL specify_input_terminal_descriptor S_DL specify_output_terminal_descriptor S_EQ S_LM reject_limit_value ( S_CM error_limit_value )? S_RM
  ;

error_limit_value
  :  limit_value
  ;

reject_limit_value
  :  limit_value
  ;

limit_value
  :  constant_mintypmax_expression
  ;

variable_decl_assignment 
  :  variable_identifier ( variable_dimension )* ( S_EQ expression )?
  |  dynamic_array_variable_identifier unsized_dimension ( variable_dimension )* ( S_EQ dynamic_array_new )?
  |  class_variable_identifier ( S_EQ class_new )?
  ;

class_new
  :   ( class_scope )? K_new ( S_LM list_of_arguments S_RM )?
  |  K_new expression
  ;

dynamic_array_new
  :  K_new S_LK expression S_RK ( S_LM expression S_RM )?
  ;

// A.2.5 Declaration ranges

unpacked_dimension 
  :  S_LK constant_range S_RK
  |  S_LK constant_expression S_RK
  ;

packed_dimension
  :  S_LK constant_range S_RK
  |  unsized_dimension
  ;

associative_dimension 
  :  S_LK data_type S_RK
  |  S_LK S_AS S_RK
  ;

variable_dimension 
  :  unsized_dimension
  |  unpacked_dimension
  |  associative_dimension
  |  queue_dimension
  ;

queue_dimension
  :  S_LK S_DL ( S_CO constant_expression )? S_RK
  ;

unsized_dimension
  :  S_LK S_RK
  ;

// A.2.6 Function declarations

function_data_type_or_implicit 
  :  data_type_or_void
  |  implicit_data_type
  ;

function_declaration
  :  B_function ( lifetime )? function_body_declaration
  ;

function_body_declaration 
  :  function_data_type_or_implicit ( interface_identifier S_DT | class_scope )? function_identifier S_SC ( tf_item_declaration )* ( function_statement_or_null )* B_endfunction ( S_CO function_identifier )?
  |  function_data_type_or_implicit ( interface_identifier S_DT | class_scope )? function_identifier S_LM ( tf_port_list )? S_RM S_SC ( block_item_declaration )* ( function_statement_or_null )* B_endfunction ( S_CO function_identifier )?
  ;

function_prototype
  :  B_function data_type_or_void function_identifier ( S_LM ( tf_port_list )? S_RM )?
  ;

dpi_import_export 
  :  K_import dpi_spec_string ( dpi_function_import_property )? ( c_identifier S_EQ )? dpi_function_proto S_SC
  |  K_import dpi_spec_string ( dpi_task_import_property )? ( c_identifier S_EQ )? dpi_task_proto S_SC
  |  K_export dpi_spec_string ( c_identifier S_EQ )? B_function function_identifier S_SC
  |  K_export dpi_spec_string ( c_identifier S_EQ )? B_task task_identifier S_SC
  ;

dpi_spec_string
  :  K_DPI_C | K_DPI
  ;

dpi_function_import_property
  :  T_context | T_pure
  ;

dpi_task_import_property
  :  T_context
  ;

dpi_function_proto
  :  function_prototype
  ;

dpi_task_proto
  :  task_prototype
  ;

// A.2.7 Task declarations

task_declaration
  :  B_task ( lifetime )? task_body_declaration
  ;

task_body_declaration 
  :   ( interface_identifier S_DT | class_scope )? task_identifier S_SC ( tf_item_declaration )* ( statement_or_null )* B_endtask ( S_CO task_identifier )?
  |   ( interface_identifier S_DT | class_scope )? task_identifier S_LM ( tf_port_list )? S_RM S_SC ( block_item_declaration )* ( statement_or_null )* B_endtask ( S_CO task_identifier )?
  ;

tf_item_declaration 
  :  block_item_declaration
  |  tf_port_declaration
  ;

tf_port_list 
  :  tf_port_item ( S_CM tf_port_item )*
  ;

tf_port_item
  :  ( attribute_instance )* ( tf_port_direction )? ( T_var )? data_type_or_implicit ( port_identifier ( variable_dimension )*  ( S_EQ expression )? )?
  ;

tf_port_direction
  :  port_direction | T_const T_ref
  ;

tf_port_declaration 
  :  ( attribute_instance )* tf_port_direction ( T_var )? data_type_or_implicit list_of_tf_variable_identifiers S_SC
  ;

task_prototype
  :  B_task task_identifier ( S_LM ( tf_port_list )? S_RM )?
  ;

// A.2.8 Block item declarations

block_item_declaration 
  :  ( attribute_instance )* data_declaration
  |  ( attribute_instance )* local_parameter_declaration S_SC
  |  ( attribute_instance )* parameter_declaration S_SC
  |  ( attribute_instance )* let_declaration
  ;

// A.2.9 Interface declarations

modport_declaration
  :  K_modport modport_item ( S_CM modport_item )* S_SC
  ;

modport_item
  :  modport_identifier S_LM modport_ports_declaration ( S_CM modport_ports_declaration )* S_RM
  ;

modport_ports_declaration 
  :  ( attribute_instance )* modport_simple_ports_declaration
  |  ( attribute_instance )* modport_tf_ports_declaration
  |  ( attribute_instance )* modport_clocking_declaration
  ;

modport_clocking_declaration
  :  B_clocking clocking_identifier
  ;

modport_simple_ports_declaration 
  :  port_direction modport_simple_port ( S_CM modport_simple_port )*
  ;

modport_simple_port 
  :  port_identifier
  |  S_DT port_identifier S_LM ( expression )? S_RM
  ;

modport_tf_ports_declaration 
  :  import_export modport_tf_port ( S_CM modport_tf_port )*
  ;

modport_tf_port 
  :  method_prototype
  |  tf_identifier
  ;

import_export
  :  K_import | K_export
  ;

// A.2.10 Assertion declarations

concurrent_assertion_item 
  :   ( block_identifier S_CO )? concurrent_assertion_statement
  |  checker_instantiation
  ;

concurrent_assertion_statement 
  :  assert_property_statement
  |  assume_property_statement
  |  cover_property_statement
  |  cover_sequence_statement
  |  restrict_property_statement
  ;

assert_property_statement
  :  K_assert B_property S_LM property_spec S_RM action_block
  ;

assume_property_statement
  :  K_assume B_property S_LM property_spec S_RM action_block
  ;

cover_property_statement
  :  K_cover B_property S_LM property_spec S_RM statement_or_null
  ;

expect_property_statement 
  :  K_expect S_LM property_spec S_RM action_block
  ;

cover_sequence_statement
  :  K_cover B_sequence S_LM ( clocking_event )? ( K_disable K_iff S_LM expression_or_dist S_RM )? sequence_expr S_RM statement_or_null
  ;

restrict_property_statement
  :  K_restrict B_property S_LM property_spec S_RM S_SC
  ;

property_instance 
  :  ps_or_hierarchical_property_identifier ( S_LM ( property_list_of_arguments )? S_RM )?
  ;

property_list_of_arguments 
  :  ( property_actual_arg )? ( S_CM ( property_actual_arg )? )* ( S_CM S_DT identifier S_LM ( property_actual_arg )? S_RM )*
  |  S_DT identifier S_LM ( property_actual_arg )? S_RM ( S_CM S_DT identifier S_LM ( property_actual_arg )? S_RM )*
  ;

property_actual_arg 
  :  property_expr
  |  sequence_actual_arg
  ;

assertion_item_declaration 
  :  property_declaration
  |  sequence_declaration
  |  let_declaration
  ;

property_declaration 
  :  B_property property_identifier ( S_LM ( property_port_list )? S_RM )? S_SC ( assertion_variable_declaration )* property_spec ( S_SC )? B_endproperty ( S_CO property_identifier )?
  ;

property_port_list 
  :  property_port_item ( S_CM property_port_item )*
  ;

property_port_item 
  :  ( attribute_instance )* ( T_local ( property_lvar_port_direction )? )? property_formal_type formal_port_identifier ( variable_dimension )* ( S_EQ property_actual_arg )?
  ;

property_lvar_port_direction
  :  T_input
  ;

property_formal_type 
  :  sequence_formal_type
  |  B_property
  ;

property_spec 
  :  ( clocking_event )? ( K_disable K_iff S_LM expression_or_dist S_RM )? property_expr
  ;

property_expr 
  :  sequence_expr
  |  K_strong S_LM sequence_expr S_RM
  |  K_weak S_LM sequence_expr S_RM
  |  S_LM property_expr S_RM
  |  O_not property_expr
  |  <assoc=right> property_expr O_or property_expr
  |  <assoc=right> property_expr O_and property_expr
  |  sequence_expr S_OR_MI_RB property_expr
  |  sequence_expr S_OR_EQ_RB property_expr
  |  K_if ( expression_or_dist ) property_expr ( K_else property_expr )?
  |  B_case ( expression_or_dist ) property_case_item ( property_case_item )* B_endcase
  |  sequence_expr S_SH_MI_SH property_expr
  |  sequence_expr S_SH_EQ_SH property_expr
  |  K_nexttime property_expr
  |  K_nexttime S_LK constant_expression S_RK property_expr
  |  K_s_nexttime property_expr
  |  K_s_nexttime S_LK constant_expression S_RK property_expr
  |  K_always property_expr
  |  K_always S_LK cycle_delay_const_range_expression S_RK property_expr
  |  K_s_always S_LK constant_range S_RK property_expr
  |  K_s_eventually property_expr
  |  K_eventually S_LK constant_range S_RK property_expr
  |  K_s_eventually S_LK cycle_delay_const_range_expression S_RK property_expr
  |  <assoc=right> property_expr K_until property_expr
  |  <assoc=right> property_expr K_s_until property_expr
  |  <assoc=right> property_expr K_until_with property_expr
  |  <assoc=right> property_expr K_s_until_with property_expr
  |  <assoc=right> property_expr K_implies property_expr
  |  <assoc=right> property_expr K_iff property_expr
  |  K_accept_on S_LM expression_or_dist S_RM property_expr
  |  K_reject_on S_LM expression_or_dist S_RM property_expr
  |  K_sync_accept_on S_LM expression_or_dist S_RM property_expr
  |  K_sync_reject_on S_LM expression_or_dist S_RM property_expr
  |  property_instance
  |  clocking_event property_expr
  ;

property_case_item 
  :  expression_or_dist ( S_CM expression_or_dist )* S_CO property_expr S_SC
  |  K_default ( S_CO )? property_expr S_SC
  ;

sequence_declaration 
  :  B_sequence sequence_identifier ( S_LM ( sequence_port_list )? S_RM )? S_SC ( assertion_variable_declaration )* sequence_expr ( S_SC )? B_endsequence ( S_CO sequence_identifier )?
  ;

sequence_port_list 
  :  sequence_port_item ( S_CM sequence_port_item )*
  ;

sequence_port_item 
  :  ( attribute_instance )* ( T_local ( sequence_lvar_port_direction )? )? sequence_formal_type formal_port_identifier ( variable_dimension )* ( S_EQ sequence_actual_arg )?
  ;

sequence_lvar_port_direction
  :  T_input | T_inout | T_output
  ;

sequence_formal_type 
  :  data_type_or_implicit
  |  B_sequence
  |  K_untyped
  ;

sequence_expr 
  :  cycle_delay_range sequence_expr ( cycle_delay_range sequence_expr )*
  |  <assoc=right> sequence_expr cycle_delay_range sequence_expr ( cycle_delay_range sequence_expr )*
  |  expression_or_dist ( boolean_abbrev )?
  |  sequence_instance ( sequence_abbrev )?
  |  S_LM sequence_expr ( S_CM sequence_match_item )* S_RM ( sequence_abbrev )?
  |  <assoc=right> sequence_expr O_and sequence_expr
  |  <assoc=right> sequence_expr K_intersect sequence_expr
  |  <assoc=right> sequence_expr O_or sequence_expr
  |  K_first_match S_LM sequence_expr ( S_CM sequence_match_item )* S_RM
  |  expression_or_dist K_throughout sequence_expr
  |  <assoc=right> sequence_expr K_within sequence_expr
  |  clocking_event sequence_expr
  ;

cycle_delay_range 
  :  S_SH_SH constant_primary
  |  S_SH_SH S_LK cycle_delay_const_range_expression S_RK
  |  S_SH_SH_LK_AS_RK
  |  S_SH_SH_LK_PL_RK
  ;

sequence_method_call 
  :  sequence_instance S_DT method_identifier
  ;

sequence_match_item 
  :  operator_assignment
  |  inc_or_dec_expression
  |  subroutine_call
  ;

sequence_instance 
  :  ps_or_hierarchical_sequence_identifier ( S_LM ( sequence_list_of_arguments )? S_RM )?
  ;

sequence_list_of_arguments 
  :  ( sequence_actual_arg )? ( S_CM ( sequence_actual_arg )? )* ( S_CM S_DT identifier S_LM ( sequence_actual_arg )? S_RM )*
  |  S_DT identifier S_LM ( sequence_actual_arg )? S_RM ( S_CM S_DT identifier S_LM ( sequence_actual_arg )? S_RM )*
  ;

sequence_actual_arg 
  :  event_expression
  |  sequence_expr
  ;

boolean_abbrev 
  :  consecutive_repetition
  |  non_consecutive_repetition
  |  goto_repetition
  ;

sequence_abbrev
  :  consecutive_repetition
  ;

consecutive_repetition 
  :  S_LK_AS const_or_range_expression S_RK
  |  S_LK_AS_RK
  |  S_LK_PL_RK
  ;

non_consecutive_repetition
  :  S_LK_EQ const_or_range_expression S_RK
  ;

goto_repetition
  :  S_LK_MI_RB const_or_range_expression S_RK
  ;

const_or_range_expression 
  :  constant_expression
  |  cycle_delay_const_range_expression
  ;

cycle_delay_const_range_expression 
  :  constant_expression S_CO constant_expression
  |  constant_expression S_CO S_DL
  ;

expression_or_dist
  :  expression ( K_dist S_LN dist_list S_RN )?
  ;

assertion_variable_declaration 
  :  var_data_type list_of_variable_decl_assignments S_SC
  ;

// A.2.11 Covergroup declarations

covergroup_declaration 
  :  B_covergroup covergroup_identifier ( S_LM ( tf_port_list )? S_RM )? ( coverage_event )? S_SC ( coverage_spec_or_option )* B_endgroup ( S_CO covergroup_identifier )?
  ;

coverage_spec_or_option 
  :  ( attribute_instance )* coverage_spec
  |  ( attribute_instance )* coverage_option S_SC
  ;

coverage_option 
  :  K_option.member_identifier S_EQ expression
  |  K_type_option.member_identifier S_EQ constant_expression
  ;

coverage_spec 
  :  cover_point
  |  cover_cross
  ;

coverage_event 
  :  clocking_event
  |  K_with B_function K_sample S_LM ( tf_port_list )? S_RM
  |  S_AT_AT_LM block_event_expression S_RM
  ;

block_event_expression 
  :  block_event_expression O_or block_event_expression
  |  B_begin hierarchical_btf_identifier
  |  B_end hierarchical_btf_identifier
  ;

hierarchical_btf_identifier 
  :  hierarchical_tf_identifier
  |  hierarchical_block_identifier
  |   ( hierarchical_identifier S_DT | class_scope )? method_identifier
  ;

cover_point 
  :   (  ( data_type_or_implicit )? cover_point_identifier S_CO )? K_coverpoint expression ( K_iff S_LM expression S_RM )? bins_or_empty
  ;

bins_or_empty 
  :  S_LN ( attribute_instance )* ( bins_or_options S_SC )* S_RN
  |  S_SC
  ;

bins_or_options 
  :  coverage_option
  |   ( K_wildcard )? bins_keyword bin_identifier ( S_LK ( covergroup_expression )? S_RK )? S_EQ S_LN covergroup_range_list S_RN ( K_with S_LM with_covergroup_expression S_RM )? ( K_iff S_LM expression S_RM )? 
  |   ( K_wildcard )? bins_keyword bin_identifier ( S_LK ( covergroup_expression )? S_RK )? S_EQ cover_point_identifier K_with S_LM with_covergroup_expression S_RM ( K_iff S_LM expression S_RM )?
  |   ( K_wildcard )? bins_keyword bin_identifier ( S_LK ( covergroup_expression )? S_RK )? S_EQ set_covergroup_expression ( K_iff S_LM expression S_RM )?
  |   ( K_wildcard )? bins_keyword bin_identifier ( S_LK S_RK )? S_EQ trans_list ( K_iff S_LM expression S_RM )?
  |  bins_keyword bin_identifier ( S_LK ( covergroup_expression )? S_RK )? S_EQ K_default ( K_iff S_LM expression S_RM )?
  |  bins_keyword bin_identifier S_EQ K_default B_sequence ( K_iff S_LM expression S_RM )?
  ;

bins_keyword
  :  K_bins | K_illegal_bins | K_ignore_bins
  ;

trans_list
  :  S_LM trans_set S_RM ( S_CM S_LM trans_set S_RM )*
  ;

trans_set
  :  trans_range_list ( S_EQ_RB trans_range_list )*
  ;

trans_range_list 
  :  trans_item
  |  trans_item S_LK_AS repeat_range S_RK
  |  trans_item S_LK_MI_RB repeat_range S_RK
  |  trans_item S_LK_EQ repeat_range S_RK
  ;

trans_item
  :  covergroup_range_list
  ;

repeat_range 
  :  covergroup_expression
  |  covergroup_expression S_CO covergroup_expression
  ;

cover_cross 
  :   ( cross_identifier S_CO )? K_cross list_of_cross_items ( K_iff S_LM expression S_RM )? cross_body
  ;

list_of_cross_items
  :  cross_item S_CM cross_item ( S_CM cross_item )*
  ;

cross_item 
  :  cover_point_identifier
  |  variable_identifier
  ;

cross_body 
  :  S_LN ( cross_body_item S_SC )* S_RN
  |  S_SC
  ;

cross_body_item 
  :  function_declaration
  |  bins_selection_or_option S_SC
  ;

bins_selection_or_option 
  :  ( attribute_instance )* coverage_option
  |  ( attribute_instance )* bins_selection
  ;

bins_selection
  :  bins_keyword bin_identifier S_EQ select_expression ( K_iff S_LM expression S_RM )?
  ;

select_expression
  :  select_condition
  |  S_EX select_condition
  |  <assoc=right> select_expression S_AN_AN select_expression
  |  <assoc=right> select_expression S_OR_OR select_expression
  |  S_LM select_expression S_RM
  |  <assoc=right> select_expression K_with S_LM with_covergroup_expression S_RM ( K_matches integer_covergroup_expression )?
  |  cross_identifier
  |  cross_set_expression ( K_matches integer_covergroup_expression )?
  ;

select_condition
  :  K_binsof S_LM bins_expression S_RM ( K_intersect S_LN covergroup_range_list S_RN )?
  ;

bins_expression 
  :  variable_identifier
  |  cover_point_identifier ( S_DT bin_identifier )?
  ;

covergroup_range_list
  :  covergroup_value_range ( S_CM covergroup_value_range )*
  ;

covergroup_value_range 
  :  covergroup_expression
  |  S_LK covergroup_expression S_CO covergroup_expression S_RK
  ;

with_covergroup_expression
  :  covergroup_expression
  ;

set_covergroup_expression
  :  covergroup_expression
  ;

integer_covergroup_expression
  :  covergroup_expression
  ;

cross_set_expression
  :  covergroup_expression
  ;

covergroup_expression
  :  expression
  ;

// A.2.12 Let declarations

let_declaration 
  :  K_let let_identifier ( S_LM ( let_port_list )? S_RM )? S_EQ expression S_SC
  ;

let_identifier 
  :  identifier
  ;

let_port_list 
  :  let_port_item ( S_CM let_port_item )*
  ;

let_port_item 
  :  ( attribute_instance )* let_formal_type formal_port_identifier ( variable_dimension )* ( S_EQ expression )?
  ;

let_formal_type 
  :  data_type_or_implicit
  |  K_untyped
  ;

let_expression 
  :   ( package_scope )? let_identifier ( S_LM ( let_list_of_arguments )? S_RM )?
  ;

let_list_of_arguments 
  :   ( let_actual_arg )? ( S_CM ( let_actual_arg )? )* ( S_CM S_DT identifier S_LM ( let_actual_arg )? S_RM )*
  |  S_DT identifier S_LM ( let_actual_arg )? S_RM ( S_CM S_DT identifier S_LM ( let_actual_arg )? S_RM )*
  ;

let_actual_arg 
  :  expression
  ;

// A.3 Primitive instances
// A.3.1 Primitive instantiation and instances

gate_instantiation 
  :  cmos_switchtype ( delay3 )?  cmos_switch_instance ( S_CM cmos_switch_instance )* S_SC
  |  enable_gatetype ( drive_strength )?  ( delay3 )?  enable_gate_instance ( S_CM enable_gate_instance )* S_SC
  |  mos_switchtype ( delay3 )?  mos_switch_instance ( S_CM mos_switch_instance )* S_SC
  |  n_input_gatetype ( drive_strength )?  ( delay2 )?  n_input_gate_instance ( S_CM n_input_gate_instance )* S_SC
  |  n_output_gatetype ( drive_strength )?  ( delay2 )?  n_output_gate_instance ( S_CM n_output_gate_instance )* S_SC
  |  pass_en_switchtype ( delay2 )?  pass_enable_switch_instance ( S_CM pass_enable_switch_instance )* S_SC
  |  pass_switchtype pass_switch_instance ( S_CM pass_switch_instance )* S_SC
  |  O_pulldown ( pulldown_strength )?  pull_gate_instance ( S_CM pull_gate_instance )* S_SC
  |  O_pullup ( pullup_strength )?  pull_gate_instance ( S_CM pull_gate_instance )* S_SC
  ;

cmos_switch_instance
  :   ( name_of_instance )? S_LM output_terminal S_CM input_terminal S_CM ncontrol_terminal S_CM pcontrol_terminal S_RM
  ;

enable_gate_instance
  :   ( name_of_instance )? S_LM output_terminal S_CM input_terminal S_CM enable_terminal S_RM
  ;

mos_switch_instance
  :   ( name_of_instance )? S_LM output_terminal S_CM input_terminal S_CM enable_terminal S_RM
  ;

n_input_gate_instance
  :   ( name_of_instance )? S_LM output_terminal S_CM input_terminal ( S_CM input_terminal )* S_RM
  ;

n_output_gate_instance
  :   ( name_of_instance )? S_LM output_terminal ( S_CM output_terminal )* S_CM input_terminal S_RM
  ;

pass_switch_instance
  :   ( name_of_instance )? S_LM inout_terminal S_CM inout_terminal S_RM
  ;

pass_enable_switch_instance
  :   ( name_of_instance )? S_LM inout_terminal S_CM inout_terminal S_CM enable_terminal S_RM
  ;

pull_gate_instance
  :   ( name_of_instance )? S_LM output_terminal S_RM
  ;

// A.3.2 Primitive strengths

pulldown_strength 
  :  S_LM strength0 S_CM strength1 S_RM
  |  S_LM strength1 S_CM strength0 S_RM
  |  S_LM strength0 S_RM
  ;

pullup_strength 
  :  S_LM strength0 S_CM strength1 S_RM
  |  S_LM strength1 S_CM strength0 S_RM
  |  S_LM strength1 S_RM
  ;

// A.3.3 Primitive terminals

enable_terminal
  :  expression
  ;

inout_terminal
  :  net_lvalue
  ;

input_terminal
  :  expression
  ;

ncontrol_terminal
  :  expression
  ;

output_terminal
  :  net_lvalue
  ;

pcontrol_terminal
  :  expression
  ;

// A.3.4 Primitive gate and switch types

cmos_switchtype
  :  O_cmos | O_rcmos
  ;

enable_gatetype
  :  O_bufif0 | O_bufif1 | O_notif0 | O_notif1
  ;

mos_switchtype
  :  O_nmos | O_pmos | O_rnmos | O_rpmos
  ;

n_input_gatetype
  :  O_and | O_nand | O_or | O_nor | O_xor | O_xnor
  ;

n_output_gatetype
  :  O_buf | O_not
  ;

pass_en_switchtype
  :  O_tranif0 | O_tranif1 | O_rtranif1 | O_rtranif0
  ;

pass_switchtype
  :  O_tran | O_rtran
  ;

// A.4 Instantiations
// A.4.1 Instantiation
// A.4.1.1 Module instantiation

module_instantiation 
  :  module_identifier ( parameter_value_assignment )? hierarchical_instance ( S_CM hierarchical_instance )* S_SC
  ;

parameter_value_assignment
  :  S_SH S_LM ( list_of_parameter_assignments )? S_RM
  ;

list_of_parameter_assignments 
  :  ordered_parameter_assignment ( S_CM ordered_parameter_assignment )*
  |  named_parameter_assignment ( S_CM named_parameter_assignment )*
  ;

ordered_parameter_assignment
  :  param_expression
  ;

named_parameter_assignment
  :  S_DT parameter_identifier S_LM ( param_expression )? S_RM
  ;

hierarchical_instance
  :  name_of_instance S_LM ( list_of_port_connections )? S_RM
  ;

name_of_instance
  :  instance_identifier ( unpacked_dimension )*
  ;

list_of_port_connections
  :  ordered_port_connection ( S_CM ordered_port_connection )*
  |  named_port_connection ( S_CM named_port_connection )*
  ;

ordered_port_connection
  :  ( attribute_instance )* ( expression )?
  ;

named_port_connection 
  :  ( attribute_instance )* S_DT port_identifier ( S_LM ( expression )? S_RM )?
  |  ( attribute_instance )* S_DT_AS
  ;

// A.4.1.2 Interface instantiation

interface_instantiation 
  :  interface_identifier ( parameter_value_assignment )? hierarchical_instance ( S_CM hierarchical_instance )* S_SC
  ;

// A.4.1.3 Program instantiation

program_instantiation 
  :  program_identifier ( parameter_value_assignment )? hierarchical_instance ( S_CM hierarchical_instance )* S_SC
  ;

// A.4.1.4 Checker instantiation

checker_instantiation 
  :  ps_checker_identifier name_of_instance S_LM ( list_of_checker_port_connections )? S_RM S_SC
  ;

list_of_checker_port_connections
  :  ordered_checker_port_connection ( S_CM ordered_checker_port_connection )*
  |  named_checker_port_connection ( S_CM named_checker_port_connection )*
  ;

ordered_checker_port_connection
  :  ( attribute_instance )* ( property_actual_arg )?
  ;

named_checker_port_connection 
  :  ( attribute_instance )* S_DT formal_port_identifier ( S_LM ( property_actual_arg )? S_RM )?
  |  ( attribute_instance )* S_DT_AS
  ;

// A.4.2 Generated instantiation

generate_region 
  :  B_generate ( generate_item )* B_endgenerate
  ;

loop_generate_construct 
  :  K_for S_LM genvar_initialization S_SC genvar_expression S_SC genvar_iteration S_RM generate_block
  ;

genvar_initialization 
  :   ( T_genvar )? genvar_identifier S_EQ constant_expression
  ;

genvar_iteration 
  :  genvar_identifier assignment_operator genvar_expression
  |  inc_or_dec_operator genvar_identifier
  |  genvar_identifier inc_or_dec_operator
  ;

conditional_generate_construct 
  :  if_generate_construct
  |  case_generate_construct
  ;

if_generate_construct 
  :  K_if S_LM constant_expression S_RM generate_block ( K_else generate_block )?
  ;

case_generate_construct 
  :  B_case S_LM constant_expression S_RM case_generate_item ( case_generate_item )* B_endcase
  ;

case_generate_item 
  :  constant_expression ( S_CM constant_expression )* S_CO generate_block
  |  K_default ( S_CO )? generate_block
  ;

generate_block 
  :  generate_item
  |   ( generate_block_identifier S_CO )? B_begin ( S_CO generate_block_identifier )? ( generate_item )* B_end ( S_CO generate_block_identifier )?
  ;

generate_item
  :  module_or_generate_item
  |  interface_or_generate_item
  |  checker_or_generate_item
  ;

// A.5 UDP declaration and instantiation
// A.5.1 UDP declaration

udp_nonansi_declaration 
  :  ( attribute_instance )* B_primitive udp_identifier S_LM udp_port_list S_RM S_SC
  ;

udp_ansi_declaration 
  :  ( attribute_instance )* B_primitive udp_identifier S_LM udp_declaration_port_list S_RM S_SC
  ;

udp_declaration 
  :  udp_nonansi_declaration udp_port_declaration ( udp_port_declaration )* udp_body B_endprimitive ( S_CO udp_identifier )?
  |  udp_ansi_declaration udp_body B_endprimitive ( S_CO udp_identifier )?
  |  K_extern udp_nonansi_declaration
  |  K_extern udp_ansi_declaration
  |  ( attribute_instance )* B_primitive udp_identifier S_LM S_DT_AS S_RM S_SC ( udp_port_declaration )* udp_body B_endprimitive ( S_CO udp_identifier )?
  ;

// A.5.2 UDP ports

udp_port_list
  :  output_port_identifier S_CM input_port_identifier ( S_CM input_port_identifier )*
  ;

udp_declaration_port_list
  :  udp_output_declaration S_CM udp_input_declaration ( S_CM udp_input_declaration )*
  ;

udp_port_declaration 
  :  udp_output_declaration S_SC
  |  udp_input_declaration S_SC
  |  udp_reg_declaration S_SC
  ;

udp_output_declaration 
  :  ( attribute_instance )* T_output port_identifier
  |  ( attribute_instance )* T_output T_reg port_identifier ( S_EQ constant_expression )?
  ;

udp_input_declaration
  :  ( attribute_instance )* T_input list_of_udp_port_identifiers
  ;

udp_reg_declaration
  :  ( attribute_instance )* T_reg variable_identifier
  ;

// A.5.3 UDP body

udp_body
  :  combinational_body | sequential_body
  ;

combinational_body
  :  B_table combinational_entry ( combinational_entry )* B_endtable
  ;

//[Mod]
combinational_entry
  :  level_input_list S_CO_EDGE S_Level S_SC_EDGE
  ;

sequential_body
  :   ( udp_initial_statement )? B_table sequential_entry ( sequential_entry )* B_endtable
  ;

//[Mod]
udp_initial_statement
  :  K_initial output_port_identifier S_EQ scalar_number S_SC
  ;

sequential_entry
  :  seq_input_list S_CO_EDGE current_state S_CO_EDGE next_state S_SC_EDGE
  ;

seq_input_list
  :  level_input_list | edge_input_list
  ;

level_input_list
  :  S_Level ( S_Level )*
  ;

edge_input_list
  :  ( S_Level )* edge_indicator ( S_Level )*
  ;

edge_indicator
  :  S_LM_EDGE S_Level S_Level S_RM_EDGE | S_Edge
  ;

current_state
  :  S_Level
  ;

//[Mod]
next_state
  :  S_Level | S_MI_EDGE
  ;

// A.5.4 UDP instantiation

udp_instantiation
  :  udp_identifier ( drive_strength )? ( delay2 )? udp_instance ( S_CM udp_instance )* S_SC
  ;

udp_instance
  :   ( name_of_instance )? S_LM output_terminal S_CM input_terminal ( S_CM input_terminal )* S_RM
  ;

// A.6 Behavioral statements
// A.6.1 Continuous assignment and net alias statements

continuous_assign 
  :  K_assign ( drive_strength )? ( delay3 )? list_of_net_assignments S_SC
  |  K_assign ( delay_control )? list_of_variable_assignments S_SC
  ;

list_of_net_assignments
  :  net_assignment ( S_CM net_assignment )*
  ;

list_of_variable_assignments
  :  variable_assignment ( S_CM variable_assignment )*
  ;

net_alias
  :  K_alias net_lvalue S_EQ net_lvalue ( S_EQ net_lvalue )* S_SC
  ;

net_assignment
  :  net_lvalue S_EQ expression
  ;

// A.6.2 Procedural blocks and assignments

initial_construct
  :  K_initial statement_or_null
  ;

always_construct
  :  always_keyword statement
  ;

always_keyword
  :  K_always | K_always_comb | K_always_latch | K_always_ff
  ;

final_construct
  :  T_final function_statement
  ;

blocking_assignment 
  :  variable_lvalue S_EQ delay_or_event_control expression
  |  nonrange_variable_lvalue S_EQ dynamic_array_new
  |   ( implicit_class_handle S_DT | class_scope | package_scope )? hierarchical_variable_identifier select S_EQ class_new
  |  operator_assignment
  ;

operator_assignment
  :  variable_lvalue assignment_operator expression
  ;

assignment_operator 
  :  S_EQ | S_PL_EQ | S_MI_EQ | S_AS_EQ | S_DV_EQ | S_PE_EQ | S_AN_EQ | S_OR_EQ | S_XO_EQ | S_LB_LB_EQ | S_RB_RB_EQ | S_LB_LB_LB_EQ | S_RB_RB_RB_EQ
  ;

nonblocking_assignment 
  :  variable_lvalue S_LB_EQ ( delay_or_event_control )? expression
  ;

procedural_continuous_assignment 
  :  K_assign variable_assignment
  |  K_deassign variable_lvalue
  |  K_force variable_assignment
  |  K_force net_assignment
  |  K_release variable_lvalue
  |  K_release net_lvalue
  ;

variable_assignment
  :  variable_lvalue S_EQ expression
  ;

// A.6.3 Parallel and sequential blocks

action_block 
  :  statement_or_null
  |   ( statement )? K_else statement_or_null
  ;

seq_block 
  :  B_begin ( S_CO block_identifier )? ( block_item_declaration )* ( statement_or_null )* B_end ( S_CO block_identifier )?
  ;

par_block 
  :  K_fork ( S_CO block_identifier )? ( block_item_declaration )* ( statement_or_null )* join_keyword ( S_CO block_identifier )?
  ;

join_keyword
  :  K_join | K_join_any | K_join_none
  ;

// A.6.4 Statements

statement_or_null 
  :  statement
  |  ( attribute_instance )* S_SC
  ;

statement
  :   ( block_identifier S_CO )? ( attribute_instance )* statement_item
  ;

statement_item 
  :  blocking_assignment S_SC
  |  nonblocking_assignment S_SC
  |  procedural_continuous_assignment S_SC
  |  case_statement
  |  conditional_statement
  |  inc_or_dec_expression S_SC
  |  subroutine_call_statement
  |  disable_statement
  |  event_trigger
  |  loop_statement
  |  jump_statement
  |  par_block
  |  procedural_timing_control_statement
  |  seq_block
  |  wait_statement
  |  procedural_assertion_statement
  |  clocking_drive S_SC
  |  randsequence_statement
  |  randcase_statement
  |  expect_property_statement
  ;

function_statement
  :  statement
  ;

function_statement_or_null 
  :  function_statement
  |  ( attribute_instance )* S_SC
  ;

variable_identifier_list
  :  variable_identifier ( S_CM variable_identifier )*
  ;

// A.6.5 Timing control statements

procedural_timing_control_statement 
  :  procedural_timing_control statement_or_null
  ;

delay_or_event_control 
  :  delay_control
  |  event_control
  |  K_repeat S_LM expression S_RM event_control
  ;

delay_control 
  :  S_SH delay_value
  |  S_SH S_LM mintypmax_expression S_RM
  ;

event_control 
  :  S_AT hierarchical_event_identifier
  |  S_AT S_LM event_expression S_RM
  |  S_AT_AS
  |  S_AT S_LM_AS_RM
  |  S_AT ps_or_hierarchical_sequence_identifier
  ;

event_expression
  :   ( edge_identifier )? expression ( K_iff expression )?
  |  sequence_instance ( K_iff expression )?
  |  <assoc=right> event_expression O_or event_expression
  |  <assoc=right> event_expression S_CM event_expression
  |  S_LM event_expression S_RM
  ;

procedural_timing_control 
  :  delay_control
  |  event_control
  |  cycle_delay
  ;

jump_statement 
  :  K_return ( expression )? S_SC
  |  K_break S_SC
  |  K_continue S_SC
  ;

wait_statement 
  :  K_wait S_LM expression S_RM statement_or_null
  |  K_wait K_fork S_SC
  |  K_wait_order S_LM hierarchical_identifier ( S_CM hierarchical_identifier )* S_RM action_block
  ;

event_trigger 
  :  S_MI_RB hierarchical_event_identifier S_SC
  |  S_MI_RB_RB ( delay_or_event_control )? hierarchical_event_identifier S_SC
  ;

disable_statement 
  :  K_disable hierarchical_task_identifier S_SC
  |  K_disable hierarchical_block_identifier S_SC
  |  K_disable K_fork S_SC
  ;

// A.6.6 Conditional statements

conditional_statement 
  :   ( unique_priority )? K_if S_LM cond_predicate S_RM statement_or_null ( K_else K_if S_LM cond_predicate S_RM statement_or_null )* ( K_else statement_or_null )?
  ;

unique_priority
  :  K_unique | K_unique0 | K_priority
  ;

cond_predicate 
  :  expression ( K_matches pattern )? ( S_AN_AN_AN expression ( K_matches pattern )? )*
  ;

//[mod]
//expression_or_cond_pattern 
//  :  expression
//  |  cond_pattern
//  ;
//
//cond_pattern
//  :  expression K_matches pattern
//  ;

// A.6.7 Case statements

case_statement 
  :   ( unique_priority )? case_keyword S_LM case_expression S_RM case_item ( case_item )* B_endcase
  |   ( unique_priority )? case_keyword S_LM case_expression S_RM K_matches case_pattern_item ( case_pattern_item )* B_endcase
  |   ( unique_priority )? B_case S_LM case_expression S_RM K_inside case_inside_item ( case_inside_item )* B_endcase
  ;

case_keyword
  :  B_case | B_casez | B_casex
  ;

case_expression
  :  expression
  ;

case_item 
  :  case_item_expression ( S_CM case_item_expression )* S_CO statement_or_null
  |  K_default ( S_CO )? statement_or_null
  ;

case_pattern_item 
  :  pattern ( S_AN_AN_AN expression )? S_CO statement_or_null
  |  K_default ( S_CO )? statement_or_null
  ;

case_inside_item 
  :  open_range_list S_CO statement_or_null
  |  K_default ( S_CO )? statement_or_null
  ;

case_item_expression
  :  expression
  ;

randcase_statement 
  :  K_randcase randcase_item ( randcase_item )* B_endcase
  ;

randcase_item
  :  expression S_CO statement_or_null
  ;

open_range_list
  :  open_value_range ( S_CM open_value_range )*
  ;

open_value_range
  :  value_range
  ;

// A.6.7.1 Patterns

pattern 
  :  S_DT variable_identifier
  |  S_DT_AS
  |  constant_expression
  |  T_tagged member_identifier ( pattern )?
  |  S_SQ_LN pattern ( S_CM pattern )* S_RN
  |  S_SQ_LN member_identifier S_CO pattern ( S_CM member_identifier S_CO pattern )* S_RN
  ;

assignment_pattern 
  :  S_SQ_LN expression ( S_CM expression )* S_RN
  |  S_SQ_LN structure_pattern_key S_CO expression ( S_CM structure_pattern_key S_CO expression )* S_RN
  |  S_SQ_LN array_pattern_key S_CO expression ( S_CM array_pattern_key S_CO expression )* S_RN
  |  S_SQ_LN constant_expression S_LN expression ( S_CM expression )* S_RN S_RN
  ;

structure_pattern_key
  :  member_identifier | assignment_pattern_key
  ;

array_pattern_key
  :  constant_expression | assignment_pattern_key
  ;

assignment_pattern_key
  :  simple_type | K_default
  ;

assignment_pattern_expression 
  :   ( assignment_pattern_expression_type )? assignment_pattern
  ;

assignment_pattern_expression_type 
  :  ps_type_identifier
  |  ps_parameter_identifier
  |  integer_atom_type
  |  type_reference
  ;

constant_assignment_pattern_expression
  :  assignment_pattern_expression
  ;

assignment_pattern_net_lvalue 
  :  S_SQ_LN net_lvalue ( S_CM net_lvalue )* S_RN
  ;

assignment_pattern_variable_lvalue 
  :  S_SQ_LN variable_lvalue ( S_CM variable_lvalue )* S_RN
  ;

// A.6.8 Looping statements

loop_statement 
  :  K_forever statement_or_null
  |  K_repeat S_LM expression S_RM statement_or_null
  |  K_while S_LM expression S_RM statement_or_null
  |  K_for S_LM ( for_initialization )? S_SC ( expression )? S_SC ( for_step )? S_RM statement_or_null
  |  K_do statement_or_null K_while S_LM expression S_RM S_SC
  |  K_foreach S_LM ps_or_hierarchical_array_identifier S_LK loop_variables S_RK S_RM statement
  ;

for_initialization 
  :  list_of_variable_assignments
  |  for_variable_declaration ( S_CM for_variable_declaration )*
  ;

for_variable_declaration 
  :   ( T_var )? data_type variable_identifier S_EQ expression ( S_CM variable_identifier S_EQ expression )*
  ;

for_step
  :  for_step_assignment ( S_CM for_step_assignment )*
  ;

for_step_assignment 
  :  operator_assignment
  |  inc_or_dec_expression
  |  function_subroutine_call
  ;

loop_variables
  :   ( index_variable_identifier )? ( S_CM ( index_variable_identifier )? )*
  ;

// A.6.9 Subroutine call statements

subroutine_call_statement 
  :  subroutine_call S_SC
  |  T_void S_SQ S_LM function_subroutine_call S_RM S_SC
  ;

// A.6.10 Assertion statements

assertion_item 
  :  concurrent_assertion_item
  |  deferred_immediate_assertion_item
  ;

deferred_immediate_assertion_item
  :   ( block_identifier S_CO )? deferred_immediate_assertion_statement
  ;

procedural_assertion_statement 
  :  concurrent_assertion_statement
  |  immediate_assertion_statement
  |  checker_instantiation
  ;

immediate_assertion_statement 
  :  simple_immediate_assertion_statement
  |  deferred_immediate_assertion_statement
  ;

simple_immediate_assertion_statement 
  :  simple_immediate_assert_statement
  |  simple_immediate_assume_statement
  |  simple_immediate_cover_statement
  ;

simple_immediate_assert_statement 
  :  K_assert S_LM expression S_RM action_block
  ;

simple_immediate_assume_statement 
  :  K_assume S_LM expression S_RM action_block
  ;

simple_immediate_cover_statement 
  :  K_cover S_LM expression S_RM statement_or_null
  ;

deferred_immediate_assertion_statement 
  :  deferred_immediate_assert_statement
  |  deferred_immediate_assume_statement
  |  deferred_immediate_cover_statement
  ;

deferred_immediate_assert_statement 
  :  K_assert S_SH_0 S_LM expression S_RM action_block
  |  K_assert T_final S_LM expression S_RM action_block
  ;

deferred_immediate_assume_statement 
  :  K_assume S_SH_0 S_LM expression S_RM action_block
  |  K_assume T_final S_LM expression S_RM action_block
  ;

deferred_immediate_cover_statement 
  :  K_cover S_SH_0 S_LM expression S_RM statement_or_null
  |  K_cover T_final S_LM expression S_RM statement_or_null
  ;

// A.6.11 Clocking block

clocking_declaration
  :   ( K_default )? B_clocking ( clocking_identifier )? clocking_event S_SC ( clocking_item )* B_endclocking ( S_CO clocking_identifier )?
  |  K_global B_clocking ( clocking_identifier )? clocking_event S_SC B_endclocking ( S_CO clocking_identifier )?
  ;

clocking_event 
  :  S_AT identifier
  |  S_AT S_LM event_expression S_RM
  ;

clocking_item 
  :  K_default default_skew S_SC
  |  clocking_direction list_of_clocking_decl_assign S_SC
  |  ( attribute_instance )* assertion_item_declaration
  ;

default_skew 
  :  T_input clocking_skew
  |  T_output clocking_skew
  |  T_input clocking_skew T_output clocking_skew
  ;

clocking_direction 
  :  T_input ( clocking_skew )?
  |  T_output ( clocking_skew )?
  |  T_input ( clocking_skew )? T_output ( clocking_skew )?
  |  T_inout
  ;

list_of_clocking_decl_assign
  :  clocking_decl_assign ( S_CM clocking_decl_assign )*
  ;

clocking_decl_assign
  :  signal_identifier ( S_EQ expression )?
  ;

clocking_skew 
  :  edge_identifier ( delay_control )?
  |  delay_control
  ;

clocking_drive 
  :  clockvar_expression S_LB_EQ ( cycle_delay )? expression
  ;

cycle_delay 
  :  S_SH_SH integral_number
  |  S_SH_SH identifier
  |  S_SH_SH S_LM expression S_RM
  ;

clockvar
  :  hierarchical_identifier
  ;

clockvar_expression
  :  clockvar select
  ;

// A.6.12 Randsequence

randsequence_statement
  :  K_randsequence S_LM ( production_identifier )? S_RM production ( production )* B_endsequence
  ;

production
  :   ( data_type_or_void )? production_identifier ( S_LM tf_port_list S_RM )? S_CO rs_rule ( S_OR rs_rule )* S_SC
  ;

rs_rule
  :  rs_production_list ( S_CO_EQ weight_specification ( rs_code_block )? )?
  ;

rs_production_list 
  :  rs_prod ( rs_prod )*
  |  K_rand K_join ( S_LM expression S_RM )? production_item production_item ( production_item )*
  ;

weight_specification 
  :  integral_number
  |  ps_identifier
  |  S_LM expression S_RM
  ;

rs_code_block
  :  S_LN ( data_declaration )* ( statement_or_null )* S_RN
  ;

rs_prod 
  :  production_item
  |  rs_code_block
  |  rs_if_else
  |  rs_repeat
  |  rs_case
  ;

production_item
  :  production_identifier ( S_LM list_of_arguments S_RM )?
  ;

rs_if_else
  :  K_if S_LM expression S_RM production_item ( K_else production_item )?
  ;

rs_repeat
  :  K_repeat S_LM expression S_RM production_item
  ;

rs_case
  :  B_case S_LM case_expression S_RM rs_case_item ( rs_case_item )* B_endcase
  ;

rs_case_item 
  :  case_item_expression ( S_CM case_item_expression )* S_CO production_item S_SC
  |  K_default ( S_CO )? production_item S_SC
  ;

// A.7 Specify section
// A.7.1 Specify block declaration

specify_block
  :  B_specify ( specify_item )* B_endspecify
  ;

specify_item 
  :  specparam_declaration
  |  pulsestyle_declaration
  |  showcancelled_declaration
  |  path_declaration
  |  system_timing_check
  ;

pulsestyle_declaration 
  :  K_pulsestyle_onevent list_of_path_outputs S_SC
  |  K_pulsestyle_ondetect list_of_path_outputs S_SC
  ;

showcancelled_declaration 
  :  K_showcancelled list_of_path_outputs S_SC
  |  K_noshowcancelled list_of_path_outputs S_SC
  ;

// A.7.2 Specify path declarations

path_declaration 
  :  simple_path_declaration S_SC
  |  edge_sensitive_path_declaration S_SC
  |  state_dependent_path_declaration S_SC
  ;

simple_path_declaration 
  :  parallel_path_description S_EQ path_delay_value
  |  full_path_description S_EQ path_delay_value
  ;

parallel_path_description 
  :  S_LM specify_input_terminal_descriptor ( polarity_operator )? S_EQ_RB specify_output_terminal_descriptor S_RM
  ;

full_path_description 
  :  S_LM list_of_path_inputs ( polarity_operator )? S_AS_RB list_of_path_outputs S_RM
  ;

list_of_path_inputs 
  :  specify_input_terminal_descriptor ( S_CM specify_input_terminal_descriptor )*
  ;

list_of_path_outputs 
  :  specify_output_terminal_descriptor ( S_CM specify_output_terminal_descriptor )*
  ;

// A.7.3 Specify block terminals

specify_input_terminal_descriptor 
  :  input_identifier ( S_LK constant_range_expression S_RK )?
  ;

specify_output_terminal_descriptor 
  :  output_identifier ( S_LK constant_range_expression S_RK )?
  ;

input_identifier
  :  input_port_identifier | inout_port_identifier | interface_identifier S_DT port_identifier
  ;

output_identifier
  :  output_port_identifier | inout_port_identifier | interface_identifier S_DT port_identifier
  ;

// A.7.4 Specify path delays

path_delay_value 
  :  list_of_path_delay_expressions
  |  S_LM list_of_path_delay_expressions S_RM
  ;

list_of_path_delay_expressions 
  :  t_path_delay_expression
  |  trise_path_delay_expression S_CM tfall_path_delay_expression
  |  trise_path_delay_expression S_CM tfall_path_delay_expression S_CM tz_path_delay_expression
  |  t01_path_delay_expression S_CM t10_path_delay_expression S_CM t0z_path_delay_expression S_CM tz1_path_delay_expression S_CM t1z_path_delay_expression S_CM tz0_path_delay_expression
  |  t01_path_delay_expression S_CM t10_path_delay_expression S_CM t0z_path_delay_expression S_CM tz1_path_delay_expression S_CM t1z_path_delay_expression S_CM tz0_path_delay_expression S_CM t0x_path_delay_expression S_CM tx1_path_delay_expression S_CM t1x_path_delay_expression S_CM tx0_path_delay_expression S_CM txz_path_delay_expression S_CM tzx_path_delay_expression
  ;

t_path_delay_expression
  :  path_delay_expression
  ;

trise_path_delay_expression
  :  path_delay_expression
  ;

tfall_path_delay_expression
  :  path_delay_expression
  ;

tz_path_delay_expression
  :  path_delay_expression
  ;

t01_path_delay_expression
  :  path_delay_expression
  ;

t10_path_delay_expression
  :  path_delay_expression
  ;

t0z_path_delay_expression
  :  path_delay_expression
  ;

tz1_path_delay_expression
  :  path_delay_expression
  ;

t1z_path_delay_expression
  :  path_delay_expression
  ;

tz0_path_delay_expression
  :  path_delay_expression
  ;

t0x_path_delay_expression
  :  path_delay_expression
  ;

tx1_path_delay_expression
  :  path_delay_expression
  ;

t1x_path_delay_expression
  :  path_delay_expression
  ;

tx0_path_delay_expression
  :  path_delay_expression
  ;

txz_path_delay_expression
  :  path_delay_expression
  ;

tzx_path_delay_expression
  :  path_delay_expression
  ;

path_delay_expression
  :  constant_mintypmax_expression
  ;

edge_sensitive_path_declaration 
  :  parallel_edge_sensitive_path_description S_EQ path_delay_value
  |  full_edge_sensitive_path_description S_EQ path_delay_value
  ;

parallel_edge_sensitive_path_description 
  :  S_LM ( edge_identifier )? specify_input_terminal_descriptor ( polarity_operator )? S_EQ_RB S_LM specify_output_terminal_descriptor ( polarity_operator )? S_CO data_source_expression S_RM S_RM
  ;

full_edge_sensitive_path_description 
  :  S_LM ( edge_identifier )? list_of_path_inputs ( polarity_operator )? S_AS_RB S_LM list_of_path_outputs ( polarity_operator )? S_CO data_source_expression S_RM S_RM
  ;

data_source_expression
  :  expression
  ;

edge_identifier
  :  T_posedge | T_negedge | T_edge
  ;

state_dependent_path_declaration 
  :  K_if S_LM module_path_expression S_RM simple_path_declaration
  |  K_if S_LM module_path_expression S_RM edge_sensitive_path_declaration
  |  K_ifnone simple_path_declaration
  ;

polarity_operator
  :  S_PL | S_MI
  ;

// A.7.5 System timing checks
// A.7.5.1 System timing check commands

system_timing_check 
  :  dol_setup_timing_check
  |  dol_hold_timing_check
  |  dol_setuphold_timing_check
  |  dol_recovery_timing_check
  |  dol_removal_timing_check
  |  dol_recrem_timing_check
  |  dol_skew_timing_check
  |  dol_timeskew_timing_check
  |  dol_fullskew_timing_check
  |  dol_period_timing_check
  |  dol_width_timing_check
  |  dol_nochange_timing_check
  ;

dol_setup_timing_check 
  :  D_setup S_LM data_event S_CM reference_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_hold_timing_check 
  :  D_hold S_LM reference_event S_CM data_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_setuphold_timing_check 
  :  D_setuphold S_LM reference_event S_CM data_event S_CM timing_check_limit S_CM timing_check_limit ( S_CM ( notifier )? ( S_CM ( timestamp_condition )? ( S_CM ( timecheck_condition )? ( S_CM ( delayed_reference )? ( S_CM ( delayed_data )? )? )? )? )? )? S_RM S_SC
  ;

dol_recovery_timing_check 
  :  D_recovery S_LM reference_event S_CM data_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_removal_timing_check 
  :  D_removal S_LM reference_event S_CM data_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_recrem_timing_check 
  :  D_recrem S_LM reference_event S_CM data_event S_CM timing_check_limit S_CM timing_check_limit ( S_CM ( notifier )? ( S_CM ( timestamp_condition )? ( S_CM ( timecheck_condition )? ( S_CM ( delayed_reference )? ( S_CM ( delayed_data )? )? )? )? )? )? S_RM S_SC
  ;

dol_skew_timing_check 
  :  D_skew S_LM reference_event S_CM data_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_timeskew_timing_check 
  :  D_timeskew S_LM reference_event S_CM data_event S_CM timing_check_limit ( S_CM ( notifier )? ( S_CM ( event_based_flag )? ( S_CM ( remain_active_flag )? )? )? )? S_RM S_SC
  ;

dol_fullskew_timing_check 
  :  D_fullskew S_LM reference_event S_CM data_event S_CM timing_check_limit S_CM timing_check_limit ( S_CM ( notifier )? ( S_CM ( event_based_flag )? ( S_CM ( remain_active_flag )? )? )? )? S_RM S_SC
  ;

dol_period_timing_check 
  :  D_period S_LM controlled_reference_event S_CM timing_check_limit ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_width_timing_check 
  :  D_width S_LM controlled_reference_event S_CM timing_check_limit S_CM threshold ( S_CM ( notifier )? )? S_RM S_SC
  ;

dol_nochange_timing_check 
  :  D_nochange S_LM reference_event S_CM data_event S_CM start_edge_offset S_CM end_edge_offset ( S_CM ( notifier )? )? S_RM
  ;

// A.7.5.2 System timing check command arguments

timecheck_condition
  :  mintypmax_expression
  ;

controlled_reference_event
  :  controlled_timing_check_event
  ;

data_event
  :  timing_check_event
  ;

delayed_data 
  :  terminal_identifier
  |  terminal_identifier S_LK constant_mintypmax_expression S_RK
  ;

delayed_reference 
  :  terminal_identifier
  |  terminal_identifier S_LK constant_mintypmax_expression S_RK
  ;

end_edge_offset
  :  mintypmax_expression
  ;

event_based_flag
  :  constant_expression
  ;

notifier
  :  variable_identifier
  ;

reference_event
  :  timing_check_event
  ;

remain_active_flag
  :  constant_mintypmax_expression
  ;

timestamp_condition
  :  mintypmax_expression
  ;

start_edge_offset
  :  mintypmax_expression
  ;

threshold
  :  constant_expression
  ;

timing_check_limit
  :  expression
  ;

// A.7.5.3 System timing check event definitions

timing_check_event 
  :  ( timing_check_event_control )? specify_terminal_descriptor ( S_AN_AN_AN timing_check_condition )?
  ;

controlled_timing_check_event 
  :  timing_check_event_control specify_terminal_descriptor ( S_AN_AN_AN timing_check_condition )?
  ;

timing_check_event_control 
  :  T_posedge
  |  T_negedge
  |  T_edge
  |  edge_control_specifier
  ;

specify_terminal_descriptor 
  :  specify_input_terminal_descriptor
  |  specify_output_terminal_descriptor
  ;

//[Mod]
edge_control_specifier
  :  T_edge edge_descriptor ( S_CM_EDGE edge_descriptor )* S_RK_EDGE
  ;

edge_descriptor
  :  S_ZO_OZ | S_Z_X S_Z_O | S_Z_O S_Z_X
  ;

timing_check_condition 
  :  scalar_timing_check_condition
  |  S_LM scalar_timing_check_condition S_RM
  ;

scalar_timing_check_condition 
  :  expression
  |  S_NE expression
  |  expression S_EQ_EQ scalar_number
  |  expression S_EQ_EQ_EQ scalar_number
  |  expression S_EX_EQ scalar_number
  |  expression S_EX_EQ_EQ scalar_number
  ;

// A.8 Expressions
// A.8.1 Concatenations

concatenation 
  :  S_LN expression ( S_CM expression )* S_RN
  ;

constant_concatenation 
  :  S_LN constant_expression ( S_CM constant_expression )* S_RN
  ;

constant_multiple_concatenation
  :  S_LN constant_expression constant_concatenation S_RN
  ;

module_path_concatenation
  :  S_LN module_path_expression ( S_CM module_path_expression )* S_RN
  ;

module_path_multiple_concatenation
  :  S_LN constant_expression module_path_concatenation S_RN
  ;

multiple_concatenation
  :  S_LN expression concatenation S_RN
  ;

streaming_concatenation
  :  S_LN stream_operator ( slice_size )? stream_concatenation S_RN
  ;

stream_operator
  :  S_RB_RB | S_LB_LB
  ;

slice_size
  :  simple_type | constant_expression
  ;

stream_concatenation
  :  S_LN stream_expression ( S_CM stream_expression )* S_RN
  ;

stream_expression
  :  expression ( K_with S_LK array_range_expression S_RK )?
  ;

array_range_expression 
  :  expression
  |  expression S_CO expression
  |  expression S_PL_CO expression
  |  expression S_MI_CO expression
  ;

empty_unpacked_array_concatenation
  :  S_LN S_RN
  ;

// A.8.2 Subroutine calls

constant_function_call
  :  function_subroutine_call
  ;

//[mod]
constant_function_call_t
  :  function_subroutine_call_t
  ;

tf_call
  :  ps_or_hierarchical_tf_identifier ( attribute_instance )* ( S_LM list_of_arguments S_RM )?
  ;

system_tf_call 
  :  system_tf_identifier ( S_LM list_of_arguments S_RM )?
  |  system_tf_identifier S_LM data_type ( S_CM expression )? S_RM
  |  system_tf_identifier S_LM expression ( S_CM ( expression )? )* ( S_CM ( clocking_event )? )? S_RM
  ;

subroutine_call 
  :  tf_call
  |  system_tf_call
  |  method_call
  |  ( K_std_CO_CO )? randomize_call
  ;

function_subroutine_call
  :  subroutine_call
  ;

//[mod]
function_subroutine_call_t
  :  tf_call
  |  system_tf_call
  |  ( K_std_CO_CO )? randomize_call
  ;

list_of_arguments 
  :   ( expression )? ( S_CM ( expression )? )* ( S_CM S_DT identifier S_LM ( expression )? S_RM )*
  |  S_DT identifier S_LM ( expression )? S_RM ( S_CM S_DT identifier S_LM ( expression )? S_RM )*
  ;

method_call
  :  method_call_root S_DT method_call_body
  ;

method_call_body 
  :  method_identifier ( attribute_instance )* ( S_LM list_of_arguments S_RM )?
  |  built_in_method_call
  ;

built_in_method_call 
  :  array_manipulation_call
  |  randomize_call
  ;

array_manipulation_call 
  :  array_method_name ( attribute_instance )* ( S_LM list_of_arguments S_RM )? ( K_with S_LM expression S_RM )?
  ;

randomize_call 
  :  K_randomize ( attribute_instance )* ( S_LM ( variable_identifier_list | T_null )? S_RM )? ( K_with ( S_LM ( identifier_list )? S_RM )? constraint_block )?
  ;

method_call_root
  :  primary
  |  implicit_class_handle
  ;

array_method_name 
  :  method_identifier | K_unique | O_and | O_or | O_xor
  ;

// A.8.3 Expressions

inc_or_dec_expression 
  :  inc_or_dec_operator ( attribute_instance )* variable_lvalue
  |  variable_lvalue ( attribute_instance )* inc_or_dec_operator
  ;
  
//[mod]
//conditional_expression
//  :  cond_predicate S_QU ( attribute_instance )* expression S_CO expression
//  ;

constant_expression
  :  constant_primary
  |  unary_operator ( attribute_instance )* constant_primary
  |  <assoc=right> constant_expression binary_operator ( attribute_instance )* constant_expression
  |  <assoc=right> constant_expression S_QU ( attribute_instance )* constant_expression S_CO constant_expression
  ;

constant_mintypmax_expression 
  :  constant_expression
  |  constant_expression S_CO constant_expression S_CO constant_expression
  ;

constant_param_expression 
  :  constant_mintypmax_expression | data_type | S_DL
  ;

param_expression
  :  mintypmax_expression | data_type | S_DL
  ;

constant_range_expression 
  :  constant_expression
  |  constant_part_select_range
  ;

constant_part_select_range 
  :  constant_range
  |  constant_indexed_range
  ;

constant_range
  :  constant_expression S_CO constant_expression
  ;

constant_indexed_range 
  :  constant_expression S_PL_CO constant_expression
  |  constant_expression S_MI_CO constant_expression
  ;

//[mod]
expression
  :  primary
  |  unary_operator ( attribute_instance )* primary
  |  inc_or_dec_expression
  |  S_LM operator_assignment S_RM
  |  <assoc=right> expression binary_operator ( attribute_instance )* expression
//|  conditional_expression
  |  <assoc=right> expression ( K_matches pattern )? ( S_AN_AN_AN expression ( K_matches pattern )? )* S_QU ( attribute_instance )* expression S_CO expression
//|  inside_expression
  |  <assoc=right> expression K_inside S_LN open_range_list S_RN
  |  tagged_union_expression
  ;

tagged_union_expression 
  :  T_tagged member_identifier ( expression )?
  ;
  
//[mod]
//inside_expression
//  :  expression K_inside S_LN open_range_list S_RN
//  ;

value_range 
  :  expression
  |  S_LK expression S_CO expression S_RK
  ;

mintypmax_expression 
  :  expression
  |  expression S_CO expression S_CO expression
  ;

//[mod]
//module_path_conditional_expression
//  :  <assoc=right> module_path_expression S_QU ( attribute_instance )* module_path_expression S_CO module_path_expression
//  ;

//[mod]
module_path_expression 
  :  module_path_primary
  |  unary_module_path_operator ( attribute_instance )* module_path_primary
  |  <assoc=right> module_path_expression binary_module_path_operator ( attribute_instance )* module_path_expression
//|  module_path_conditional_expression
  |  <assoc=right> module_path_expression S_QU ( attribute_instance )* module_path_expression S_CO module_path_expression
  ;

module_path_mintypmax_expression 
  :  module_path_expression
  |  module_path_expression S_CO module_path_expression S_CO module_path_expression
  ;

part_select_range
  :  constant_range | indexed_range
  ;

indexed_range 
  :  expression S_PL_CO constant_expression
  |  expression S_MI_CO constant_expression
  ;

genvar_expression
  :  constant_expression
  ;

// A.8.4 Primaries

//[mod]
constant_primary 
  :  primary_literal
  |  ps_parameter_identifier constant_select
  |  specparam_identifier ( S_LK constant_range_expression S_RK )?
  |  genvar_identifier
  |  formal_port_identifier constant_select
  |   ( package_scope | class_scope )? enum_identifier
  |  constant_concatenation ( S_LK constant_range_expression S_RK )?
  |  constant_multiple_concatenation ( S_LK constant_range_expression S_RK )?
//|  constant_function_call
  |  constant_function_call_t
  |  constant_let_expression
  |  S_LM constant_mintypmax_expression S_RM
//|  constant_cast
  |  <assoc=right> constant_primary S_SQ S_LM expression S_RM
  |  casting_type_t S_SQ S_LM expression S_RM
  |  constant_assignment_pattern_expression
  |  type_reference
  |  T_null
  ;

module_path_primary 
  :  number
  |  identifier
  |  module_path_concatenation
  |  module_path_multiple_concatenation
  |  function_subroutine_call
  |  S_LM module_path_mintypmax_expression S_RM
  ;

//[mod]
primary 
  :  primary_literal
  |   ( class_qualifier | package_scope )? hierarchical_identifier select
  |  empty_unpacked_array_concatenation
  |  concatenation ( S_LK range_expression S_RK )?
  |  multiple_concatenation ( S_LK range_expression S_RK )?
//|  function_subroutine_call
  |  function_subroutine_call_t
  |  <assoc=right> primary S_DT method_call_body
  |  let_expression
  |  S_LM mintypmax_expression S_RM
  |  cast
  |  assignment_pattern_expression
  |  streaming_concatenation
  |  sequence_method_call
  |  K_this
  |  S_DL
  |  T_null
  ;

class_qualifier
  :   ( T_local S_CO_CO )? ( implicit_class_handle S_DT | class_scope )?
  ;

range_expression 
  :  expression
  |  part_select_range
  ;

primary_literal
  :  number | L_Time | N_Unbased_unsized | L_String
  ;

implicit_class_handle
  :  K_this | K_super | K_this S_DT K_super
  ;

bit_select
  :  ( S_LK expression S_RK )*
  ;

select 
  :   ( ( S_DT member_identifier bit_select )* S_DT member_identifier )? bit_select ( S_LK part_select_range S_RK )?
  ;

nonrange_select 
  :   ( ( S_DT member_identifier bit_select )* S_DT member_identifier )? bit_select
  ;

constant_bit_select
  :  ( S_LK constant_expression S_RK )*
  ;

constant_select 
  :   ( ( S_DT member_identifier constant_bit_select )* S_DT member_identifier )? constant_bit_select ( S_LK constant_part_select_range S_RK )?
  ;

//[mod]
//constant_cast 
//  :  casting_type S_SQ S_LM constant_expression S_RM
//  ;

constant_let_expression
  :  let_expression
  ;

cast 
  :  casting_type S_SQ S_LM expression S_RM
  ;

// A.8.5 Expression left-side values

net_lvalue 
  :  ps_or_hierarchical_net_identifier constant_select
  |  S_LN net_lvalue ( S_CM net_lvalue )* S_RN
  |   ( assignment_pattern_expression_type )? assignment_pattern_net_lvalue
  ;

variable_lvalue 
  :   ( implicit_class_handle S_DT | package_scope )? hierarchical_variable_identifier select
  |  S_LN variable_lvalue ( S_CM variable_lvalue )* S_RN
  |   ( assignment_pattern_expression_type )? assignment_pattern_variable_lvalue
  |  streaming_concatenation
  ;

nonrange_variable_lvalue 
  :   ( implicit_class_handle S_DT | package_scope )? hierarchical_variable_identifier nonrange_select
  ;

// A.8.6 Operators

unary_operator 
  :  S_PL | S_MI | S_EX | S_NE | S_AN | S_NE_AN | S_OR | S_NE_OR | S_XO | S_NE_XO | S_XO_NE
  ;

binary_operator 
  :  S_PL | S_MI | S_AS | S_DV | S_PE | S_EQ_EQ | S_EX_EQ | S_EQ_EQ_EQ | S_EX_EQ_EQ | S_EQ_EQ_QU | S_EX_EQ_QU | S_AN_AN | S_OR_OR | S_AS_AS
  |  S_LB | S_LB_EQ | S_RB | S_RB_EQ | S_AN | S_OR | S_XO | S_XO_NE | S_NE_XO | S_RB_RB | S_LB_LB | S_RB_RB_RB | S_LB_LB_LB
  |  S_MI_RB | S_LB_MI_RB
  ;

inc_or_dec_operator
  :  S_PL_PL | S_MI_MI
  ;

unary_module_path_operator 
  :  S_EX | S_NE | S_AN | S_NE_AN | S_OR | S_NE_OR | S_XO | S_NE_XO | S_XO_NE
  ;

binary_module_path_operator 
  :  S_EQ_EQ | S_EX_EQ | S_AN_AN | S_OR_OR | S_AN | S_OR | S_XO | S_XO_NE | S_NE_XO
  ;

// A.8.7 Numbers

number 
  :  integral_number
  |  real_number
  ;

integral_number 
  : binary_number
  | hex_number
  | octal_number
  | decimal_number
  ;

//[Mod]
scalar_number
  : binary_number
  | N_Unsigned
  ;

decimal_number 
  :  ( size )? N_Dec
  | N_Unsigned
  ;

binary_number
  :  ( size )? N_Bin
  ;


octal_number
  :  ( size )? N_Oct
  ;


hex_number
  :  ( size )? N_Hex
  ;

size
  :  N_Unsigned
  ;

real_number
  :  N_Fix
  |  N_Exp
  ;

// A.8.8 Strings

// A.9 General
// A.9.1 Attributes

attribute_instance
  :  S_LM_AS attr_spec ( S_CM attr_spec )* S_AS_RM
  ;

attr_spec
  :  attr_name ( S_EQ constant_expression )?
  ;

attr_name
  :  identifier
  ;

// A.9.2 Comments

// A.9.3 Identifiers

array_identifier
  :  identifier
  ;

block_identifier
  :  identifier
  ;

bin_identifier
  :  identifier
  ;

c_identifier
  :   I_Simple
  ;

cell_identifier
  :  identifier
  ;

checker_identifier
  :  identifier
  ;

class_identifier
  :  identifier
  ;

class_variable_identifier
  :  variable_identifier
  ;

clocking_identifier
  :  identifier
  ;

config_identifier
  :  identifier
  ;

const_identifier
  :  identifier
  ;

constraint_identifier
  :  identifier
  ;

covergroup_identifier
  :  identifier
  ;

covergroup_variable_identifier
  :  variable_identifier
  ;

cover_point_identifier
  :  identifier
  ;

cross_identifier
  :  identifier
  ;

dynamic_array_variable_identifier
  :  variable_identifier
  ;

enum_identifier
  :  identifier
  ;

formal_identifier
  :  identifier
  ;

formal_port_identifier
  :  identifier
  ;

function_identifier
  :  identifier
  ;

generate_block_identifier
  :  identifier
  ;

genvar_identifier
  :  identifier
  ;

hierarchical_array_identifier
  :  hierarchical_identifier
  ;

hierarchical_block_identifier
  :  hierarchical_identifier
  ;

hierarchical_event_identifier
  :  hierarchical_identifier
  ;

hierarchical_identifier
  :   ( D_root S_DT )? ( identifier constant_bit_select S_DT )* identifier
  ;

hierarchical_net_identifier
  :  hierarchical_identifier
  ;

hierarchical_parameter_identifier
  :  hierarchical_identifier
  ;

hierarchical_property_identifier
  :  hierarchical_identifier
  ;

hierarchical_sequence_identifier
  :  hierarchical_identifier
  ;

hierarchical_task_identifier
  :  hierarchical_identifier
  ;

hierarchical_tf_identifier
  :  hierarchical_identifier
  ;

hierarchical_variable_identifier
  :  hierarchical_identifier
  ;

identifier 
  :  I_Simple
  |  I_Escaped
  ;

index_variable_identifier
  :  identifier
  ;

interface_identifier
  :  identifier
  ;

interface_instance_identifier
  :  identifier
  ;

inout_port_identifier
  :  identifier
  ;

input_port_identifier
  :  identifier
  ;

instance_identifier
  :  identifier
  ;

library_identifier
  :  identifier
  ;

member_identifier
  :  identifier
  ;

method_identifier
  :  identifier
  ;

modport_identifier
  :  identifier
  ;

module_identifier
  :  identifier
  ;

net_identifier
  :  identifier
  ;

net_type_identifier
  :  identifier
  ;

output_port_identifier
  :  identifier
  ;

package_identifier
  :  identifier
  ;

package_scope 
  :  package_identifier S_CO_CO
  |  D_unit S_CO_CO
  ;

parameter_identifier
  :  identifier
  ;

port_identifier
  :  identifier
  ;

production_identifier
  :  identifier
  ;

program_identifier
  :  identifier
  ;

property_identifier
  :  identifier
  ;

ps_class_identifier
  :   ( package_scope )? class_identifier
  ;

ps_covergroup_identifier
  :   ( package_scope )? covergroup_identifier
  ;

ps_checker_identifier
  :   ( package_scope )? checker_identifier
  ;

ps_identifier
  :   ( package_scope )? identifier
  ;

ps_or_hierarchical_array_identifier 
  :   ( implicit_class_handle S_DT | class_scope | package_scope )? hierarchical_array_identifier
  ;

ps_or_hierarchical_net_identifier
  :   ( package_scope )? net_identifier | hierarchical_net_identifier
  ;

ps_or_hierarchical_property_identifier 
  :   ( package_scope )? property_identifier
  |  hierarchical_property_identifier
  ;

ps_or_hierarchical_sequence_identifier 
  :   ( package_scope )? sequence_identifier
  |  hierarchical_sequence_identifier
  ;

ps_or_hierarchical_tf_identifier 
  :   ( package_scope )? tf_identifier
  |  hierarchical_tf_identifier
  ;

ps_parameter_identifier 
  :   ( package_scope | class_scope )? parameter_identifier
  |  ( generate_block_identifier ( S_LK constant_expression S_RK )? S_DT )* parameter_identifier
  ;

ps_type_identifier
  :   ( K_local_CO_CO| package_scope | class_scope )? type_identifier
  ;

sequence_identifier
  :  identifier
  ;

signal_identifier
  :  identifier
  ;

specparam_identifier
  :  identifier
  ;

system_tf_identifier
  :  I_System_tf
  ;

task_identifier
  :  identifier
  ;

tf_identifier
  :  identifier
  ;

terminal_identifier
  :  identifier
  ;

topmodule_identifier
  :  identifier
  ;

type_identifier
  :  identifier
  ;

udp_identifier
  :  identifier
  ;

variable_identifier
  :  identifier
  ;