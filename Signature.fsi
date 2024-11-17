module Signature

type FCT_NAME = string
type RULE_NAME = string

type NAME =
| UndefConst
| BoolConst of bool
| IntConst of int
| StringConst of string
| FctName of FCT_NAME

type ASSOCIATIVITY =
| LeftAssoc
| RightAssoc

type INFIX_STATUS =
| NonInfix
| Infix of ASSOCIATIVITY * int

type FCT_KIND =
| Static
| Monitored             // same as 'in'
| Controlled
| Shared
| Out 
| Derived

val fct_kind_to_string : FCT_KIND -> string

type TYPE =
| TypeParam of string
| Undef
| Boolean
| Integer
| String
| Rule
| BaseType of string
| Prod of TYPE list

val type_to_string : TYPE -> string
val type_list_to_string : TYPE list -> string

type TYPE_INFO = {
    arity   : int;
    maps_to : (TYPE list -> TYPE) option;    // None for user-defined types; Some ... for mapping type names to built-in types
}

type FCT_INFO = {
    fct_kind : FCT_KIND;
    fct_type : TYPE list * TYPE;
    infix_status : INFIX_STATUS
}

type RULE_INFO = {
    rule_type : TYPE list;
}

type NAME_INFO =
|   TypeInfo of TYPE_INFO       // names used for type parameters (declared using 'anydomain' in AsmetaL)
|   FctInfo of FCT_INFO
|   RuleInfo of RULE_INFO

type SIGNATURE = Map<FCT_NAME, NAME_INFO>

val empty_signature : SIGNATURE
val signature_override : SIGNATURE -> SIGNATURE -> SIGNATURE

val add_type_name : string -> int * (TYPE list -> TYPE) option -> SIGNATURE -> SIGNATURE
val add_function_name : string -> FCT_KIND * (TYPE list * TYPE) * INFIX_STATUS -> SIGNATURE -> SIGNATURE
val add_rule_name : string -> TYPE list -> SIGNATURE -> SIGNATURE

val fct_names  : SIGNATURE -> Set<string>
val rule_names : SIGNATURE -> Set<string>

val is_name_defined : string -> SIGNATURE -> bool
val is_function_name : string -> SIGNATURE -> bool
val is_rule_name : string -> SIGNATURE -> bool
val fct_kind : string -> SIGNATURE -> FCT_KIND
val fct_type : string -> SIGNATURE -> TYPE list * TYPE
val arity : string -> SIGNATURE -> int
val infix_status : string -> SIGNATURE -> INFIX_STATUS
val is_infix : string -> SIGNATURE -> bool
val is_left_assoc : string -> SIGNATURE -> bool
val is_right_assoc : string -> SIGNATURE -> bool
val precedence : string -> SIGNATURE -> int

val match_fct_type : string -> TYPE list -> (TYPE list * TYPE) -> TYPE
