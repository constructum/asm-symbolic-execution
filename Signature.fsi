module Signature

type FCT_NAME = string
type RULE_NAME = string

type ASSOCIATIVITY =
| LeftAssoc
| RightAssoc

type INFIX_STATUS =
| NonInfix
| Infix of ASSOCIATIVITY * int

type FCT_KIND =
| Constructor           // (static) constructor for inductive data types
| Static
| Monitored             // same as 'in'
| Controlled
| Shared
| Out 
| Derived

val fct_kind_to_string : FCT_KIND -> string
val infix_status_to_string : INFIX_STATUS -> string

type TYPE =
| Boolean
| Integer
| String
| Undef
| Rule
| TypeParam of string
| TypeCons of string * TYPE list
| Subset of string * TYPE
| Prod of TYPE list
| Seq of TYPE
| Powerset of TYPE
| Bag of TYPE
| Map of TYPE * TYPE

type NAME =
| UndefConst
| BoolConst of bool
| IntConst of int
| StringConst of string
| FctName of FCT_NAME

val type_to_string : TYPE -> string
val type_list_to_string : TYPE list -> string
val fct_type_to_string : TYPE list * TYPE -> string

type TYPE_KIND =
| BasicType
| AnyType           // type parameter (needed to implement AsmetaL's 'anydomain')
| EnumType          // inductive types - AsmetaL: enum / abstract domains
| SubsetType        // subset 'types'  - AsmetaL: concrete domains (i.e. subset of a basic or abstract domain)

val type_kind_to_string : TYPE_KIND -> string

type TYPE_INFO = {
    arity : int;
    type_kind : TYPE_KIND;
    maps_to : (TYPE list -> TYPE) option;  // None for user-declared types; Some ... for mapping type names to built-in types
}

type FCT_INFO = {
    fct_kind : FCT_KIND;
    infix_status : INFIX_STATUS
    fct_types : (TYPE list * TYPE) list;      // it is a list due to function overloading in AsmetaL
}

type RULE_INFO = {
    rule_type : TYPE list;
}

type NAME_INFO =
|   TypeInfo of TYPE_INFO       // names used for type parameters (declared using 'anydomain' in AsmetaL)
|   FctInfo of FCT_INFO
|   RuleInfo of RULE_INFO

type SIGNATURE = Map<FCT_NAME, NAME_INFO>

type ErrorDetails =
|   TypeMismatch of TYPE * TYPE
|   FunctionCallTypeMismatch of (string * TYPE list * TYPE) * TYPE list
|   TypeOfResultUnknown of string * TYPE list * TYPE
|   NoMatchingFunctionType of string * TYPE list
|   AmbiguousFunctionCall of string * TYPE list
|   NotAFunctionName of string
|   VariableAlreadyInUse of string
|   UnknownVariable of string

exception Error of ErrorDetails
val error_msg : ErrorDetails -> string

module TypeEnv =
    type TYPE_ENV = Map<string, TYPE>
    val empty : TYPE_ENV
    val get : string -> TYPE_ENV -> TYPE
    val add_distinct : string -> TYPE -> TYPE_ENV -> TYPE_ENV
    val add_overwrite : string -> TYPE -> TYPE_ENV -> TYPE_ENV

val empty_signature : SIGNATURE
val signature_override : SIGNATURE -> SIGNATURE -> SIGNATURE

val add_type_name : string -> int * TYPE_KIND * (TYPE list -> TYPE) option -> SIGNATURE -> SIGNATURE
val add_function_name : string -> FCT_KIND * INFIX_STATUS * (TYPE list * TYPE) -> SIGNATURE -> SIGNATURE
val add_rule_name : string -> TYPE list -> SIGNATURE -> SIGNATURE

val type_names  : SIGNATURE -> Set<string>
val fct_names  : SIGNATURE -> Set<string>
val rule_names : SIGNATURE -> Set<string>

val is_name_defined : string -> SIGNATURE -> bool

val construct_type : SIGNATURE -> (string * TYPE list) -> TYPE

val is_type_name : string -> SIGNATURE -> bool
val type_arity : string -> SIGNATURE -> int
val type_kind  : string -> SIGNATURE -> TYPE_KIND

val is_rule_name : string -> SIGNATURE -> bool

val is_function_name : string -> SIGNATURE -> bool
val fct_kind : string -> SIGNATURE -> FCT_KIND
val fct_types : string -> SIGNATURE -> list<TYPE list * TYPE>
val fct_type : string -> SIGNATURE -> TYPE list * TYPE
val infix_status : string -> SIGNATURE -> INFIX_STATUS
val is_infix : string -> SIGNATURE -> bool
val is_left_assoc : string -> SIGNATURE -> bool
val is_right_assoc : string -> SIGNATURE -> bool
val precedence : string -> SIGNATURE -> int

val main_type : TYPE -> TYPE
val match_type : TYPE -> TYPE -> TypeEnv.TYPE_ENV -> TypeEnv.TYPE_ENV
val match_fct_type : string -> TYPE list -> (TYPE list * TYPE) list -> TYPE

val signature_to_string : SIGNATURE -> string
