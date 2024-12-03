module Background

//--------------------------------------------------------------------

open Common
open Signature

//--------------------------------------------------------------------

type VALUE =
| UNDEF
| BOOL of bool
| INT of int
| STRING of string
| CELL of string * VALUE list     // for values of user-defined inductive data types
//| TUPLE of VALUE list

let TRUE = BOOL true
let FALSE = BOOL false

let rec value_to_string = function
|   UNDEF -> "undef"
|   BOOL b -> if b then "true" else "false"
|   INT i -> i.ToString ()
|   STRING s -> "\"" + s + "\""
|   CELL (tag, args) -> if List.isEmpty args then tag else tag + " (" + (args >>| value_to_string |> String.concat ", ") + ")"

let type_of_value (sign : SIGNATURE) (x : VALUE) =
    match x with
    |   UNDEF    -> Undef
    |   BOOL b   -> Boolean
    |   INT i    -> Integer
    |   STRING s -> String
    |   CELL (tag, _) -> let (_, ran) = fct_type tag sign in ran

//--------------------------------------------------------------------

type STATIC_STATE = Map<string, VALUE list -> VALUE>

//--------------------------------------------------------------------

let eq = function
| [ x : VALUE; y : VALUE ] -> BOOL(x = y)
| _ -> UNDEF

let neq = function
| [ x : VALUE; y : VALUE ] -> BOOL(x <> y)
| _ -> UNDEF

let gt = function
| [ UNDEF; UNDEF ] -> FALSE
| [ BOOL x; BOOL y ] -> BOOL (x > y)
| [ INT x; INT y ] -> BOOL (x > y)
| [ STRING x; STRING y ] -> BOOL (x > y)
| _ -> UNDEF

let ge = function
| [ UNDEF; UNDEF ] -> TRUE
| [ BOOL x; BOOL y ] -> BOOL (x >= y)
| [ INT x; INT y ] -> BOOL (x >= y)
| [ STRING x; STRING y ] -> BOOL (x >= y)
| _ -> UNDEF

let lt = function
| [ UNDEF; UNDEF ] -> FALSE
| [ BOOL x; BOOL y ] -> BOOL (x < y)
| [ INT x; INT y ] -> BOOL (x < y)
| [ STRING x; STRING y ] -> BOOL (x < y)
| _ -> UNDEF

let le = function
| [ UNDEF; UNDEF ] -> TRUE
| [ BOOL x; BOOL y ] -> BOOL (x <= y)
| [ INT x; INT y ] -> BOOL (x <= y)
| [ STRING x; STRING y ] -> BOOL (x <= y)
| _ -> UNDEF

let plus = function
| [ UNDEF; UNDEF ] -> UNDEF
| [ BOOL x; BOOL y ] -> BOOL (x || y)
| [ INT x; INT y ] -> INT (x + y)
| [ STRING x; STRING y ] -> STRING (x + y)
| _ -> UNDEF

let minus = function
| [ INT x; INT y ] -> INT (x - y)
| _ -> UNDEF

let times = function
| [ UNDEF; UNDEF ] -> UNDEF
| [ BOOL x; BOOL y ] -> BOOL (x && y)
| [ INT x; INT y ] -> INT (x * y)
| _ -> UNDEF

let div = function
| [ INT x; INT y ] -> if y = 0 then UNDEF else INT (x / y)
| _ -> UNDEF

let _not = function
| [ BOOL x ] -> BOOL (not x)
| _ -> UNDEF

let _and = function
| [ BOOL x; BOOL y ] -> BOOL (x && y)
| _ -> UNDEF

let _or = function
| [ BOOL x; BOOL y ] -> BOOL (x || y)
| _ -> UNDEF

let _implies = function
| [ BOOL x; BOOL y ] -> BOOL ((not x) || y)
| _ -> UNDEF

let _iff = function
| [ BOOL x; BOOL y ] -> BOOL (x = y)
| _ -> UNDEF

let const_static_fct (const_val : VALUE) (args : VALUE list) = const_val

//--------------------------------------------------------------------

let background_types = 
    let fail type_ arity args = failwith (sprintf "%s type expects %d type parameter(s), but %d were given" type_ arity (List.length args))
    [
        ("Boolean",  0, Some (function [] -> Integer | args -> fail "Boolean" 0 args));
        ("Integer",  0, Some (function [] -> Integer | args -> fail "Integer" 0 args));
        ("String",   0, Some (function [] -> String  | args -> fail "String"  0 args));
        ("Undef",    0, Some (function [] -> Undef   | args -> fail "Undef"   0 args));
        ("Rule",     0, Some (function [] -> Rule    | args -> fail "Rule"    0 args));
        ("Seq",      1, Some (function [ty] -> Seq ty      | args -> fail "Seq"      1 args));
        ("Powerset", 1, Some (function [ty] -> Powerset ty | args -> fail "Powerset" 1 args));
        ("Bag",      1, Some (function [ty] -> Bag ty      | args -> fail "Bag"      1 args));
        ("Map",      2, Some (function [ty1; ty2] -> Map (ty1, ty2) | args -> fail "Map" 2 args));
    ]

let background_functions = 
    [
        ("not",     _not,       ([Boolean], Boolean), NonInfix);
        ("iff",     _iff,       ([Boolean; Boolean], Boolean), Infix (RightAssoc, 0));
        ("implies", _implies,   ([Boolean; Boolean], Boolean), Infix (RightAssoc, 1));
        ("or",      _or,        ([Boolean; Boolean], Boolean), Infix (LeftAssoc, 2));
        ("and",     _and,       ([Boolean; Boolean], Boolean), Infix (LeftAssoc, 3));
        ("=",       eq,         ([TypeParam "a"; TypeParam "a"], Boolean), Infix (LeftAssoc, 4));
        ("!=",      neq,        ([TypeParam "a"; TypeParam "a"], Boolean), Infix (LeftAssoc, 4)); 
        (">",       gt,         ([Integer; Integer], Boolean), Infix (LeftAssoc, 5)); 
        (">=",      ge,         ([Integer; Integer], Boolean), Infix (LeftAssoc, 5)); 
        ("<",       lt,         ([Integer; Integer], Boolean), Infix (LeftAssoc, 5)); 
        ("<=",      le,         ([Integer; Integer], Boolean), Infix (LeftAssoc, 5)); 
        ("+",       plus,       ([Integer; Integer], Integer), Infix (LeftAssoc, 6));
        ("-",       minus,      ([Integer; Integer], Integer), Infix (LeftAssoc, 6));
        ("*",       times,      ([Integer; Integer], Integer), Infix (LeftAssoc, 7));
        ("div",     div,        ([Integer; Integer], Integer), Infix (LeftAssoc, 7));
    ]

let signature =
    let sign0 = Map.empty
    let add_fct sign (f, _, f_type, f_infix) = add_function_name f (Static, f_infix, f_type) sign
    let add_typ sign (t, arity, maps_to) = add_type_name t (arity, BasicType, maps_to) sign
    let sign1 = List.fold add_typ sign0 background_types
    let sign2 = List.fold add_fct sign1 background_functions   //(fun sign (f, _, f_type, f_infix) -> add_function_name f (Static, f_type, f_infix) sign)
    sign2

let state =
    Map.ofList
        (List.map (fun (f, f_interp, _, _) -> (f, f_interp)) background_functions)
