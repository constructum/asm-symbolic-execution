module Background

//--------------------------------------------------------------------

open Signature

//--------------------------------------------------------------------

type VALUE =
| UNDEF
| BOOL of bool
| INT of int
| STRING of string
//| TUPLE of VALUE list

let TRUE = BOOL true
let FALSE = BOOL false

let value_to_string = function
|   UNDEF -> "undef"
|   BOOL b -> if b then "true" else "false"
|   INT i -> i.ToString ()
|   STRING s -> "\"" + s + "\""

let type_of_value = function
|   UNDEF    -> Undef
|   BOOL b   -> Boolean
|   INT i    -> Integer
|   STRING s -> String

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
    [
        ("Boolean", 0, Some (function [] -> Boolean | _ -> failwith "Boolean type has no parameters"));
        ("Integer", 0, Some (function [] -> Integer | _ -> failwith "Integer type has no parameters"));
        ("String",  0, Some (function [] -> String  | _ -> failwith "String type has no parameters"));
        ("Undef",   0, Some (function [] -> Undef   | _ -> failwith "Undef type has no parameters"));
        ("Rule",    0, Some (function [] -> Rule    | _ -> failwith "Rule type has no parameters"));
            // note (!!!): this implies that 'undef' is not really practically usable, because it is of type 'Undef', which is not compatible with any other types
        // !!! Asmeta note: Complex, Real, Natural, Char not implemented
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
    let add_fct sign (f, _, f_type, f_infix) = add_function_name f (Static, f_type, f_infix) sign
    let add_typ sign (t, arity, maps_to) = add_type_name t (arity, maps_to) sign
    let sign1 = List.fold add_typ sign0 background_types
    let sign2 = List.fold add_fct sign1 background_functions   //(fun sign (f, _, f_type, f_infix) -> add_function_name f (Static, f_type, f_infix) sign)
    sign2

let state =
    Map.ofList
        (List.map (fun (f, f_interp, _, _) -> (f, f_interp)) background_functions)
