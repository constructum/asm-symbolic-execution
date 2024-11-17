module Signature

open Common

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

let fct_kind_to_string = function
| Static -> "static"
| Monitored -> "monitored"
| Controlled -> "controlled"
| Shared -> "shared"
| Out -> "out"
| Derived -> "derived"

type TYPE =         // !!! AsmetaL note: Complex, Real, Natural, Char not implemented
| Boolean
| Integer
| String
| Undef
| Rule
| TypeParam of string
| TypeCons of string * TYPE list
| Prod of TYPE list

let rec type_to_string ty =
    match ty with
    |   TypeParam a -> "'" ^ a
    |   Undef -> "Undef"
    |   Boolean -> "Boolean"
    |   Integer -> "Integer"
    |   String -> "String"
    |   Rule -> "Rule"
    |   TypeCons (s, tys)  -> if List.isEmpty tys then s else s ^ "(" ^ (tys |> type_list_to_string) ^ ")"
    |   Prod tys -> "Prod(" ^ (tys |> type_list_to_string) ^ ")"

and type_list_to_string tys =
    tys >>| type_to_string |> String.concat ", "

exception TypeMismatch of TYPE * TYPE

let match_type (ty : TYPE) (ty_sign : TYPE) (ty_env : Map<string, TYPE>) : Map<string, TYPE> =
    let error_msg () =
        sprintf ("type %s does not match %s") (ty |> type_to_string) (ty_sign |> type_to_string)
    match ty with
    |   TypeParam a ->
            failwith (sprintf "%s: type parameter not allowed in concrete type to be matched to signature type %s"
                (type_to_string ty) (type_to_string ty_sign))
    |   _ ->
            if ty = ty_sign then
                Map.empty
            else
                match ty_sign with
                |   TypeParam a ->
                        if Map.containsKey a ty_env then
                            if ty = Map.find a ty_env
                            then ty_env
                            else raise (TypeMismatch (ty, ty_sign))
                        else Map.add a ty ty_env
                |   _ -> raise (TypeMismatch (ty, ty_sign))

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
|   TypeInfo of TYPE_INFO
|   FctInfo of FCT_INFO
|   RuleInfo of RULE_INFO

// only function names for the moment, later rules and types

type SIGNATURE = Map<FCT_NAME, NAME_INFO>

let empty_signature : SIGNATURE = Map.empty

let signature_override (sign0 : SIGNATURE) sign' = Common.map_override sign0 sign'

let add_type_name type_name (arity, maps_to) (sign : SIGNATURE) =
    Map.add type_name (TypeInfo { arity = arity; maps_to = maps_to }) sign

let add_function_name fct_name (fct_kind, fct_type, infix_status) (sign : SIGNATURE) =
    Map.add fct_name (FctInfo { fct_kind = fct_kind; fct_type = fct_type; infix_status = infix_status }) sign

let add_rule_name rule_name rule_type (sign : SIGNATURE) =
    Map.add rule_name (RuleInfo { rule_type = rule_type }) sign

let is_name_defined name (sign : SIGNATURE) =
    Map.containsKey name sign

let is_type_name name (sign : SIGNATURE) =
    try match (Map.find name sign) with
        |   TypeInfo _ -> true
        |   FctInfo fi  -> false
        |   RuleInfo ri -> false
    with _ -> false

let get_type tyname tyargs (sign : SIGNATURE) : TYPE =
    if tyname = "Complex" || tyname = "Real" || tyname = "Natural" || tyname = "Char"
    then TypeCons (tyname, tyargs)  // !!! temporary for AsmetaL compatibility: non-implemented types seen as user-defined base types
    else
        try match (Map.find tyname sign) with
            |   TypeInfo { arity = n; maps_to = M } ->
                    if List.length tyargs <> n
                    then failwith (sprintf "type '%s' instantiated with %d arguments, but its arity is %d" tyname (List.length tyargs) n)            
                    else
                        match M with
                        |   Some f -> f tyargs
                        |   None -> TypeCons (tyname, tyargs)
            |   _ -> failwith (sprintf "unknown type '%s'" tyname)
        with _ -> failwith (sprintf "unknown type '%s'" tyname)

let is_function_name name (sign : SIGNATURE) =
    try match (Map.find name sign) with
        |   TypeInfo _ -> false
        |   FctInfo fi  -> true
        |   RuleInfo ri -> false
    with _ -> false

let is_rule_name name (sign : SIGNATURE) =
    try match (Map.find name sign) with
        |   TypeInfo _ -> false
        |   FctInfo fi  -> false
        |   RuleInfo ri -> true
    with _ -> false

let fct_names sign  = Set.ofSeq (Map.keys sign) |> Set.filter (fun name -> is_function_name name sign)
let rule_names sign = Set.ofSeq (Map.keys sign) |> Set.filter (fun name -> is_rule_name name sign)

// arity is for both function and rule names
let arity name (sign : SIGNATURE) =
    match (Map.find name sign) with
    |   TypeInfo _  -> failwith (sprintf "arity called for type parameter name '%s'" name)
    |   FctInfo fi  -> List.length (fst fi.fct_type)
    |   RuleInfo ri -> List.length ri.rule_type

let get_fct_info msg fct_name (sign : SIGNATURE) f = 
    assert is_function_name fct_name sign
    (Map.find fct_name sign)
    |> function FctInfo fi -> f fi | _ -> failwith (sprintf "Signature.%s: '%s' is not a function name" msg fct_name)

let fct_kind fct_name (sign : SIGNATURE) = 
    get_fct_info "fct_kind" fct_name sign (fun fi -> fi.fct_kind)

let fct_type fct_name (sign : SIGNATURE) = 
    get_fct_info "fct_type" fct_name sign (fun fi -> fi.fct_type)

let infix_status fct_name (sign : SIGNATURE) =
    get_fct_info "infix_status" fct_name sign (fun fi -> fi.infix_status)
    
let is_infix fct_name (sign : SIGNATURE) =
    get_fct_info "is_infix" fct_name sign (fun fi -> fi.infix_status <> NonInfix)

let is_left_assoc fct_name (sign : SIGNATURE) =
    get_fct_info "is_left_assoc" fct_name sign (fun fi -> fi.infix_status |> function Infix (LeftAssoc, _) -> true | _ -> false)

let is_right_assoc fct_name (sign : SIGNATURE) =
    get_fct_info "is_right_assoc" fct_name sign (fun fi -> fi.infix_status |> function Infix (RightAssoc, _) -> true | _ -> false)

let precedence fct_name (sign : SIGNATURE) =
    get_fct_info "is_right_assoc" fct_name sign (fun fi -> fi.infix_status |> function Infix (_, n) -> n | _ -> 0)

//--------------------------------------------------------------------

let match_fct_type (fct_name : string) (args_types : TYPE list) (sign_fct_type : TYPE list * TYPE) : TYPE =
    let (sign_args_types, sign_res_type) = sign_fct_type
    let error_msg () =
        sprintf "function '%s : %s -> %s' called with arguments of type(s) %s"
            fct_name (sign_args_types |> type_list_to_string) (sign_res_type |> type_to_string) (args_types |> type_list_to_string)
    let result_type sign_res_type ty_env =
        match sign_res_type with
        |   TypeParam a ->
                try Map.find a ty_env
                with _ -> failwith (sprintf "type of result of function %s : %s -> %s is unknown (type parameter '%s cannot be instantiated)"
                                        fct_name (sign_args_types |> type_list_to_string) (sign_res_type |> type_to_string) a)
        |   _ -> sign_res_type
    let rec match_types = function
        |   ([], [], ty_env : Map<string, TYPE>) ->
                (ty_env, result_type sign_res_type ty_env)
        |   (arg_type :: args_types', sign_arg_type :: sign_arg_types', ty_env) -> 
                let ty_env_1 =
                    try match_type arg_type sign_arg_type ty_env
                    with _ -> failwith (error_msg ())
                match_types (args_types', sign_arg_types', ty_env_1)
        |   (_, _, _) -> // arity does not match
                failwith (error_msg ())
    let (_, result_type) = match_types (args_types, sign_args_types, Map.empty)
    result_type

//--------------------------------------------------------------------
