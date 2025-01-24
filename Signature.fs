module Signature

open Common

let trace = ref 0

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

let fct_kind_to_string = function
| Constructor -> "constructor"
| Static -> "static"
| Monitored -> "monitored"
| Controlled -> "controlled"
| Shared -> "shared"
| Out -> "out"
| Derived -> "derived"

let infix_status_to_string = function
| NonInfix -> "non-infix"
| Infix (LeftAssoc, n) -> sprintf "infix left-associative with precedence %d" n
| Infix (RightAssoc, n) -> sprintf "infix right-associative with precedence %d" n

type TYPE =         // !!! AsmetaL note: Complex, Real, Natural, Char not implemented
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

let rec type_to_string ty =
    match ty with
    |   TypeParam a -> "'" ^ a
    |   Undef -> "Undef"
    |   Boolean -> "Boolean"
    |   Integer -> "Integer"
    |   String -> "String"
    |   Rule -> "Rule"
    |   TypeCons (s, tys)  -> if List.isEmpty tys then s else s ^ "(" ^ (tys |> type_list_to_string) ^ ")"
    |   Subset (tyname, main_type) -> (tyname) ^ " subsetof " ^ (type_to_string main_type)
    |   Prod tys -> "Prod(" ^ (tys |> type_list_to_string) ^ ")"
    |   Seq ty -> "Seq(" ^ (type_to_string ty) ^ ")"
    |   Powerset ty -> "Powerset(" ^ (type_to_string ty) ^ ")"
    |   Bag ty -> "Bag(" ^ (type_to_string ty) ^ ")"
    |   Map (ty1, ty2) -> "Map(" ^ (type_to_string ty1) ^ ", " ^ (type_to_string ty2) ^ ")"

and type_list_to_string tys =
    tys >>| type_to_string |> String.concat ", "

and fct_type_to_string (args_type, res_type) =
    sprintf "%s -> %s" (args_type |> type_list_to_string) (res_type |> type_to_string)

//--------------------------------------------------------------------

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

let error_msg (err : ErrorDetails) =
    match err with
    |   TypeMismatch (ty, ty_sign) ->
            sprintf "type mismatch: %s does not match %s" (ty |> type_to_string) (ty_sign |> type_to_string)
    |   FunctionCallTypeMismatch ((fct_name, sign_args_types, sign_res_type), args_types) ->
            sprintf "function '%s : %s -> %s' called with arguments of type(s) %s"
                fct_name (sign_args_types |> type_list_to_string) (sign_res_type |> type_to_string) (args_types |> type_list_to_string)
    |   TypeOfResultUnknown (fct_name, sign_args_types, sign_res_type) ->
            sprintf "type of result of function %s : %s -> %s is unknown (type parameter '%s cannot be instantiated)"
                fct_name (sign_args_types |> type_list_to_string) (sign_res_type |> type_to_string) (sign_res_type |> type_to_string)
    |   NoMatchingFunctionType (fct_name, args_types) ->
            sprintf "no matching function type found for '%s' with arguments of type(s) (%s)" fct_name (args_types |> type_list_to_string)
    |   AmbiguousFunctionCall (fct_name, args_types) ->
            sprintf "ambiguous function call: multiple matching function types found for '%s' with arguments of type(s) %s" fct_name (args_types |> type_list_to_string)
    |   NotAFunctionName name ->
            sprintf "there is no function name '%s' in the signature" name
    |   VariableAlreadyInUse v ->
            sprintf "variable '%s' already in use" v
    |   UnknownVariable v ->
            sprintf "unknown variable '%s'" v

//--------------------------------------------------------------------

module TypeEnv =
    type TYPE_ENV = Map<string, TYPE>
    let empty : TYPE_ENV = Map.empty
    let get v (env : TYPE_ENV) = try Map.find v env with _ -> raise (Error (UnknownVariable v))
    let add_distinct v ty (env : TYPE_ENV) =
        if Map.containsKey v env
        then raise (Error (VariableAlreadyInUse v))
        else Map.add v ty env
    let add_overwrite v ty (env : TYPE_ENV) =
        Map.add v ty env

type TYPE_ENV = TypeEnv.TYPE_ENV

//--------------------------------------------------------------------

let rec match_type (ty : TYPE) (ty_sign : TYPE) (ty_env : Map<string, TYPE>) : Map<string, TYPE> =
    if !trace > 0 then fprintf stderr "match_type(%s, %s)\n" (ty |> type_to_string) (ty_sign |> type_to_string)
    match (ty, ty_sign) with
    |   (_, Subset (_, ty_sign')) ->
            match_type ty ty_sign' ty_env
    |   (Subset (_, ty'), _) ->
            match_type ty' ty_sign ty_env
    |   (TypeParam a, _) ->
            failwith (sprintf "%s: type parameter not allowed in concrete type to be matched to signature type %s"
                (type_to_string ty) (type_to_string ty_sign))
    |   _ ->
            (*if ty = Undef || ty_sign = Undef then
                //!!!!!!!!!!!!! make everything compatible with undef for the moment - but this should be done properly
                Map.empty
            else*)
            if ty = ty_sign then
                Map.empty
            else
                match ty_sign with
                |   TypeParam a ->
                        if Map.containsKey a ty_env then
                            if (ty = Map.find a ty_env)
                            then ty_env
                            else raise (Error (TypeMismatch (ty, ty_sign)))
                        else Map.add a ty ty_env
                |   _ -> raise (Error (TypeMismatch (ty, ty_sign)))

type TYPE_KIND =
| BasicType
| AnyType           // type parameter (needed to implement AsmetaL's 'anydomain')
| EnumType          // inductive types - AsmetaL: enum / abstract domains
| SubsetType        // subset 'types'  - AsmetaL: concrete domains (i.e. subset of a basic or abstract domain)

let type_kind_to_string = function
| BasicType -> "BasicType"
| AnyType -> "AnyType"
| EnumType -> "EnumType"
| SubsetType -> "SubsetType"

type TYPE_INFO = {
    arity : int;
    type_kind : TYPE_KIND;
    maps_to : (TYPE list -> TYPE) option;  // None for user-declared types; Some ... for mapping type names to built-in types
}

type FCT_INFO = {
    fct_kind : FCT_KIND;
    infix_status : INFIX_STATUS;
    fct_types : (TYPE list * TYPE) list;      // it is a list due to function overloading in AsmetaL
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

//--------------------------------------------------------------------

let signature_to_string sign =
    let name_info_to_string (name : string) (name_info : NAME_INFO) =
        match name_info with
        | TypeInfo { arity = n; type_kind = kind; maps_to = maps_to } ->
            sprintf "type %s(%d)\n" name n
        | FctInfo { fct_kind = kind; infix_status = status; fct_types = fct_types } ->
            ( String.concat "\n" (
                List.map
                    (fun fct_type -> sprintf "%s function %s : %s" (fct_kind_to_string kind) name (fct_type_to_string fct_type))
                    fct_types) ) + "\n"   // + (infix_status_to_string status)
        | RuleInfo { rule_type = ty } ->
            sprintf "rule %s : %s\n" name (ty |> type_list_to_string)
    String.concat ""
        (Seq.map snd (Map.toSeq (Map.map (fun name name_info -> sprintf "%s" (name_info_to_string name name_info)) sign)))

//--------------------------------------------------------------------

let empty_signature : SIGNATURE = Map.empty

let signature_override (sign0 : SIGNATURE) sign' = Common.map_override sign0 sign'

let add_type_name type_name (arity, type_kind, maps_to) (sign : SIGNATURE) =
    if Map.containsKey type_name sign
    then failwith (sprintf "type name '%s' already declared" type_name)
    else Map.add type_name (TypeInfo { arity = arity; type_kind = type_kind; maps_to = maps_to }) sign

let add_function_name fct_name (fct_kind, infix_status, new_fct_type) (sign : SIGNATURE) =
    let existing_fct_types =
        try
            match Map.find fct_name sign with
            |   FctInfo { fct_kind = existing_fct_kind; infix_status = existing_infix_status; fct_types = fct_types } ->
                    if fct_kind <> existing_fct_kind
                    then failwith (sprintf "function '%s' already declared with kind %s, but now being declared with kind %s" fct_name (existing_fct_kind |> fct_kind_to_string) (fct_kind |> fct_kind_to_string))
                    if infix_status <> NonInfix && existing_infix_status <> NonInfix
                    then failwith (sprintf "function '%s' already declared as infix %s, but now being declared as %s" fct_name (existing_infix_status |> infix_status_to_string) (infix_status |> infix_status_to_string))
                    if List.exists (fun (args_type, res_type) -> args_type = fst new_fct_type && res_type = snd new_fct_type) fct_types
                    then fprintf stderr "warning: function name '%s : %s' already declared\n" fct_name (new_fct_type |> fct_type_to_string)
                    fct_types
            |   TypeInfo _ -> failwith (sprintf "function name '%s' already declared as a type name" fct_name)
            |   RuleInfo _ -> failwith (sprintf "function name '%s' already declared as a rule name" fct_name)
        with _ -> []
    let arity = new_fct_type |> fst |> List.length
    if infix_status <> NonInfix && arity <> 2
    then failwith (sprintf "infix notation only allowed for binary functions, but arity of '%s' is %d" fct_name arity)
    else Map.add fct_name (FctInfo { fct_kind = fct_kind; fct_types = existing_fct_types @ [new_fct_type]; infix_status = infix_status }) sign

let add_rule_name rule_name rule_type (sign : SIGNATURE) =
    if Map.containsKey rule_name sign
    then failwith (sprintf "rule name '%s' already declared" rule_name)
    else Map.add rule_name (RuleInfo { rule_type = rule_type }) sign

let is_name_defined name (sign : SIGNATURE) =
    Map.containsKey name sign

let is_type_name name (sign : SIGNATURE) =
    try match (Map.find name sign) with
        |   TypeInfo _ -> true
        |   FctInfo fi  -> false
        |   RuleInfo ri -> false
    with _ -> false

let construct_type (sign : SIGNATURE) (tyname, tyargs) : TYPE =
    if !trace > 1 then fprintf stderr "construct_type(%s, %s)\n" tyname (tyargs |> type_list_to_string)
    if  // !!! temporary for AsmetaL compatibility: non-implemented types seen as user-defined base types
        tyname = "Complex" || tyname = "Real" || tyname = "Natural" || tyname = "Char"    // AsmetaL predefined basic domains
    then if List.isEmpty tyargs then TypeCons (tyname, tyargs) else failwith (sprintf "type '%s' does not expect type arguments" tyname)
    else // !!! another special case for AsmetaL: Prod can have any number of type arguments
        if tyname = "Prod"
        then Prod tyargs
        else // normal case
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

let type_names sign  = Set.ofSeq (Map.keys sign) |> Set.filter (fun name -> is_type_name name sign)
let fct_names sign  = Set.ofSeq (Map.keys sign) |> Set.filter (fun name -> is_function_name name sign)
let rule_names sign = Set.ofSeq (Map.keys sign) |> Set.filter (fun name -> is_rule_name name sign)

let get_type_info msg tyname (sign : SIGNATURE) f = 
    assert is_type_name tyname sign
    (Map.find tyname sign)
    |> function TypeInfo ti -> f ti | _ -> failwith (sprintf "Signature.%s: '%s' is not a type name" msg tyname)

let type_arity (tyname : string) sign =
    get_type_info "type_arity" tyname sign (fun ti -> ti.arity)

let type_kind (tyname : string) sign =
    get_type_info "type_kind" tyname sign (fun ti -> ti.type_kind)

let get_fct_info msg fct_name (sign : SIGNATURE) f = 
    if !trace > 0 then fprintf stderr "(|signature| = %d) " (Map.count sign)
    if !trace > 0 then fprintf stderr "get_fct_info(%s, %s)\n" msg fct_name
    if !trace > 0 then fprintf stderr $"{Map.containsKey fct_name sign}\n"
    (try (Map.find fct_name sign) with _ -> raise (Error (NotAFunctionName fct_name)))
    |> function FctInfo fi -> f fi | _ -> raise (Error (NotAFunctionName fct_name))

let fct_kind fct_name (sign : SIGNATURE) = 
    get_fct_info "fct_kind" fct_name sign (fun fi -> fi.fct_kind)

let fct_types fct_name (sign : SIGNATURE) = 
    get_fct_info "fct_type" fct_name sign (fun fi -> fi.fct_types)

let fct_type fct_name (sign : SIGNATURE) = 
    match fct_types fct_name sign with
    |   [fct_type] -> fct_type
    |   _ -> failwith (sprintf "Signature.fct_type: overloaded function '%s'" fct_name)

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

let main_type = function
|   Subset (_, ty) -> ty
|   ty -> ty

//--------------------------------------------------------------------

let match_one_fct_type (fct_name : string) (args_types : TYPE list) (sign_fct_type : TYPE list * TYPE) : TYPE =
    let (sign_args_types, sign_res_type) = sign_fct_type
    let result_type sign_res_type ty_env =
        match sign_res_type with
        |   TypeParam a ->
                try Map.find a ty_env
                with _ -> raise (Error (TypeOfResultUnknown (fct_name, sign_args_types, sign_res_type)))
        |   _ -> sign_res_type
    let rec match_types = function
        |   ([], [], ty_env : Map<string, TYPE>) ->
                (ty_env, result_type sign_res_type ty_env)
        |   (arg_type :: args_types', sign_arg_type :: sign_arg_types', ty_env) -> 
                let ty_env_1 =
                    try match_type arg_type sign_arg_type ty_env
                    with _ -> raise (Error (FunctionCallTypeMismatch ((fct_name, sign_args_types, sign_res_type), args_types)))
                match_types (args_types', sign_arg_types', ty_env_1)
        |   (_, _, _) -> // arity does not match
                raise (Error (FunctionCallTypeMismatch ((fct_name, sign_args_types, sign_res_type), args_types)))
    let (_, result_type) = match_types (args_types, sign_args_types, Map.empty)
    result_type

let match_fct_type (fct_name : string) (args_types : TYPE list) (sign_fct_types : list<TYPE list * TYPE>) : TYPE =
    if !trace > 0 then fprintf stderr "\nfunction '%s': match_fct_type (%s) with:\n%s\n" fct_name (args_types |> type_list_to_string) (String.concat "," (sign_fct_types >>| fct_type_to_string))
    let rec matching_types results candidates =
        match candidates with
        |   [] -> results
        |   sign_fct_type :: candidates' ->
                if !trace > 1 then fprintf stderr "  sign_fct_type = %s\n" (sign_fct_type |> fct_type_to_string)
                try match match_one_fct_type fct_name args_types sign_fct_type with
                    |   ty -> matching_types (ty :: results) candidates'
                with ex -> matching_types results candidates'
    let results = List.rev (matching_types [] sign_fct_types)
    match results with
    |   [] -> raise (Error (NoMatchingFunctionType (fct_name, args_types)))
    |   [ty] -> ty
    |   _ -> raise (Error (AmbiguousFunctionCall (fct_name, args_types)))

//--------------------------------------------------------------------
