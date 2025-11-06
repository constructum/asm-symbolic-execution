module Engine

//--------------------------------------------------------------------

open System.Diagnostics
open System.Collections.Generic

open Common
open IndMap
open PrettyPrinting
open Background

//--------------------------------------------------------------------

let trace = ref 0
let level = ref 0
let module_name = "Engine"

let rec spaces level = if level = 0 then "" else "    " + spaces (level-1)
let rec indent level ppt = if level = 0 then ppt else blo4 [ indent (level-1) ppt ]

//--------------------------------------------------------------------

type FUNCTION_INTERPRETATION =
|   Constructor of (VALUE list -> VALUE)
|   StaticSymbolic of (TERM list -> TERM)       // rewriting rules for term simplification, e.g. for boolean functions 
|   StaticBackground of (VALUE list -> VALUE)
|   StaticUserDefined of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledInitial of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledUninitialized
|   Derived of (string list * TERM)             // string list is the list of arguments, TERM is the body of the derived function

and FUNCTION' =
    FctName of string

and FUNCTION_ATTRS = {
    fct_id    : int;
    fct_kind  : Signature.FCT_KIND;
    fct_types : (TYPE list * TYPE) list;   // !!! to be implemented together with monomorphization
    fct_interpretation : FUNCTION_INTERPRETATION
}

and FCT_ID =
|   FctId of int

and RULE_DEF' =
    RuleName of string

and RULE_DEF_ATTRS = {
    rule_def_id   : int;
    // rule_type : (TYPE list * TYPE);   // !!! to be implemented together with monomorphization
    rule_def  : (string list * RULE) option
}
and RULE_DEF_ID =
|   RuleDefId of int

and ENGINE' = {
    signature       : Signature.SIGNATURE
    initial_state   : State.STATE         // use only for initial state in this module, never use '_dynamic' field - also the second elem. of _dynamic_initial seems not to be used !
    invariants      : Map<string, TERM>   // Added invariants field

    functions       : IndMap<FUNCTION', FUNCTION_ATTRS>
    rule_defs       : IndMap<RULE_DEF', RULE_DEF_ATTRS>
    types           : IndMap<TYPE', TYPE_ATTRS>
    terms           : IndMap<TERM', TERM_ATTRS>
    rules           : IndMap<RULE', RULE_ATTRS>
    supds           : IndMap<S_UPDATE_SET', S_UPDATE_SET_ATTRS>

    TRUE_           : TERM option ref
    FALSE_          : TERM option ref
    AND_            : FCT_ID option ref
    OR_             : FCT_ID option ref
    NOT_            : FCT_ID option ref
    EQUALS_         : FCT_ID option ref

    smt_ctx         : SmtInterface.SMT_CONTEXT
}

and ENGINE = Engine of int

and ENGINES = ResizeArray<ENGINE'>

and TYPE = Type of int

and TYPE' =
| Boolean'
| Integer'
| String'
| Undef'
| Rule'
| TypeParam' of string
| TypeCons' of string * TYPE list
| Subset' of string * TYPE
| Prod' of TYPE list
| Seq' of TYPE
| Powerset' of TYPE
| Bag' of TYPE
| Map' of TYPE * TYPE

and TYPE_ATTRS = {
    type_id : int
    signature_type : Signature.TYPE
    carrier_set : VALUE Set option
}

and TERM' =
|   Value'      of (VALUE)                  // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   Initial'    of (FCT_ID * VALUE list)    // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   AppTerm'    of (FCT_ID * TERM list)
|   CondTerm'   of (TERM * TERM * TERM)
|   VarTerm'    of (string * TYPE)
|   QuantTerm'  of (AST.QUANT_KIND * string * TERM * TERM)
|   LetTerm'    of (string * TERM * TERM)
|   DomainTerm' of TYPE                  // AsmetaL construct: finite type (e.g. enum, abstract, subsetof) used as finite set
//  | TupleTerm   of 'annotation * ('annotation ANN_TERM list)

and TERM = Term of int

and TERM_ATTRS = {
    term_id       : int
    term_type     : TYPE
    smt_expr      : SmtInterface.SMT_EXPR option ref
    initial_state_eval_res : TERM option ref     // (symbolic) value of the term in the initial state, used also for static functions
}

and TERM_INDUCTION<'fct_id, 'term> = {
    Value      : (VALUE) -> 'term;
    Initial    : ('fct_id * VALUE list) -> 'term;
    AppTerm    : ('fct_id * 'term list) -> 'term;
    CondTerm   : ('term * 'term * 'term) -> 'term;
    VarTerm    : (string * TYPE) -> 'term;
    QuantTerm  : (AST.QUANT_KIND * string * 'term * 'term) -> 'term;
    LetTerm    : (string * 'term * 'term) -> 'term;
    DomainTerm : (TYPE) -> 'term;
}

and S_UPDATE_SET' = Set<(FCT_ID * VALUE list) * TERM>
and S_UPDATE_SET  = S_UpdateSet of int
and S_UPDATE_SET_ATTRS = { s_update_set_id : int }

and RULE' =
|   S_Updates' of S_UPDATE_SET     //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
|   UpdateRule' of (FCT_ID * TERM list) * TERM
|   CondRule' of TERM * RULE * RULE
|   ParRule' of RULE list
|   SeqRule' of RULE list
|   IterRule' of RULE
|   LetRule' of string * TERM * RULE
|   ForallRule' of string * TERM * TERM * RULE
|   MacroRuleCall' of RULE_DEF_ID * TERM list

and RULE = Rule of int

and RULE_ATTRS = unit

and RULE_INDUCTION<'term, 'rule> = {
    S_Updates : S_UPDATE_SET -> 'rule;
    UpdateRule : (FCT_ID * 'term list) * 'term -> 'rule;
    CondRule : 'term * 'rule * 'rule -> 'rule;
    ParRule : 'rule list -> 'rule;
    SeqRule : 'rule list -> 'rule;
    IterRule : 'rule -> 'rule;
    LetRule : string * 'term * 'rule -> 'rule;
    ForallRule : string * 'term * 'term * 'rule -> 'rule;
    MacroRuleCall : RULE_DEF_ID * 'term list -> 'rule;     // Map<FCT_NAME * VALUE list, 'term> -> 'rule;
}

and FCT_DEF_DB = Map<Signature.FCT_NAME, string list * TERM>    // for function definitions
and RULE_DEF_DB = Map<Signature.RULE_NAME, string list * RULE>     // for rule macros

and LOCATION = FCT_ID * VALUE list

and UPDATE = LOCATION * TERM
and UPDATE_SET = Set<UPDATE>
and UPDATE_MAP = Map<FCT_ID, Map<VALUE list, TERM>>

and ENV = Map<string, TERM * TYPE>

and PATH_COND = Set<TERM>

and ErrorDetails = ENGINE * string * ErrorDetails'

and ErrorDetails' =
// type errors
|   TypeMismatch of TYPE * TYPE
|   FunctionCallTypeMismatch of (string * TYPE list * TYPE) * TYPE list
|   TypeOfResultUnknown of string * TYPE list * TYPE
|   NoMatchingFunctionType of string * TYPE list
|   AmbiguousFunctionCall of string * TYPE list
|   NotAFunctionName of string
|   VariableAlreadyInUse of string
|   UnknownVariable of string
// runtime errors
|   InconsistentUpdates of ENGINE * TERM list option * UPDATE * UPDATE * UPDATE_SET option


let engines = new ENGINES()


exception Error of ErrorDetails

let rec error_msg ((eng, fct_name, details) : ErrorDetails) =
    let type_to_string, type_list_to_string = type_to_string eng, type_list_to_string eng
    (sprintf "error in function Engine.%s:\n" fct_name) +
    match details with
    // type errors
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
    // runtime errors
    |   InconsistentUpdates (eng, opt_conditions, u1, u2, opt_u_set) ->
            (   sprintf "\n--- inconsistent updates:\n%s\n%s\n" (show_s_update eng u1) (show_s_update eng u2) ) +
            (   match opt_conditions with    
                |   None -> ""
                |   Some ts ->
                        sprintf "\n--- initial state conditions leading to the inconsistent updates:\n%s\n"
                            (String.concat "\n" (ts >>| term_to_string eng)) ) +
            (   match opt_u_set with
                |   None -> ""
                |   Some U ->
                        sprintf "\n--- updates collected on this path so far:\n%s\n" (String.concat "\n" (List.map (show_s_update eng) (List.ofSeq U))) )

and type'_to_string eng (ty' : TYPE') =
    let type_to_string, type_list_to_string = type_to_string eng, type_list_to_string eng
    match ty' with
    |   TypeParam' a -> "'" ^ a
    |   Undef' -> "Undef"
    |   Boolean' -> "Boolean"
    |   Integer' -> "Integer"
    |   String' -> "String"
    |   Rule' -> "Rule"
    |   TypeCons' (s, tys)  -> if List.isEmpty tys then s else s ^ "(" ^ (tys |> type_list_to_string) ^ ")"
    |   Subset' (tyname, main_type) -> (tyname) ^ " subsetof " ^ (type_to_string main_type)
    |   Prod' tys -> "Prod(" ^ (tys |> type_list_to_string) ^ ")"
    |   Seq' ty -> "Seq(" ^ (type_to_string ty) ^ ")"
    |   Powerset' ty -> "Powerset(" ^ (type_to_string ty) ^ ")"
    |   Bag' ty -> "Bag(" ^ (type_to_string ty) ^ ")"
    |   Map' (ty1, ty2) -> "Map(" ^ (type_to_string ty1) ^ ", " ^ (type_to_string ty2) ^ ")"

and type_to_string eng ty =
    type'_to_string eng (get_type' eng ty)

and type_list_to_string (eng : ENGINE) tys =
    tys >>| type_to_string eng |> String.concat ", "

and fct_type_to_string (eng : ENGINE) (args_type, res_type) =
    sprintf "%s -> %s" (args_type |> type_list_to_string eng) (res_type |> type_to_string eng)

and inline get_fct_id (Engine eid) (name : string) : FCT_ID =
    match engines.[eid].functions |> try_get_index (FctName name) with
    | Some fct_id -> FctId fct_id
    | None -> failwith (sprintf "Engine.get_fct_id: function '%s' not found in global context #%d" name eid)

and inline get_function' (Engine eid) (FctId id) : FUNCTION' * FUNCTION_ATTRS =
    engines.[eid].functions |> get id

and inline fct_name eng fct_id = let (FctName name) = fst (get_function' eng fct_id) in name
and inline fct_kind eng fct_id = (snd (get_function' eng fct_id)).fct_kind
and inline fct_types eng fct_id = (snd (get_function' eng fct_id)).fct_types
and inline fct_interpretation eng fct_id = (snd (get_function' eng fct_id)).fct_interpretation

and inline make_type (eng as Engine eid : ENGINE) (ty' : TYPE') (opt_sign_type : Signature.TYPE option) : TYPE =
    let enum_finite_type (ty' : TYPE') (S : State.STATE) =
        match ty' with
        |   Boolean' -> Some State.boolean_carrier_set
        |   Integer' -> None
        |   String'  -> None
        |   Undef'   -> Some State.undef_carrier_set
        |   Rule' ->
                try Some (Option.get (Map.find "Rule" S._carrier_sets))
                with _ -> failwith "SymbState.enum_finite_type: carrier set of 'Rule' not found or not defined"  // not found: not in map; not defined: None
        |   TypeParam' _ -> None
        |   TypeCons' (tyname, []) ->
                try Some (Option.get (Map.find tyname S._carrier_sets))
                with _ -> failwith (sprintf "SymbState.enum_finite_type: carrier set of '%s' not found" tyname)
        |   Subset' (tyname, _) ->
                try Some (Option.get (Map.find tyname S._carrier_sets))
                with _ -> failwith (sprintf "SymbState.enum_finite_type: carrier set of '%s' not found" tyname)
        |   TypeCons' (tyname, _)  -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for user-defined type '%s' with type arity > 0" tyname)
        |   Prod' _  -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for 'Prod' types")
        |   Seq' _   -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for 'Seq' types")
        |   Powerset' _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for 'Powerset' types")
        |   Bag' _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for 'Bag' types")
        |   Map' _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for 'Map' types")
    let rec type'_to_sign_type (ty' : TYPE') : Signature.TYPE =
        let type_to_sign_type ty = type'_to_sign_type (get_type' eng ty)
        match ty' with
        |   Boolean' -> Signature.Boolean
        |   Integer' -> Signature.Integer
        |   String'  -> Signature.String
        |   Undef'   -> Signature.Undef
        |   Rule'    -> Signature.Rule
        |   TypeParam' name -> Signature.TypeParam name
        |   TypeCons' (tyname, ty_args) -> Signature.TypeCons (tyname, ty_args |> List.map type_to_sign_type)
        |   Subset' (tyname, main_ty) -> Signature.Subset (tyname, type_to_sign_type main_ty)
        |   Prod' ty_elems -> Signature.Prod (ty_elems |> List.map (type_to_sign_type))
        |   Seq' elem_ty -> Signature.Seq (type_to_sign_type elem_ty)
        |   Powerset' elem_ty -> Signature.Powerset (type_to_sign_type elem_ty)
        |   Bag' elem_ty -> Signature.Bag (type_to_sign_type elem_ty)
        |   Map' (dom_ty, rng_ty) -> Signature.Map (type_to_sign_type dom_ty, type_to_sign_type rng_ty)
    match IndMap.try_get_index ty' engines.[eid].types with
    |   Some type_id ->
            Type type_id
    |   None ->
            let e = engines.[eid]
            let type_id = e.types |> count
            let attrs = {
                type_id = type_id;
                signature_type = match opt_sign_type with Some sign_ty -> sign_ty | None -> type'_to_sign_type ty';
                carrier_set = try enum_finite_type ty' e.initial_state with _ -> None        //!!!! temporarily set to None for type where enum_finite_type is not yet implemented
            }
            e.types |> add (ty', attrs) |> Type

and inline get_type eng ty' = make_type eng ty' None        // precond.: type must exist, i.e. must have been created before with make_type called with (Some signature_type)
and get_type' (Engine eid) (Type type_id) = engines.[eid].types |> get_obj type_id

and convert_type (eng as Engine eid) (ty : Signature.TYPE) : TYPE =
    let make_type, convert_type = make_type eng, convert_type eng
    match ty with
    |   Signature.Boolean                    -> make_type Boolean' (Some ty)
    |   Signature.Integer                    -> make_type Integer' (Some ty)
    |   Signature.String                     -> make_type String' (Some ty)
    |   Signature.Undef                      -> make_type Undef' (Some ty)
    |   Signature.Rule                       -> make_type Rule' (Some ty)
    |   Signature.TypeParam name             -> make_type (TypeParam' name) (Some ty)
    |   Signature.Prod ty_elems              -> make_type (Prod' (ty_elems |> List.map convert_type)) (Some ty)
    |   Signature.Seq elem_ty                -> make_type (Seq' (convert_type elem_ty)) (Some ty)
    |   Signature.Powerset elem_ty           -> make_type (Powerset' (convert_type elem_ty)) (Some ty)
    |   Signature.Bag elem_ty                -> make_type (Bag' (convert_type elem_ty)) (Some ty)
    |   Signature.Map (dom_ty, rng_ty)       -> make_type (Map' (convert_type dom_ty, convert_type rng_ty)) (Some ty)
    |   Signature.TypeCons (tyname, ty_args) -> make_type (TypeCons' (tyname, ty_args |> List.map convert_type)) (Some ty)
    |   Signature.Subset (tyname, main_ty)   -> make_type (Subset' (tyname, convert_type main_ty)) (Some ty)

and inline to_signature_type (eng as Engine eid) (Type type_id : TYPE) : Signature.TYPE =
    (snd (engines.[eid].types |> get type_id)).signature_type

and inline enum_finite_type (eng as Engine eid) (Type type_id : TYPE) : VALUE Set option =
    (snd (engines.[eid].types |> get type_id)).carrier_set

and inline BooleanType (eng : ENGINE) = get_type eng Boolean'
and inline IntegerType (eng : ENGINE) = get_type eng Integer'
and inline StringType (eng : ENGINE) = get_type eng String'
and inline UndefType (eng : ENGINE) = get_type eng Undef'
and inline RuleType (eng : ENGINE) = get_type eng Rule'
and inline TypeParam (eng : ENGINE) (name : string) = get_type eng (TypeParam' name)
and inline ProdType (eng : ENGINE) (ty_elems : TYPE list) = get_type eng (Prod' ty_elems)
and inline SeqType (eng : ENGINE) (elem_ty : TYPE) = get_type eng (Seq' elem_ty)
and inline PowersetType (eng : ENGINE) (elem_ty : TYPE) = get_type eng (Powerset' elem_ty)
and inline BagType (eng : ENGINE) (elem_ty : TYPE) = get_type eng (Bag' elem_ty)
and inline MapType (eng : ENGINE) (dom_ty : TYPE, rng_ty : TYPE) = get_type eng (Map' (dom_ty, rng_ty))
and inline TypeCons (eng : ENGINE) (tyname : string, ty_args : TYPE list) = get_type eng (TypeCons' (tyname, ty_args))
and inline SubsetType (eng : ENGINE) (tyname : string, main_ty : TYPE) = get_type eng (Subset' (tyname, main_ty))

and match_type (eng : ENGINE) (ty : TYPE) (ty_sign : TYPE) (ty_env : Map<string, TYPE>) : Map<string, TYPE> =
    let type_to_string, get_type', match_type = type_to_string eng, get_type' eng, match_type eng
    if !trace > 0 then fprintf stderr "match_type(%s, %s)\n" (ty |> type_to_string) (ty_sign |> type_to_string)
    match (get_type' ty, get_type' ty_sign) with
    |   (_, Subset' (_, ty_sign')) -> match_type ty ty_sign' ty_env
    |   (Subset' (_, ty'), _)      -> match_type ty' ty_sign ty_env
    |   (TypeParam' a, _) ->
            failwith (sprintf "%s: type parameter not allowed in concrete type to be matched to signature type %s"
                (type_to_string ty) (type_to_string ty_sign))
    |   _ ->
            if ty = ty_sign then Map.empty else
                match get_type' ty_sign with
                |   TypeParam' a ->
                        if Map.containsKey a ty_env then
                            if ty = Map.find a ty_env then ty_env
                            else raise (Error (eng, "match_type", TypeMismatch (ty, ty_sign)))
                        else Map.add a ty ty_env
                |   _ -> raise (Error (eng, "match_type", TypeMismatch (ty, ty_sign)))

and match_one_fct_type eng (fct_name : string) (args_types : TYPE list) (sign_fct_type : TYPE list * TYPE) : TYPE =
    let (sign_args_types, sign_res_type) = sign_fct_type
    let result_type sign_res_type ty_env =
        match get_type' eng sign_res_type with
        |   TypeParam' a ->
                try Map.find a ty_env
                with _ -> raise (Error (eng, "match_one_fct_type", TypeOfResultUnknown (fct_name, sign_args_types, sign_res_type)))
        |   _ -> sign_res_type
    let rec match_types = function
        |   ([], [], ty_env : Map<string, TYPE>) ->
                (ty_env, result_type sign_res_type ty_env)
        |   (arg_type :: args_types', sign_arg_type :: sign_arg_types', ty_env) -> 
                let ty_env_1 =
                    try match_type eng arg_type sign_arg_type ty_env
                    with _ -> raise (Error (eng, "match_one_fct_type", FunctionCallTypeMismatch ((fct_name, sign_args_types, sign_res_type), args_types)))
                match_types (args_types', sign_arg_types', ty_env_1)
        |   (_, _, _) -> // arity does not match
                raise (Error (eng, "match_one_fct_type", FunctionCallTypeMismatch ((fct_name, sign_args_types, sign_res_type), args_types)))
    let (_, result_type) = match_types (args_types, sign_args_types, Map.empty)
    result_type

and match_fct_type (eng as Engine eid) (fct_name : string) (args_types : TYPE list) (sign_fct_types : list<TYPE list * TYPE>) : TYPE =
    if !trace > 0 then fprintf stderr "\nfunction '%s': match_fct_type (%s) with:\n%s\n" fct_name (args_types |> type_list_to_string eng) (String.concat "," (sign_fct_types >>| fct_type_to_string eng))
    let rec matching_types results candidates =
        match candidates with
        |   [] -> results
        |   sign_fct_type :: candidates' ->
                if !trace > 1 then fprintf stderr "  sign_fct_type = %s\n" (sign_fct_type |> fct_type_to_string eng)
                try match match_one_fct_type eng fct_name args_types sign_fct_type with
                    |   ty -> matching_types (ty :: results) candidates'
                with ex -> matching_types results candidates'
    let results = List.rev (matching_types [] sign_fct_types)
    match results with
    |   [] -> raise (Error (eng, "match_fct_type", NoMatchingFunctionType (fct_name, args_types)))
    |   [ty] -> ty
    |   _ -> raise (Error (eng, "match_fct_type", AmbiguousFunctionCall (fct_name, args_types)))

and type_of_value (eng as Engine eid) x = convert_type eng (Background.type_of_value engines.[eid].signature x)    //!!!! could be made more efficient for cells
and main_type_of eng ty = match get_type' eng ty with Subset' (_, main_type) -> main_type | _ -> ty


and compute_type (eng as Engine eid) (t' : TERM') : TYPE =
    let sign, fct_name, fct_types, type_of_value, get_term_type = engines.[eid].signature, fct_name eng, fct_types eng, type_of_value eng, get_term_type eng
    match t' with
    |   Value' x -> type_of_value x
    |   Initial' (f, xs) -> match_fct_type eng (fct_name f) (xs >>| type_of_value) (fct_types f)
    |   AppTerm' (f, ts) -> match_fct_type eng (fct_name f) (ts >>| get_term_type) (fct_types f)
    |   CondTerm' (G, t1, t2) -> if get_term_type t1 = get_term_type t2 then get_term_type t1 else failwith "compute_type: types of branches of conditional term do not match"
    |   VarTerm' (v, ty) -> ty
    |   QuantTerm' (_, _, t_set, _) -> BooleanType eng
    |   LetTerm' (_, t1, t2) -> get_term_type t2
    |   DomainTerm' tyname -> PowersetType eng tyname

and get_term_type (Engine eid) (t as Term tid : TERM) : TYPE =
    (engines.[eid].terms |> get_attrs tid).term_type

and inline get_smt_expr (Engine eid) (t as Term tid : TERM) : SmtInterface.SMT_EXPR option =
    !(engines.[eid].terms |> get_attrs tid).smt_expr

and inline set_smt_expr (Engine eid) (t as Term tid : TERM) (smt_expr : SmtInterface.SMT_EXPR) =
    (engines.[eid].terms |> get_attrs tid).smt_expr := Some smt_expr

and inline initial_state_eval_res (Engine eid) (t as Term tid : TERM) : TERM option ref =
    (engines.[eid].terms |> get_attrs tid).initial_state_eval_res

and inline get_term (eng as Engine eid : ENGINE) (t' : TERM') : TERM =
    match IndMap.try_get_index t' engines.[eid].terms with
    |   Some tid ->
            Term tid
    |   None ->
            let e = engines.[eid]
            let tid = e.terms |> count
            let attrs = {
                term_id    = tid;
                term_type  = compute_type eng t';
                smt_expr   = ref None;
                initial_state_eval_res = ref None
            }
            e.terms |> add (t', attrs) |> Term

and inline get_term'_attrs (Engine eid) (Term tid) = engines.[eid].terms |> get tid
and inline get_term' (Engine eid) (Term tid) = engines.[eid].terms |> get_obj tid
and inline get_term_attrs (Engine eid) (Term tid) = engines.[eid].terms |> get_attrs tid

and inline Value eng x = get_term eng (Value' x)
and inline Initial eng (f, xs) = get_term eng (Initial' (f, xs))
and inline AppTerm eng (f, ts) = get_term eng (AppTerm' (f, ts))
and inline CondTerm eng (G, t1, t2) = get_term eng (CondTerm' (G, t1, t2))
and inline VarTerm eng v = get_term eng (VarTerm' v)
and inline QuantTerm eng (q_kind, v, t_set, t_cond) = get_term eng (QuantTerm' (q_kind, v, t_set, t_cond))
and inline LetTerm eng (x, t1, t2) = get_term eng (LetTerm' (x, t1, t2))
and inline DomainTerm eng tyname = get_term eng (DomainTerm' tyname)
and inline TRUE (Engine eid) = !engines.[eid].TRUE_ |> Option.get
and inline FALSE (Engine eid) = !engines.[eid].FALSE_ |> Option.get
and inline AND (Engine eid) = !engines.[eid].AND_ |> Option.get
and inline OR (Engine eid) = !engines.[eid].OR_ |> Option.get
and inline NOT (Engine eid) = !engines.[eid].NOT_ |> Option.get
and inline EQUALS (Engine eid) = !engines.[eid].EQUALS_ |> Option.get

and convert_term (eng : ENGINE) (t : AST.TYPED_TERM) : TERM =
    AST.ann_term_induction (fun x -> x) {
        Value      = fun (_, x) -> Value eng x;
        Initial    = fun (_, (f, xs)) -> Initial eng (get_fct_id eng f, xs);
        AppTerm    = fun (ty, (f, ts)) ->
                        match f with
                        |   Signature.UndefConst    -> Value eng UNDEF
                        |   Signature.BoolConst b   -> Value eng (BOOL b)
                        |   Signature.IntConst i    -> Value eng (INT i)
                        |   Signature.StringConst s -> Value eng (STRING s)
                        |   Signature.FctName f ->
                                let f_id = get_fct_id eng f
                                try
                                    AppTerm eng (f_id, ts)
                                with ex as Signature.Error (Signature.NoMatchingFunctionType (f, tys)) ->
                                    fprintf stderr "convert_term: in term %A\n" (AppTerm eng (f_id, ts))
                                    raise ex
        CondTerm   = fun (_, (G, t1, t2)) -> CondTerm eng (G, t1, t2);
        VarTerm    = fun (ty, v) -> VarTerm eng (v, convert_type eng ty)
        QuantTerm  = fun (ty, (q_kind, v, t_set, t_cond)) -> QuantTerm eng (q_kind, v, t_set, t_cond);
        LetTerm    = fun (_, (v, t1, t2)) -> LetTerm eng (v, t1, t2);
        DomainTerm = fun (_, D) -> DomainTerm eng (convert_type eng D);
    } t

and inline get_s_update_set (eng as Engine eid : ENGINE) (us' : S_UPDATE_SET') : S_UPDATE_SET =
    match IndMap.try_get_index us' engines.[eid].supds with
    |   Some uid ->
            S_UpdateSet uid
    |   None ->
            let e = engines.[eid]
            let uid = e.supds |> count
            let attrs : S_UPDATE_SET_ATTRS = {
                s_update_set_id = uid
            }
            e.supds |> add (us', attrs) |> S_UpdateSet

and inline get_s_update_set' (Engine eid) (S_UpdateSet uid : S_UPDATE_SET) : S_UPDATE_SET' =
    engines.[eid].supds |> get uid |> fst

and inline s_update_set_empty (eng as Engine eid) : S_UPDATE_SET =
    get_s_update_set eng Set.empty

and inline s_update_set_is_empty (eng as Engine eid) (S_UpdateSet uid : S_UPDATE_SET) : bool =
    engines.[eid].supds |> get uid |> fst |> Set.isEmpty

and inline s_update_set_union (eng as Engine eid) (S_UpdateSet uid1 : S_UPDATE_SET) (S_UpdateSet uid2 : S_UPDATE_SET) : S_UPDATE_SET =
    let supds = engines.[eid].supds
    let us1, _ = supds |> get uid1
    let us2, _ = supds |> get uid2
    get_s_update_set eng (Set.union us1 us2)

and inline s_update_set_seq_merge_2 (eng as Engine eid) (S_UpdateSet uid1 : S_UPDATE_SET) (S_UpdateSet uid2 : S_UPDATE_SET) : S_UPDATE_SET =
    let supds = engines.[eid].supds
    let us1, _ = supds |> get uid1
    let us2, _ = supds |> get uid2
    get_s_update_set eng (seq_merge_2 eng us1 us2)

and inline s_update_set_to_list (Engine eid) (S_UpdateSet uid : S_UPDATE_SET) : list<(FCT_ID * VALUE list) * TERM> =
    let us', _ = engines.[eid].supds |> get uid
    List.ofSeq us'

and inline get_rule_def_id (Engine eid) (name : string) : RULE_DEF_ID =
    match engines.[eid].rule_defs |> try_get_index (RuleName name) with
    | Some rule_def_id -> RuleDefId rule_def_id
    | None -> failwith (sprintf "Engine.get_named_rule_id: function '%s' not found in global context #%d" name eid)

and inline get_rule_def' (Engine eid) (RuleDefId id : RULE_DEF_ID) : RULE_DEF' * RULE_DEF_ATTRS =
    engines.[eid].rule_defs |> get id

and inline get_rule_name (Engine eid) (RuleDefId id : RULE_DEF_ID) = let RuleName r_name, _ =engines.[eid].rule_defs |> get id in r_name
and inline get_rule_def (eng as Engine eid) (id : RULE_DEF_ID) = (snd (get_rule_def' eng id)).rule_def

and inline get_rule' (Engine eid) (Rule rid) = engines.[eid].rules |> get rid |> fst

and inline get_rule (eng as Engine eid : ENGINE) (R' : RULE') : RULE =
    match IndMap.try_get_index R' engines.[eid].rules with
    |   Some rid ->
            Rule rid
    |   None ->
            let e = engines.[eid]
            let rid = e.rules |> count
            e.rules |> add (R', ()) |> Rule

and inline UpdateRule eng ((f, ts), t_rhs) = get_rule eng (UpdateRule' ((f, ts), t_rhs))
and inline CondRule eng (G, R1, R2) = get_rule eng (CondRule' (G, R1, R2))
and inline ParRule eng Rs = get_rule eng (ParRule' Rs)
and inline SeqRule eng Rs = get_rule eng (SeqRule' Rs)
and inline IterRule eng R' = get_rule eng (IterRule' R')
and inline LetRule eng (v, t1, R') = get_rule eng (LetRule' (v, t1, R'))
and inline MacroRuleCall eng (r, args) = get_rule eng (MacroRuleCall' (r, args))
and inline ForallRule eng (v, t_set, G, R') = get_rule eng (ForallRule' (v, t_set, G, R'))
and inline S_Updates eng upds = get_rule eng (S_Updates' upds)   // Map.map (fun ((f, xs), t_rhs) -> ((get_fct_id eng f, xs), convert_term eng t_rhs)) upds

and convert_rule (eng : ENGINE) (R : AST.RULE) : RULE =
    AST.rule_induction (convert_term eng) {
        UpdateRule = fun ((f, ts), t_rhs) -> UpdateRule eng ((get_fct_id eng f, ts), t_rhs);
        CondRule   = fun (G, R1, R2) -> CondRule eng (G, R1, R2);
        ParRule    = fun Rs -> ParRule eng Rs;
        SeqRule    = fun Rs -> SeqRule eng Rs;
        IterRule   = fun R' -> IterRule eng R';
        LetRule    = fun (v, t1, R') -> LetRule eng (v, t1, R');
        MacroRuleCall = fun (r_name, args) -> MacroRuleCall eng (get_rule_def_id eng r_name, args);
        ForallRule = fun (v, t_set, G, R') -> ForallRule eng (v, t_set, G, R');
        S_Updates  = fun upds -> S_Updates eng (get_s_update_set eng (Set.map (fun ((f, xs), t_rhs) -> (get_fct_id eng f, xs), convert_term eng t_rhs) upds))
    } R

and new_engine (sign : Signature.SIGNATURE, initial_state : State.STATE, fct_def_db : AST.MACRO_DB, rule_def_db : AST.RULES_DB, invariants : Map<string, AST.TYPED_TERM>, smt_ctx : SmtInterface.SMT_CONTEXT) : ENGINE =
    let eid = engines.Count
    let new_engine = {
        signature       = sign
        initial_state   = initial_state
        invariants      = Map.empty
        functions       = newIndMap<FUNCTION', FUNCTION_ATTRS>()
        rule_defs       = newIndMap<RULE_DEF', RULE_DEF_ATTRS>()
        types           = newIndMap<TYPE', TYPE_ATTRS>()
        terms           = newIndMap<TERM', TERM_ATTRS>()
        rules           = newIndMap<RULE', RULE_ATTRS>()
        supds           = newIndMap<S_UPDATE_SET', S_UPDATE_SET_ATTRS>()
        TRUE_           = ref None
        FALSE_          = ref None
        AND_            = ref None
        OR_             = ref None
        NOT_            = ref None
        EQUALS_         = ref None
        smt_ctx         = smt_ctx
    }
    engines.Add new_engine
    let extract_fct_interpretation_if_possible f_name =
        let f_kind = Signature.fct_kind f_name sign
        match Signature.fct_kind f_name sign with
        |   Signature.Constructor ->
                Some (Constructor (fun xs -> CELL (f_name, xs)))
        |   Signature.Static ->
                match initial_state._static |> Map.tryFind f_name with
                |   None -> fprintf stderr "Warning: static function '%s' is in signature, but is not defined - ignored\n" f_name; None
                |   Some fct_interp ->
                        if Set.contains f_name (Signature.fct_names Background.signature)   // background functions
                        then Some (StaticBackground fct_interp)
                        else Some (StaticUserDefined (fct_interp, None))   // second component is the AsmetaL definition to be filled in later
        |   Signature.Controlled ->
                match initial_state._dynamic_initial |> fst |> Map.tryFind f_name with
                |   Some fct_def -> Some (ControlledInitial (fct_def, None))
                |   None -> Some ControlledUninitialized
        |   Signature.Derived ->
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) -> Some (Derived (args, convert_term (Engine eid) body))   // !!! convert_term here is problematic, because functions are not yet in fctTable, see how it is done for the other kinds of functions
                |   None -> failwith (sprintf "Engine.new_engine: derived function '%s' is in signature, but is not defined\n" f_name)
        |   Signature.Monitored -> failwith (sprintf "Engine.new_engine: monitored function '%s' - not implemented" f_name)
        |   Signature.Shared -> failwith (sprintf "Engine.new_engine: shared function '%s' - not implemented" f_name)
        |   Signature.Out -> failwith (sprintf "Engine.new_engine: out function '%s' - not implemented" f_name)
    let extract_rule_def_rhs r_name =
        match rule_def_db |> Map.tryFind r_name with
        |   Some (args, R) -> (args, R)
        |   None -> failwith (sprintf "Engine.new_engine: no definition found for rule macro '%s'\n" r_name)
    let add_functions fct_list =
        fct_list
            |> List.map (fun (name, _) -> (name, extract_fct_interpretation_if_possible name))
            |> List.filter (function (_, None) -> false | _ -> true)
            |> Seq.iteri ( fun i (name, opt_fct_interpretation) ->
                match opt_fct_interpretation with
                |   None -> ()
                |   Some fct_interpretation ->
                        new_engine.functions |> add (
                            FctName name, {
                                fct_id   = i;
                                fct_kind = Signature.fct_kind name sign;
                                fct_types = List.map (fun (args_ty, res_ty) -> (args_ty >>| convert_type (Engine eid), convert_type (Engine eid) res_ty)) (Signature.fct_types name sign);
                                fct_interpretation = fct_interpretation
                            }) |> ignore )
    let functions = sign |> Map.toList |> List.filter (fun (name, _) -> Signature.is_function_name name sign)
    // add to engine non-derived functions first, then derived functions
    functions |> List.filter (fun (name, _) -> not (Signature.fct_kind name sign = Signature.Derived)) |> add_functions
    functions |> List.filter (fun (name, _) -> Signature.fct_kind name sign = Signature.Derived) |> add_functions
    // add rules
    rule_def_db |> Map.toList
        |> List.map (fun (name, _) -> (name, extract_rule_def_rhs name))
        |> Seq.iteri (fun i (name, rule_def) ->
            new_engine.rule_defs |> add (
                RuleName name, {
                    rule_def_id   = i;
                    // rule_type = Signature.rule_types name sign;   // !!! to be implemented together with monomorphization
                    rule_def  = None
                }) |> ignore )
    for i in 0..(new_engine.functions |> count) - 1 do
        let FctName f_name, (f_attrs as { fct_interpretation = fct_intp }) = new_engine.functions |> get i
        match fct_intp with
        |   StaticUserDefined (fct_interp, None) ->
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) ->
                        new_engine.functions |> set i (FctName f_name, { f_attrs with fct_interpretation = StaticUserDefined (fct_interp, Some (args, convert_term (Engine eid) body)) })
                |   None -> failwith (sprintf "cannot find definition of static function '%s'\n" f_name)
        |   ControlledInitial (fct_interp, None) ->
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) ->
                        new_engine.functions |> set i (FctName f_name, { f_attrs with fct_interpretation = ControlledInitial (fct_interp, Some (args, convert_term (Engine eid) body)) })
                |   None -> failwith (sprintf "cannot find initial definition of controlled function '%s'\n" f_name)
        |   _ -> ()     // if not any of the above cases, do nothing (the entry of fctTable was already completely initialized)
    for i in 0..(new_engine.rule_defs |> count) - 1 do
        let RuleName rd_name, (rd_attrs as { rule_def_id = id; rule_def = _ }) = new_engine.rule_defs |> get i
        let (args, body) = extract_rule_def_rhs rd_name
        new_engine.rule_defs |> set i (RuleName rd_name, { rd_attrs with rule_def = Some (args, convert_rule (Engine eid) body) })
    let new_ctx = {
        new_engine with
            invariants = Map.map (fun _ t -> convert_term (Engine eid) t) invariants
        }
    engines.[eid] <- new_ctx
    engines.[eid].TRUE_   := Some (Value (Engine eid) (BOOL true))
    engines.[eid].FALSE_  := Some (Value (Engine eid) (BOOL false))
    engines.[eid].AND_    := Some (get_fct_id (Engine eid) "and")
    engines.[eid].OR_     := Some (get_fct_id (Engine eid) "or")
    engines.[eid].NOT_    := Some (get_fct_id (Engine eid) "not")
    engines.[eid].EQUALS_ := Some (get_fct_id (Engine eid) "=")
    Engine eid

and get_engine' (Engine eid : ENGINE) : ENGINE' =
    if eid < engines.Count then
        engines.[eid]
    else
        failwith (sprintf "get_engine': engine %d not found" eid)

and initial_state_of (Engine eid) =
    engines.[eid].initial_state

and invariants_of (Engine eid) =
    engines.[eid].invariants

and smt_solver_push (Engine eid) =
    SmtInterface.smt_solver_push engines.[eid].smt_ctx

and smt_solver_pop (Engine eid) =
    SmtInterface.smt_solver_pop engines.[eid].smt_ctx

//--------------------------------------------------------------------

and term_induction (eng: ENGINE) (fct_id : FCT_ID -> 'fct_id) (F : TERM_INDUCTION<'fct_id, 'term>) (t : TERM) :'term =
    let term_ind = term_induction eng fct_id F
    match get_term' eng t with
    |   Value' x              -> F.Value x
    |   Initial' (f, xs)      -> F.Initial (fct_id f, xs)
    |   AppTerm' (f, ts)      -> F.AppTerm (fct_id f, List.map (fun t -> term_ind t) ts)
    |   CondTerm' (G, t1, t2) -> F.CondTerm (term_ind G, term_ind t1, term_ind t2)
    |   VarTerm' (v, ty)      -> F.VarTerm (v, ty)
    |   QuantTerm' (q_kind, v, t_set, t_cond) -> F.QuantTerm (q_kind, v, term_ind t_set, term_ind t_cond)
    |   LetTerm' (x, t1, t2)  -> F.LetTerm (x, term_ind t1, term_ind t2)
    |   DomainTerm' tyname    -> F.DomainTerm tyname

//--------------------------------------------------------------------

and skipRule eng = ParRule eng []

//--------------------------------------------------------------------

and rule_induction (eng: ENGINE) (term : TERM -> 'term) (F : RULE_INDUCTION<'term, 'rule>) (R : RULE) : 'rule =
    let rule_ind = rule_induction eng term
    match get_rule' eng R with
    |   S_Updates' U -> F.S_Updates U   // F.S_Updates (Map.map (fun loc -> fun t_rhs -> term t_rhs) U)
    |   UpdateRule' ((f, ts), t) -> F.UpdateRule ((f, List.map term ts), term t)
    |   CondRule' (G, R1, R2: RULE) -> F.CondRule (term G, rule_ind F R1, rule_ind F R2)
    |   ParRule' Rs -> F.ParRule (List.map (rule_ind F) Rs)
    |   SeqRule' Rs -> F.SeqRule (List.map (rule_ind F) Rs)
    |   IterRule' R -> F.IterRule (rule_ind F R)
    |   LetRule' (v, t, R) -> F.LetRule (v, term t, (rule_ind F) R)
    |   ForallRule' (v, t_set, t_filter, R) -> F.ForallRule (v, term t_set, term t_filter, (rule_ind F) R)
    |   MacroRuleCall' (r, ts) -> F.MacroRuleCall (r, List.map term ts)

//--------------------------------------------------------------------
//
//  pretty printing
//
//--------------------------------------------------------------------

and pp_list sep = function
|   []         -> []
|   [x]        -> [ x ]
|   (x :: xs') -> x :: (sep @ (pp_list sep xs'))

and pp_name (name : Signature.NAME) =
    (   match name with
    |   Signature.UndefConst -> "undef"
    |   Signature.BoolConst b -> if b then "true" else "false"
    |   Signature.IntConst i -> i.ToString()
    |   Signature.StringConst s -> "\"" + s + "\""
    |   Signature.FctName f -> f ) |> str

and pp_app_term sign = function
    |   (Signature.FctName f, [t1; t2]) when Signature.infix_status f sign <> Signature.NonInfix ->
            blo0 [ str "("; blo0 [ t1; brk 1; str (sprintf "%s " f); t2 ]; str ")" ]
    |   (Signature.FctName f, ts) when ts <> [] ->
            blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] ts); str ")" ]
    |   (name, _) -> pp_name name

and pp_location_term sign prefix = function
    |   (f : string, xs : VALUE list) when xs <> [] ->
            blo0 [ str (prefix+"["); str f; str "("; blo0 (pp_list [str",";brk 1] (List.map (fun x -> str (value_to_string x)) xs)); str ")]" ]
    |   (f, _) -> blo0 [ str $"{prefix}[{f}]" ]

and pp_term (eng : ENGINE) (t : TERM) =
    let sign = (get_engine' eng).signature
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    term_induction eng (fun x -> x) {
        AppTerm  = fun (f, ts) -> pp_app_term (Signature.FctName (fct_name eng f), ts);
        CondTerm = fun (G, t1, t2) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun x -> str (value_to_string x);
        Initial  = fun (f, xs) -> pp_location_term "initial" (fct_name eng f, xs);
        VarTerm = fun (x, _) -> str x;
        QuantTerm = fun (q_kind, v, t_set, t_cond) ->
            blo0 [ str ("("^(AST.quant_kind_to_str q_kind)^" "); str v; str " in "; t_set; str " with "; t_cond; str ")" ];
        LetTerm = fun (v, t1, t2) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
        DomainTerm = fun tyname -> str (type_to_string eng tyname);
    } t

and pp_rule (eng : ENGINE)  (R : RULE) =
    let sign = (get_engine' eng).signature
    let (pp_app_term, pp_term) = (pp_app_term sign, pp_term eng)
    rule_induction eng pp_term {
        S_Updates = fun U ->
                        let pp_elem ((f, xs), t) = blo0 [ str (fct_name eng f); str " "; str "("; blo0 (pp_list [str",";brk 1] (xs >>| fun x -> str (value_to_string x))); str ") := "; (pp_term t) ]
                        let L = s_update_set_to_list eng U >>| pp_elem
                        blo0 [ str "{"; line_brk; blo2 ( pp_list [line_brk] L); line_brk; str "}" ];
        UpdateRule = fun ((f, ts), t) -> blo0 [ pp_app_term (Signature.FctName (fct_name eng f), ts); str " := "; t ];
        CondRule = fun (G, R1, R2) -> blo0 ( str "if " :: G:: str " then " :: line_brk :: blo2 [ R1 ] :: line_brk ::
                                             (if R2 <> str "skip" then [ str "else "; line_brk; blo2 [ R2 ]; line_brk; str "endif" ] else [ str "endif"]) );
        ParRule = fun Rs -> if Rs <> [] then blo0 [ str "par"; line_brk; blo2 ( pp_list [line_brk] Rs); line_brk; str "endpar" ] else str "skip";
        SeqRule = fun Rs -> blo0 [ str "seq"; line_brk; blo2 (pp_list [line_brk] Rs); line_brk; str "endseq" ];
        IterRule = fun R' -> blo0 [ str "iterate "; line_brk; blo2 [ R' ]; line_brk; str "enditerate" ];
        LetRule = fun (v, t, R) -> blo0 [ str "let "; str v; str " = "; t; line_brk; str "in "; R; line_brk; str "endlet" ];
        ForallRule = fun (v, t_set, t_filter, R) -> blo0 [ str "forall "; str v; str " in "; t_set; str " with "; t_filter; str " do"; line_brk; blo2 [ R ]; line_brk; str "endforall" ];
        MacroRuleCall = fun (r, ts) -> blo0 [ str (get_rule_name eng r); str "["; blo0 (pp_list [str",";brk 1] ts); str "]" ];
    } R


and name_to_string t      = t |> pp_name |> PrettyPrinting.toString 80
and term_to_string sign t = t |> pp_term sign |> PrettyPrinting.toString 80
and rule_to_string sign t = t |> pp_rule sign |> PrettyPrinting.toString 80

//--------------------------------------------------------------------
//
//  function tables
//
//--------------------------------------------------------------------

and show_fct_tables (eng as Engine eid: ENGINE) =
    let e = get_engine' eng
    let index_s = e.functions |> show_index (fun (FctName f_name) -> f_name)
    let show_table_entry (i, FctName f_name, { fct_kind = f_kind; fct_id = f_id; fct_interpretation = f_intp }) =
        if i <> f_id then
            failwith (sprintf "show_fct_tables: function id %d does not match index %d" f_id i)
        else
            sprintf "%d: %s (%s) = [%s]"
                f_id f_name (Signature.fct_kind_to_string f_kind)
                (match f_intp with
                    | Constructor _ -> "constructor"
                    | StaticSymbolic _ -> "static (symbolic)"
                    | StaticBackground _ -> "static (background)"
                    | StaticUserDefined _ -> "static (user-defined)"
                    | ControlledInitial _ -> "controlled (initial)"
                    | ControlledUninitialized -> "controlled (uninitialized)"
                    | Derived (args, body) -> sprintf "derived (%s) = %s" (String.concat ", " args) (term_to_string eng body) )
    let table_s = e.functions |> show_table show_table_entry
    index_s + table_s

//--------------------------------------------------------------------
//
//  locations, symbolic updates, symbolic update sets
//
//--------------------------------------------------------------------

and location_to_string eng ((f, xs) : LOCATION) : string = Updates.location_to_string (fct_name eng f, xs)

and show_s_update eng ((f, xs), t) =
    let f = fct_name eng f
    sprintf "%s := %s"
        (if List.isEmpty xs then f else sprintf "%s (%s)" f (String.concat ", " (List.map value_to_string xs)))
        (PrettyPrinting.toString 80 (pp_term eng t))

and show_s_update_set eng (U :UPDATE_SET) =
    "{ " +
    ( Set.toList U >>| show_s_update eng
        |> String.concat ", "   ) +
    " }"

and show_s_update_map eng (U :UPDATE_MAP) =
    let s_update_set = Set.ofSeq (Map.toSeq U |> Seq.collect (fun (f : FCT_ID, table) -> table |> Map.toSeq |> Seq.map (fun (args, value) -> (f, args), value)))
    show_s_update_set eng s_update_set

//--------------------------------------------------------------------

and add_s_update eng (U : UPDATE_MAP) (u as (loc as (f, args), value): UPDATE) =
    if !trace > 0 then fprintf stderr "add_s_update: %s\n" (show_s_update eng u)
    Map.change f
        ( function None -> Some (Map.add args value Map.empty)
                 | Some table ->
                        Some (  if Map.containsKey args table
                                then if value <> Map.find args table  // deal with conflicting updates
                                     then raise (Error (eng, "add_s_update", InconsistentUpdates (eng, None, (loc, Map.find args table), (loc, value), None)))
                                     else table
                                else Map.add args value table ) )
        U

and s_update_set_to_s_update_map eng (U : UPDATE_SET) =
    Set.fold (add_s_update eng) Map.empty U

and consistent eng (U : UPDATE_SET) =
    try let x = s_update_set_to_s_update_map eng U
        in true
    with Failure _ -> false
    
and locations (U : UPDATE_SET) : Set<LOCATION> =
    Set.map (fun (loc, value) -> loc) U

and seq_merge_2 eng (U : UPDATE_SET) (V : UPDATE_SET) =
    if not (consistent eng U)
    then U
    else let U_reduced = Set.filter (fun (loc, _) -> not (Set.contains loc (locations V))) U
         in Set.union U_reduced V

and seq_merge_n eng (Us : UPDATE_SET list) : UPDATE_SET =
    List.fold (seq_merge_2 eng) Set.empty Us

and apply_s_update_map (UM0 : UPDATE_MAP) (UM' : UPDATE_MAP) =
    let update_dynamic_function_table (f_table : Map<VALUE list, TERM>) (updates_of_f : Map<VALUE list, TERM>) =
            Map.fold (fun table args value -> Map.add args value table) f_table updates_of_f
    let apply_to_s_update_map (UM0 : UPDATE_MAP) (UM' : UPDATE_MAP) =
            Map.fold
                ( fun UM f updates_of_f ->
                    Map.change f
                        (function None -> Some (update_dynamic_function_table Map.empty updates_of_f) 
                                | Some f_table -> Some (update_dynamic_function_table f_table updates_of_f)) UM )
                UM0 UM'
    in  apply_to_s_update_map UM0 UM'

and apply_s_update_set eng S U =
    apply_s_update_map S (s_update_set_to_s_update_map eng U)

and sequel_s_state : ENGINE -> UPDATE_MAP -> UPDATE_SET -> UPDATE_MAP = apply_s_update_set

//--------------------------------------------------------------------

and get_env (env : ENV) (var : string) =
    Map.find var env

and add_binding (env : ENV) (var : string, t : TERM, ty : TYPE) =
    Map.add var (t, ty) env

and replace_vars (eng : ENGINE) (env : ENV) (t : TERM) : TERM =
    term_induction eng (fun x -> x) {
        Value      = Value eng
        Initial    = Initial eng
        AppTerm    = AppTerm eng
        CondTerm   = CondTerm eng
        VarTerm    = fun (v, _) -> get_env env v |> fst
        QuantTerm  = QuantTerm eng
        LetTerm    = LetTerm eng
        DomainTerm = DomainTerm eng
    } t

//--------------------------------------------------------------------

and get_values eng (ts : TERM list) : VALUE list option =    // only if all arguments are values
    List.fold ( function
                |   Some ts -> (fun t -> match get_term' eng t with Value' v -> Some(v :: ts) | _ -> None)
                |   None -> (fun _ -> None) ) (Some []) (List.rev ts)

//--------------------------------------------------------------------

and add_cond (G : TERM) (C : PATH_COND) = (Set.add G C)

//--------------------------------------------------------------------
//
//  SMT solver interface
//  
//--------------------------------------------------------------------

let rec smt_map_term (eng as Engine eid) (t : TERM) : SmtInterface.SMT_EXPR =
    let C = engines[eid].smt_ctx
    let (ctx, con, fct) = (!C.ctx, !C.con, !C.fct)
    let get_term_type' t = get_type' eng (get_term_type eng t)
    let type_to_string, get_type = type_to_string eng, get_type eng

    let smt_map_ITE (eng as Engine eid) (G_, t1_, t2_) : SmtInterface.SMT_EXPR =
        let err_msg (G, T_G, t1, T_t1, t2, T_t2) =
            failwith (sprintf "smt_map_ITE: type error: for term %s the expected type is (Boolean, T, T), where T is Boolean, Integer or a user-defined type; type (%s, %s, %s) found instead"
                (term_to_string eng (CondTerm eng (G, t1, t2))) (type_to_string T_G) (type_to_string T_t1) (type_to_string T_t2) )
        match (smt_map_term eng G_, get_term_type' G_, smt_map_term eng t1_, get_term_type' t1_, smt_map_term eng t2_, get_term_type' t2_) with
        |   (SmtInterface.SMT_BoolExpr G, Boolean', SmtInterface.SMT_BoolExpr t1, Boolean', SmtInterface.SMT_BoolExpr t2, Boolean') ->
                SmtInterface.SMT_BoolExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.BoolExpr)
        |   (SmtInterface.SMT_BoolExpr G, Boolean', SmtInterface.SMT_IntExpr t1, Integer', SmtInterface.SMT_IntExpr t2, Integer') ->
                SmtInterface.SMT_IntExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.IntExpr)
        |   (SmtInterface.SMT_BoolExpr G, Boolean', SmtInterface.SMT_Expr t1, TypeCons' (tyname1, []), SmtInterface.SMT_Expr t2, TypeCons' (tyname2, [])) ->
                if tyname1 = tyname2
                then SmtInterface.SMT_Expr (ctx.MkITE (G, (t1 : Microsoft.Z3.Expr), (t2 : Microsoft.Z3.Expr)) : Microsoft.Z3.Expr)
                else err_msg (G_, BooleanType eng, t1_, TypeCons eng (tyname1, []), t2_, TypeCons eng (tyname2, []))
        |   (_, T_G, _, T_t1, _, T_t2) -> err_msg (G_, get_type T_G, t1_, get_type T_t1, t2_, get_type T_t2)

    let smt_map_app_term (eng : ENGINE) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
        let FctName f, { fct_id = fct_id; fct_kind = f_kind; fct_interpretation = fct_intp } = get_function' eng f_id
        if (match fct_intp with StaticBackground _ -> true | _ -> false) then 
            let es = ts >>| smt_map_term eng
            //let f' = get_function' eng f
            match (f, es) with
            |   ("=",       [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
            |   ("=",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
            |   ("=",       [ SmtInterface.SMT_Expr e1;     SmtInterface.SMT_Expr e2 ])     -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
            |   ("!=",      [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
            |   ("!=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
            |   ("!=",      [ SmtInterface.SMT_Expr e1;     SmtInterface.SMT_Expr e2 ])     -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
            |   ("not",     [ SmtInterface.SMT_BoolExpr e ])                                -> SmtInterface.SMT_BoolExpr (ctx.MkNot e)
            |   ("and",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkAnd (e1, e2))
            |   ("or",      [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkOr (e1, e2))
            |   ("xor",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkXor (e1, e2))
            |   ("implies", [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkImplies (e1, e2))
            |   ("iff",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkIff (e1, e2))
            |   (">",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkGt (e1, e2))
            |   (">=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkGe (e1, e2))
            |   ("<",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkLt (e1, e2))
            |   ("<=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkLe (e1, e2))
            |   ("+",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkAdd (e1, e2) :?> Microsoft.Z3.IntExpr)
            |   ("-",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkSub (e1, e2) :?> Microsoft.Z3.IntExpr)
            |   ("*",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkMul (e1, e2) :?> Microsoft.Z3.IntExpr)
            |   _ -> failwith (sprintf "smt_map_term_background_function: error (t = %s)" (term_to_string eng (AppTerm eng (FctId fct_id, ts))))
        else failwith (sprintf "smt_map_app_term: '%s' is not a background function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

    let smt_map_initial (eng : ENGINE) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
        let FctName f, { fct_kind = f_kind } = get_function' eng f_id
        if f_kind = Signature.Controlled then
            let sign = engines.[eid].signature
            let fail (f, dom, ran) =
                failwith (sprintf "smt_map_term_user_defined_function: function '%s : %s -> %s' not found" f (Signature.type_list_to_string dom) (Signature.type_to_string ran))
            match (f, Signature.fct_type f sign, ts >>| fun t -> smt_map_term eng t) with
            |   (f, (dom, Signature.Boolean), es) ->
                    try SmtInterface.SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.BoolExpr) with _ -> fail (f, dom, Signature.Boolean)
            |   (f, (dom, Signature.Subset (_, Signature.Boolean)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                    try SmtInterface.SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.BoolExpr) with _ -> fail (f, dom, Signature.Boolean)
            |   (f, (dom, Signature.Integer), es) ->
                    try SmtInterface.SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.IntExpr) with _ -> fail (f, dom, Signature.Integer)
            |   (f, (dom, Signature.Subset (_, Signature.Integer)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                    try SmtInterface.SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.IntExpr) with _ -> fail (f, dom, Signature.Integer)
            |   (f, (dom, (ran as Signature.TypeCons (tyname, []))), es) ->
                    let (kind, ar) = (Signature.type_kind tyname sign, Signature.type_arity tyname sign)
                    if kind <> Signature.EnumType || ar <> 0 then failwith (sprintf "smt_map_term_user_defined_function: types in function '%s : %s -> %s' not supported" f (Signature.type_list_to_string dom) (Signature.type_to_string ran))
                    try SmtInterface.SMT_Expr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr))) with _ -> fail (f, dom, ran)
            |   (f, (_, ran), _) -> failwith (sprintf "smt_map_term_user_defined_function : error (t = %s)" (term_to_string eng (AppTerm eng (f_id, ts))))
        else failwith (sprintf "smt_map_initial: '%s' is not a controlled function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

    match get_smt_expr eng t with
    |   Some e -> e
    |   None ->
            let result = 
                match get_term' eng t with
                |   Value' (INT i)           -> SmtInterface.SMT_IntExpr (ctx.MkInt i)
                |   Value' (BOOL b)          -> SmtInterface.SMT_BoolExpr (ctx.MkBool b)
                |   Value' (CELL (cons, [])) -> SmtInterface.SMT_Expr (Map.find cons (!C.con))
                |   Initial' (f, xs)         -> smt_map_initial eng (f, xs >>| Value eng)
                |   CondTerm' (G, t1, t2)    -> smt_map_ITE eng (G, t1, t2)
                |   AppTerm' (f, ts)         -> smt_map_app_term eng (f, ts)
                |   _ -> failwith (sprintf "smt_map_term: not supported (t = %s)" (term_to_string eng t))
            set_smt_expr eng t result
            result

//--------------------------------------------------------------------
//
//  symbolic evaluator
//  
//  through the symbolic evaluation functions:
//  - S or eng   stands for engine
//  - env        stands for variable environment
//
//--------------------------------------------------------------------

let s_not eng t =
    match get_term' eng t with
    |   Value' (BOOL b) -> Value eng (BOOL (not b))
    |   _ -> AppTerm eng (NOT eng, [t])

let s_equals eng (t1, t2) =
    if t1 = t2 then TRUE eng
    else
        match (get_term' eng t1, get_term' eng t2) with
        |   (Value' x1, Value' x2) -> if x1 = x2 then TRUE eng else FALSE eng
        |   (_, _) -> AppTerm eng (EQUALS eng, [t1; t2])

let s_and eng (phi1, phi2)=
    match (get_term' eng phi1, get_term' eng phi2) with
    |   (Value' (BOOL false), _) -> FALSE eng
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> FALSE eng
    |   (_, Value' (BOOL true)) -> phi1
    |   (phi1', phi2') -> if phi1 = phi2 then phi1 else AppTerm eng (AND eng, [phi1; phi2])

let s_or eng (phi1, phi2) =
    match (get_term' eng phi1, get_term' eng phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> TRUE eng
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> TRUE eng
    |   (_, _) -> if phi1 = phi2 then phi1 else AppTerm eng (OR eng, [phi1; phi2])

let s_xor eng (phi1, phi2) =
    match (get_term' eng phi1, get_term' eng phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> s_not eng phi2
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> s_not eng phi1
    |   (_, _) -> if phi1 = phi2 then FALSE eng else AppTerm eng (get_fct_id eng "xor", [phi1; phi2])

let s_implies eng (phi1, phi2) =
    match (get_term' eng phi1, get_term' eng phi2) with
    |   (Value' (BOOL b1), _) -> s_or eng (Value eng (BOOL (not b1)), phi2)
    |   (_, Value' (BOOL b2)) -> s_or eng (s_not eng phi1, Value eng (BOOL b2))
    |   (_, _) -> if phi1 = phi2 then TRUE eng else AppTerm eng (get_fct_id eng "implies", [phi1; phi2])

let s_iff eng (phi1, phi2) =
    match (get_term' eng phi1, get_term' eng phi2) with
    |   (Value' (BOOL false), _) -> s_not eng phi2
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> s_not eng phi1
    |   (_, Value' (BOOL true)) -> phi1
    |   (_, _) -> if phi1 = phi2 then TRUE eng else AppTerm eng (get_fct_id eng  "iff", [phi1; phi2])


let ctx_condition eng C =
    List.fold (fun a -> fun b -> s_and eng (a, b)) (TRUE eng) (Set.toList C)

let smt_assert (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_term_type eng phi = BooleanType eng
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; (!C.slv).Assert be
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_assert' expects a Boolean term, %s found instead " (term_to_string eng phi))

let with_extended_path_cond (eng : ENGINE) (G : TERM) eval_fct (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) =
    smt_solver_push eng
    smt_assert eng G
    let result = eval_fct () eng (UM, env, add_cond G pc)
    smt_solver_pop eng
    result

//--------------------------------------------------------------------

let smt_formula_is_true (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_term_type eng phi = BooleanType eng
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check ((!C.ctx).MkNot be) = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_true: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_formula_is_true' expects a Boolean term, %s found instead " (term_to_string eng phi))

let smt_formula_is_false (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_term_type eng phi = BooleanType eng
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check be = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_false: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_formula_is_false' expects a Boolean term, %s found instead " (term_to_string eng phi))

let rec interpretation (eng : ENGINE) (UM : UPDATE_MAP) (pc : PATH_COND) (f as FctId f_id) (xs : VALUE list) =
    let Value = Value eng
    let eval_fct_definition_in_curr_state (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> add_binding env' (arg, Value x, type_of_value eng x)) Map.empty args xs
        let body' = body        // alternative: // let body' = replace_vars eng env body
        s_eval_term body' eng (UM, env, pc)
    let eval_fct_definition_in_initial_state (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> add_binding env' (arg, Value x, type_of_value eng x)) Map.empty args xs
        let body' = body        // alternative: // let body' = replace_vars eng env body
        s_eval_term body' eng (Map.empty, env, Set.empty)   //!!!! to be modified if at some point initial state constraints are implemented => path condition may then be non-empty
    let FctName f_name, { fct_interpretation = f_intp; fct_id = f_id } = get_function' eng f
    match f_intp with
    |   Constructor (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticBackground (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticUserDefined (_ : VALUE list -> VALUE, Some (fct_def : string list * TERM)) ->
            // memoization of computed values for static user-defined functions
            let res = initial_state_eval_res eng (AppTerm eng (f, xs >>| Value))
            match !res with
            |   Some t' -> t'
            |   None -> let t' = eval_fct_definition_in_initial_state fct_def xs in res := Some t'; t'
    |   ControlledInitial (_ : VALUE list -> VALUE, Some (fct_def : string list * TERM)) -> 
            try Map.find xs (Map.find (FctId f_id) UM)
            with _ ->
                let res = initial_state_eval_res eng (AppTerm eng (f, xs >>| Value))
                match !res with
                |   Some t' -> t'
                |   None -> let t' = eval_fct_definition_in_initial_state fct_def xs in res := Some t'; t'
    |   ControlledUninitialized ->
            try Map.find xs (Map.find (FctId f_id) UM)
            with _ -> Initial eng (f, xs)
    |   Derived (fct_def : string list * TERM) ->
            eval_fct_definition_in_curr_state fct_def xs
    |   StaticSymbolic (s_fct_interpretation: TERM list -> TERM) ->
            failwith (sprintf "Engine.interpretation: static symbolic function '%s' - not implemented" f_name)
    |   StaticUserDefined (_, None) ->
            failwith (sprintf "definition of static function '%s' missing" f_name)
    |   ControlledInitial (_, None) -> 
            failwith (sprintf "initial state definition of controlled function '%s' missing" f_name)

and smt_eval_formula (phi : TERM) (eng : ENGINE) (UM : UPDATE_MAP, env, pc : PATH_COND) =
    // precondition: term_type sign phi = Boolean
    if !trace > 0 then fprintf stderr "smt_eval_formula(%s) -> " (term_to_string eng phi)
    let phi = expand_term phi eng (UM, env, pc)
    let result =
        if (!SymbEval.use_smt_solver && smt_formula_is_true eng phi)
        then TRUE eng
        else if (!SymbEval.use_smt_solver && smt_formula_is_true eng (s_not eng phi))
        then FALSE eng
        else phi
    if !trace > 0 then fprintf stderr "%s\n" (term_to_string eng result)
    result

and expand_term t (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let get_term_type, type_to_string = get_term_type eng, type_to_string eng
    term_induction eng (fun x -> x) {
        Value   = fun x (UM, env, pc) -> Value eng x;
        Initial = fun (f, xs) (UM, env, pc) -> Initial eng (f, xs)
        AppTerm = fun (f, ts) (UM : UPDATE_MAP, env, pc) ->
            let FctName name, { fct_kind = f_kind; fct_interpretation = f_intp } = get_function' eng f
            match f_intp with
            |   StaticUserDefined (_, Some (args, body)) ->
                    let ts = ts >>| fun t -> t (UM, env, pc)
                    let env = List.fold2 (fun env' arg t -> add_binding env' (arg, s_eval_term t eng (UM, env, pc), get_term_type t)) Map.empty args ts
                    s_eval_term body eng (UM, env, pc)
            | _ -> AppTerm eng (f, ts >>| fun t -> t (UM, env, pc))
        CondTerm  = fun (G, t1, t2) (UM : UPDATE_MAP, env, pc) -> CondTerm eng (G (UM, env, pc), t1 (UM, env, pc), t2 (UM, env, pc));
        VarTerm   = fun (v, _) (UM : UPDATE_MAP, env, pc) -> fst (get_env env v);
        QuantTerm = fun (q_kind, v, t_set, t_cond) (UM : UPDATE_MAP, env, pc) -> expand_quantifier (q_kind, v, t_set, t_cond) eng (UM, env, pc);
        LetTerm   = fun (v, t1, t2) (UM : UPDATE_MAP, env, pc) ->
                        let t1_val = t1 (UM, env, pc)
                        t2 (UM, add_binding env (v, t1_val, get_term_type t1_val), pc);
        DomainTerm = fun dom (UM : UPDATE_MAP, env, pc) ->
            match enum_finite_type eng dom with
            |   Some xs -> Value eng (SET ((main_type_of eng dom) |> to_signature_type eng, xs))
            |   _ -> failwith (sprintf "Engine.expand_term: domain of type '%s' is not enumerable" (dom |> type_to_string))
    } t ((UM : UPDATE_MAP), (env : ENV), (pc : PATH_COND))

and expand_quantifier (q_kind, v, t_set : UPDATE_MAP * ENV * PATH_COND -> TERM, t_cond : UPDATE_MAP * ENV * PATH_COND -> TERM)
                        (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let t_set = t_set (UM, env, pc)
    let t_set_type = get_term_type eng t_set
    let elem_type =
        match get_type' eng t_set_type with
        |   Powerset' tyname -> tyname
        |   _ -> failwith (sprintf "Engine.expand_quantifier: expected a set or domain type, %s found instead" (type_to_string eng t_set_type))
    match get_term' eng (s_eval_term t_set eng (UM, env, pc)) with
    |   Value' (Background.SET (_, xs)) ->
            let eval_instance x = t_cond (UM, add_binding env (v, Value eng x, elem_type), pc)
            let t_conds = List.map eval_instance (Set.toList xs)
            match q_kind with
            |   AST.Forall -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_and eng (t_accum, t1)) (TRUE eng)  t_conds
            |   AST.Exist  -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_or  eng (t_accum, t1)) (FALSE eng) t_conds
            |   AST.ExistUnique -> failwith "Engine.expand_quantifier: 'ExistUnique' not implemented"
    |   x -> failwith (sprintf "Engine.expand_quantifier: not a set (%s)" (term_to_string eng t_set))

and try_case_distinction_for_term_with_finite_range (eng : ENGINE) (UM : UPDATE_MAP, env, pc : PATH_COND) (f : FCT_ID) (ts0 : TERM list) : TERM =
    let generate_cond_term (t, cases : (VALUE * TERM) list) =
        let mkCondTerm (G, t1, t2) = CondTerm eng (G, t1, t2)
        let mkEq t1 t2 = s_equals eng (t1, t2)
        let rec mk_cond_term (cases : (VALUE * TERM) list) =
            match cases with
            |   [] -> failwith "mk_cond_term: empty list of cases"
            |   [(t1, t2)] -> t2
            |   (t1, t2) :: cases' ->
                    let eq_term  = s_eval_term (mkEq t (Value eng t1)) eng (UM, env, pc)
                    match get_term' eng eq_term with
                    |   Value' (BOOL true) -> t2
                    |   Value' (BOOL false) -> mk_cond_term cases'
                    |   _ -> mkCondTerm (eq_term, t2, mk_cond_term cases')
        mk_cond_term cases
    let make_case_distinction (t : TERM) (elem_term_pairs : (VALUE * TERM) list) =
        if List.isEmpty elem_term_pairs
        then failwith (sprintf "Engine.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string eng t))
        generate_cond_term (t, elem_term_pairs)
    let rec F past_args = function
    |   [] -> AppTerm eng (f, List.rev past_args)
    |   t1 :: ts' ->
            let t1 = s_eval_term t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' x1 -> F (Value eng x1 :: past_args) ts'
            |   _ ->
                    match (try enum_finite_type eng (get_term_type eng t1) with _ -> None) with
                    |   None ->
                            failwith (sprintf "arguments of dynamic function '%s' must be fully evaluable for unambiguous determination of a location\n('%s' found instead)"
                                        (fct_name eng f) (term_to_string eng (AppTerm eng (f, ts0))))
                    |   Some elems ->
                            make_case_distinction t1 (List.map (fun elem -> (elem, F (Value eng elem :: past_args) ts')) (Set.toList elems))
    let result = F [] ts0
    result

and eval_app_term (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) (fct_id : FCT_ID, ts : (ENGINE -> UPDATE_MAP * ENV * PATH_COND -> TERM) list) : TERM = 
//  let with_extended_path_cond = with_extended_path_cond C
    //if !trace > 0 then fprintfn stderr "|signature|=%d | eval_app_term %s%s\n" (Map.count sign) (spaces !level) (term_to_string sign (AppTerm (fct_name, [])))
    let rec F (ts_past : TERM list) ts =
        match ts with
        |   t :: ts_fut ->
                let t = t eng (UM, env, pc)
                match get_term' eng t with
                |   Value' x1             -> F (t :: ts_past) ts_fut
                |   Initial'  (f, xs)     -> F (t :: ts_past) ts_fut
                |   CondTerm' (G1, t11, t12) -> s_eval_term_ (CondTerm eng (G1, F ts_past ((fun _ _ -> t11) :: ts_fut), F ts_past ((fun _ _ -> t12) :: ts_fut))) eng (UM, env, pc)
                |   LetTerm'  (v, t1, t2) -> F (t :: ts_past) ts_fut
                |   VarTerm'  v           -> F (t :: ts_past) ts_fut
                |   AppTerm'  _           -> F (t :: ts_past) ts_fut
                |   QuantTerm' _          -> failwith "Engine.eval_app_term: QuantTerm not implemented"
                |   DomainTerm' _         -> failwith "Engine.eval_app_term: DomainTerm not implemented"
        |   [] ->
                let FctName f_name, { fct_kind = f_kind; fct_interpretation = f_intp }  = get_function' eng fct_id
                match (f_name, List.rev ts_past) with
                |   "and", [ t1; t2 ] -> s_and eng (t1, t2)
                |   "or", [ t1; t2 ]  -> s_or eng (t1, t2)
                |   "xor", [ t1; t2 ] -> s_xor eng (t1, t2)
                |   "implies", [ t1; t2 ] -> s_implies eng (t1, t2)
                |   "iff", [ t1; t2 ] -> s_iff eng (t1, t2)
                |   "=", [ t1; t2 ]   -> s_equals eng (t1, t2)
                |   f, ts ->
                    match get_values eng ts with
                    |   Some xs -> interpretation eng UM pc fct_id xs
                    |   None ->
                        match f_kind with
                        |   Signature.Static ->
                                let t = AppTerm eng (fct_id, ts)
                                match get_type' eng (get_term_type eng t) with
                                |   Boolean' ->
                                        AppTerm eng (fct_id, ts)
                                        // if Set.contains t pc                  then TRUE eng
                                        // else if Set.contains (s_not eng t) pc then FALSE eng
                                        // else smt_eval_formula t eng (UM, env, pc)
                                | _ -> AppTerm eng (fct_id, ts)
                        |   Signature.Controlled -> s_eval_term (try_case_distinction_for_term_with_finite_range eng (UM, env, pc) fct_id ts) eng (UM, env, pc)
                        |   other_kind -> failwith (sprintf "Engine.eval_app_term: kind '%s' of function '%s' not implemented" (Signature.fct_kind_to_string other_kind) f)
    let f_name = fct_name eng fct_id           //!!!!!!!!!!!!! this can replaced by fct_id
    match (f_name, ts) with
    |   "and", [ t1; t2 ] ->
            let t1 = t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' (BOOL false) -> FALSE eng
            |   Value' (BOOL true)  -> t2 eng (UM, env, pc)        // alternative: with_extended_path_cond t1' (fun _ -> t2) (S, env, C)
            |   t1' ->
                let t2 = t2 eng (UM, env, pc)
                match get_term' eng t2 with
                |   Value' (BOOL false) -> FALSE eng
                |   Value' (BOOL true) -> t1    // with_extended_path_cond t2' (fun _ -> t1) (S, env, C)
                |   t2' -> if t1' = t2' then t1 else F [] [(fun _ _ -> t1); fun _ _ -> t2]
    |   "or", [ t1; t2 ] ->
            let t1 = t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' (BOOL true) -> TRUE eng
            |   Value' (BOOL false) -> t2 eng (UM, env, pc)
            |   t1' ->
                let t2 = t2 eng (UM, env, pc)
                match get_term' eng t2 with
                |   Value' (BOOL true) -> TRUE eng
                |   Value' (BOOL false) -> t1
                |   t2' -> if t1' = t2' then t1 else F [] [(fun _ _ -> t1); fun _ _ -> t2]
    |   "implies", [ t1; t2 ] ->
            let t1 = t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' (BOOL false) -> TRUE eng
            |   Value' (BOOL true)  -> t2 eng (UM, env, pc)       // with_extended_path_cond t1' ( fun _ _ -> t2) (S, env, C)
            |   t1' ->
                let t2 = t2 eng (UM, env, pc)
                match get_term' eng t2 with
                |   Value' (BOOL false) -> s_not eng t1
                |   Value' (BOOL true)  -> TRUE eng
                |   t2' -> if t1' = t2' then TRUE eng else F [] [(fun _ _ -> t1); fun _ _ -> t2]
    |   "iff", [ t1; t2 ] ->
            let t1 = t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' (BOOL false) -> s_not eng (t2 eng (UM, env, pc))
            |   Value' (BOOL true)  -> t2 eng (UM, env, pc)
            |   t1' ->
                let t2 = t2 eng (UM, env, pc)
                match get_term' eng t2 with
                |   Value' (BOOL false) -> s_not eng t1
                |   Value' (BOOL true)  -> t1
                |   t2' -> if t1' = t2' then TRUE eng else F [] [(fun _ _ -> t1); fun _ _ -> t2]
    |   "=", [ t1; t2 ] ->
            let t1 = t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   t1' as Value' x1 ->
                let t2 = t2 eng (UM, env, pc)
                match get_term' eng t2 with
                |   Value' x2 -> Value eng (BOOL (x1 = x2))
                |   t2' -> F [] [(fun _ _ -> t1);  fun _ _ -> t2]
            |   t1' -> F [] [( fun _ _ -> t1);  fun _ _ -> t2 eng (UM, env, pc)]
    |   _ ->
    F [] ts

and eval_cond_term (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) (G, t1 : ENGINE -> UPDATE_MAP * ENV * PATH_COND -> TERM, t2) : TERM = 
    let get_term_type' t = get_type' eng (get_term_type eng t)
    let with_extended_path_cond = with_extended_path_cond eng
    let term_to_string = term_to_string eng
    let G = G eng (UM, env, pc)
    match get_term' eng G with
    |   Value' (BOOL true)  -> t1 eng (UM, env, pc)
    |   Value' (BOOL false) -> t2 eng (UM, env, pc)
    |   CondTerm' (G', G1, G2) ->
            if get_term_type' G1 <> Boolean' || get_term_type' G2 <> Boolean'
            then failwith (sprintf "eval_cond_term: '%s' and '%s' must be boolean terms" (term_to_string G1) (term_to_string G2))
            else let t1_G'     = t1 eng (UM, env, add_cond G' (add_cond G1 pc))
                 let t1_not_G' = t1 eng (UM, env, add_cond (s_not eng G') (add_cond G1 pc))
                 let t2_G'     = t2 eng (UM, env, add_cond G' (add_cond G2 pc))
                 let t2_not_G' = t2 eng (UM, env, add_cond (s_not eng G') (add_cond G2 pc))
                 s_eval_term (CondTerm eng (G', CondTerm eng (G1, t1_G', t2_G'), CondTerm eng (G2, t1_not_G', t2_not_G'))) eng (UM, env, pc)
    |   _ ->    if (!trace > 1)
                then fprintfn stderr "\n%sctx_condition: %s" (spaces !level) (term_to_string (ctx_condition eng pc))
                if not SymbEval.simplify_cond then
                    // version 1: no simplification whatsoever (inefficient, but useful for debugging)
                    CondTerm eng (G, t1 eng (UM, env, add_cond G pc), t2 eng (UM, env, add_cond (s_not eng G) pc))
                else 
                    // version 2: with simplification
                    if Set.contains G pc
                    then t1 eng (UM, env, pc)
                    else if Set.contains (s_not eng G) pc
                    then t2 eng (UM, env, pc)
                    else let (t1', t2') = (t1 eng (UM, env, add_cond G pc), t2 eng (UM, env, add_cond (s_not eng G) pc))
                         if t1' = t2' then t1'
                         else if not !SymbEval.use_smt_solver
                              then  let t1' = s_eval_term t1' eng (UM, env, add_cond G pc)
                                    let t2' = s_eval_term t2' eng (UM, env, add_cond (s_not eng G) pc)
                                    if t1' = t2' then t1' else CondTerm eng (G, t1', t2')
                              else  let t1' = with_extended_path_cond G             ( fun _ -> s_eval_term t1') (UM, env, pc)  
                                    let t2' = with_extended_path_cond (s_not eng G) ( fun _ -> s_eval_term t2') (UM, env, pc)  
                                    if t1' = t2' then t1' else CondTerm eng (G, t1', t2')
and eval_let_term (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) (v, t1, t2) : TERM =
    let t1 = t1 eng (UM, env, pc)
    t2 eng (UM, add_binding env (v, t1, get_term_type eng t1), pc)
    // let env' = add_binding env (v, t1, get_type eng t1)
    // let t2 = t2 eng (UM, env', pc)
    // let t2 = replace_vars eng env' t2
    // t2 eng (UM, env', pc)

and s_eval_term_ (t : TERM) (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    term_induction eng (fun x -> x) {
        Value      = fun x C _ -> Value C x;
        Initial    = fun (f, xs) C _ -> Initial C (f, xs);
        AppTerm    = fun (f, ts) C (UM, env, pc) -> eval_app_term C (UM, env, pc) (f, ts)
        CondTerm   = fun (G, t1, t2) C (UM, env, pc) -> eval_cond_term C (UM, env, pc) (G, t1, t2);
        VarTerm    = fun (v, _) -> fun C (_, env, _) -> fst (get_env env v);
        QuantTerm  = fun (q_kind, v, t_set, t_cond) C (UM, env, pc) -> expand_quantifier (q_kind, v, t_set C, t_cond C) C (UM, env, pc);
        LetTerm    = fun (v, t1, t2) C (_, env, _) -> eval_let_term C (UM, env, pc) (v, t1, t2) 
        DomainTerm = fun dom C (_, _, _) ->
            match enum_finite_type eng dom with
            |   Some xs -> Value C (SET (main_type_of eng dom |> to_signature_type eng, xs))
            |   None -> failwith (sprintf "Engine.s_eval_term_: domain of type '%s' is not enumerable" (dom |> type_to_string eng))
    } t eng (UM, env, pc)

and s_eval_term (t : TERM) (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let t = s_eval_term_ t eng (UM, env, pc)
    if get_type' eng (get_term_type eng t) = Boolean'
    then    match get_term' eng t with
            |   Value' (BOOL _)  -> t
            |   _ -> smt_eval_formula t eng (UM, env, pc)
    else    t

//--------------------------------------------------------------------

let rec try_case_distinction_for_update_with_finite_domain
        (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND)
        (f : FCT_ID) (ts0 : TERM list) (t_rhs : TERM): RULE =
    let (CondRule, UpdateRule) = (CondRule eng, UpdateRule eng)
    let mkEq (t1 : TERM) t2 = s_equals eng (t1, t2)  // AppTerm' (Boolean, (FctName "=", [t1; t2]))
    let generate_cond_rule (t, cases : (VALUE * RULE) list) : RULE =
        let t = s_eval_term t eng (UM, env, pc)
        let ty = get_term_type eng t
        let rec mk_cond_rule cases =
            match cases with
            |   [] -> failwith "mk_cond_rule: empty list of cases"
            |   [(t1, R)] -> s_eval_rule R eng (UM, env, pc)
            |   (t1, R) :: cases' ->
                    let eq_term0 = mkEq t (Value eng t1)
                    let eq_term  = s_eval_term eq_term0 eng (UM, env, pc)
                    match get_term' eng eq_term with
                    |   Value' (BOOL true) -> s_eval_rule R eng (UM, env, pc)
                    |   Value' (BOOL false) -> mk_cond_rule cases'
                    |   _ -> CondRule (eq_term, s_eval_rule R eng (UM, env, pc), mk_cond_rule cases')
        mk_cond_rule cases
    let make_case_distinction (t : TERM) (elem_rule_pairs : (VALUE * RULE) list) =
        if List.isEmpty elem_rule_pairs
        then failwith (sprintf "Engine.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string eng t))
        generate_cond_rule (t, elem_rule_pairs)
    let rec F past_args = function
        |   [] -> UpdateRule ((f, List.rev past_args), t_rhs)
        |   t1 :: ts' ->
            let t1 = s_eval_term t1 eng (UM, env, pc)
            match get_term' eng t1 with
            |   Value' x1 -> F (Value eng x1 :: past_args) ts'
            |   _ ->
                    match (try enum_finite_type eng (get_term_type eng t1) with _ -> None) with
                    |   None ->
                            failwith (sprintf "location (%s, (%s)) on the lhs of update cannot be fully evaluated"
                                        (fct_name eng f) (String.concat ", " (ts0 >>| term_to_string eng)))
                    |   Some elems ->
                            make_case_distinction t1 (List.map (fun elem -> (elem, F (Value eng elem :: past_args) ts')) (Set.toList elems))
    F [] ts0

and s_eval_rule (R : RULE) (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
    let (CondRule, UpdateRule, S_Updates) = (CondRule eng, UpdateRule eng, S_Updates eng)
    let (ParRule, SeqRule, IterRule, skipRule) = (ParRule eng, SeqRule eng, IterRule eng, skipRule eng)
    let s_eval_term t = s_eval_term t eng
    let s_eval_rule R = s_eval_rule R eng
    let get_type, get_s_update_set, get_s_update_set', s_update_set_union, s_update_set_empty =
        get_type eng, get_s_update_set eng, get_s_update_set' eng, s_update_set_union eng, s_update_set_empty eng
    let with_extended_path_cond = with_extended_path_cond eng
    let rule_to_string, term_to_string, pp_rule = rule_to_string eng, term_to_string eng, pp_rule eng

    if (!trace > 1)
    then fprintf stderr "%s----------------------\n%ss_eval_rule %s\n%s\n\n"
            (spaces !level) (spaces !level) (show_s_update_map eng UM) (toString 80 (indent (!level) (pp_rule R)))
    level := !level + 1

    let eval_update ((f, ts), t_rhs) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
        if !trace > 0 then fprintf stderr "eval_update: %s\n" (rule_to_string (UpdateRule ((f, ts), t_rhs)))
        match get_term' eng (s_eval_term t_rhs (UM, env, pc)) with
        |   CondTerm' (G, t1, t2) ->
                s_eval_rule (CondRule (G, UpdateRule ((f, ts), t1), UpdateRule ((f, ts), t2))) (UM, env, pc)
        |   _ ->
            let rec F (ts_past : TERM list) : TERM list -> RULE = function
                |   (t1 :: ts_fut) ->
                    match get_term' eng t1 with
                    |   Value' _        -> F (t1 :: ts_past) ts_fut
                    |   Initial' _      -> F (t1 :: ts_past) ts_fut
                    |   CondTerm' (G1, t11, t12) ->
                           s_eval_rule (CondRule (G1, F ts_past (t11 :: ts_fut), F ts_past (t12 :: ts_fut))) (UM, env, pc)
                    |   QuantTerm' _    -> failwith "Engine.eval_app_term: QuantTerm not implemented"
                    |   LetTerm' _      -> failwith "Engine.eval_app_term: LetTerm not implemented"
                    |   VarTerm' _      -> F (s_eval_term_ t1 eng (UM, env, pc) :: ts_past) ts_fut
                    |   AppTerm' _      -> F (s_eval_term_ t1 eng (UM, env, pc) :: ts_past) ts_fut
                    |   DomainTerm' _   -> failwith "Engine.eval_app_term: DomainTerm not implemented"
                |   [] ->
                    match get_values eng (ts_past >>| fun t -> s_eval_term t (UM, env, pc)) with
                    |   Some xs -> S_Updates (get_s_update_set (Set.singleton ((f, List.rev xs), s_eval_term t_rhs (UM, env, pc))))
                    |   None -> try_case_distinction_for_update_with_finite_domain eng (UM, env, pc) f ts t_rhs
            F [] ts

    let eval_cond (G, R1, R2) (UM, env, pc) = 
        let get_term_type' t = get_type' eng (get_term_type eng t)
        let G = s_eval_term G (UM, env, pc)
        match get_term' eng G with
        |   Value' (BOOL true)  -> s_eval_rule R1 (UM, env, pc)
        |   Value' (BOOL false) -> s_eval_rule R2 (UM, env, pc)
        |   CondTerm' (G', G1, G2) ->
                if get_term_type' G1 <> Boolean' || get_term_type' G2 <> Boolean'
                then failwith (sprintf "s_eval_rule.eval_cond: '%s' and '%s' must be boolean terms" (term_to_string G1) (term_to_string G2))
                else s_eval_rule (CondRule (G', CondRule (G1, R1, R2), CondRule (G2, R1, R2))) (UM, env, pc)
        |   _ ->    //let (R1', R2') = (s_eval_rule R1 (S, env, add_cond G C), s_eval_rule R2 (S, env, add_cond (s_not G) C)_
                    if not !SymbEval.use_smt_solver
                    then    let R1' = s_eval_rule R1 (UM, env, (add_cond G pc))
                            let R2' = s_eval_rule R2 (UM, env, (add_cond (s_not eng G) pc))
                            if R1' = R2' then R1' else CondRule (G, R1', R2')
                    else    let R1' = with_extended_path_cond G           (fun _ _ -> s_eval_rule R1) (UM, env, pc)
                            let R2' = with_extended_path_cond (s_not eng G) (fun _ _ -> s_eval_rule R2) (UM, env, pc)  
                            if R1' = R2' then R1' else CondRule (G, R1', R2')

    let rec eval_par Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates s_update_set_empty
        |   [R1]        -> s_eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_par R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_par R1 R2 (UM, env, pc) : RULE =
        match get_rule' eng (s_eval_rule R1 (UM, env, pc)) with
        |   S_Updates' U1 ->
                match get_rule' eng (s_eval_rule R2 (UM, env, pc)) with
                |   S_Updates' U2 ->
                        S_Updates (s_update_set_union U1 U2)
                |   CondRule' (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, ParRule [ S_Updates U1; R21 ], ParRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R2))
        |   CondRule' (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, ParRule [ R11; R2 ], ParRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R1))

    and eval_seq Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates s_update_set_empty
        |   [R1]        -> s_eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_seq R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_seq R1 R2 (UM, env, pc): RULE = 
        match get_rule' eng (s_eval_rule R1 (UM, env, pc)) with
        |   S_Updates' U1 ->
                let S' =
                    try sequel_s_state eng UM (get_s_update_set' U1)
                    with Error (_, _, InconsistentUpdates (C, _, u1, u2, _)) ->
                            raise (Error (eng, "s_eval_rule.eval_binary_seq",
                                InconsistentUpdates (C, Some (List.ofSeq pc), u1, u2, Some (get_s_update_set' U1))))
                match get_rule' eng (s_eval_rule R2 (S', env, pc)) with
                |   S_Updates' U2 ->
                        S_Updates (s_update_set_seq_merge_2 eng U1 U2)
                |   CondRule' (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, SeqRule [ S_Updates U1; R21 ], SeqRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R2))
        |   CondRule' (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, SeqRule [ R11; R2 ], SeqRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R1))

    and eval_iter R (UM, env, pc) =
        match get_rule' eng (s_eval_rule R (UM, env, pc)) with
        |   S_Updates' U ->
                if s_update_set_is_empty eng U
                then S_Updates s_update_set_empty
                else s_eval_rule (SeqRule [ S_Updates U; IterRule R ]) (UM, env, pc)
        |   CondRule' (G, R1, R2) ->
                //s_eval_rule (SeqRule [ CondRule (G, R1, R2); IterRule R ]) (UM, env, pc)
                s_eval_rule (CondRule (G, SeqRule [R1; IterRule R], SeqRule [R2; IterRule R])) (UM, env, pc)
        |   R' -> failwith (sprintf "SymEvalRules.s_eval_rule: eval_iter_rule - R'' = %s" (rule_to_string (get_rule eng R')))

    and eval_let (v, t, R) (UM, env, pc) =
        let t' = s_eval_term t (UM, env, pc)
        let R' = s_eval_rule R (UM, add_binding env (v, t', get_term_type eng t'), pc)
        R'

    and eval_forall (v, ts, G, R) (UM, env, pc) =
        match get_term' eng (s_eval_term ts (UM, env, pc)) with
        |   Value' (SET (_, xs)) ->
                let eval_instance x =
                    let env' = let t_x = Value eng x in add_binding env (v, t_x, get_term_type eng t_x)
                    CondRule (s_eval_term G (UM, env', pc), s_eval_rule R (UM, env', pc), skipRule)
                let Rs = List.map (fun x -> eval_instance x) (Set.toList xs)
                s_eval_rule (ParRule Rs) (UM, env, pc)
        |   x -> failwith (sprintf "Engine.forall_rule: not a set (%A): %A v" ts x)

    and eval_macro_rule_call (r, args) (UM, env, pc) =
        let (formals, body) =
            match get_rule_def eng r with
            |   Some (formals, body) -> (formals, body)
            |   None -> failwith (sprintf "Engine.eval_macro_rule_call: macro rule '%s' not defined" (get_rule_name eng r))
        let env' =
            List.fold2 (fun env' formal arg -> add_binding env' (formal, s_eval_term arg (UM, env, pc), get_term_type eng arg)) env formals args
        s_eval_rule body (UM, env', pc)
 
    let R_eval =
        match get_rule' eng R with
        |   UpdateRule' ((f, ts), t) -> eval_update ((f, ts), t) (UM, env, pc)
        |   CondRule' (G, R1, R2)    -> eval_cond (G, R1, R2) (UM, env, pc)
        |   ParRule' Rs              -> eval_par Rs (UM, env, pc)
        |   SeqRule' Rs              -> eval_seq Rs (UM, env, pc)
        |   IterRule' R              -> eval_iter R (UM, env, pc)
        |   LetRule' (v, t, R)       -> eval_let (v, t, R) (UM, env, pc) 
        |   ForallRule' (v, t, G, R) -> eval_forall (v, t, G, R) (UM, env, pc) 
        |   MacroRuleCall' (r, args) -> eval_macro_rule_call (r, args) (UM, env, pc)
        |   S_Updates' S             -> R

    level := !level - 1
    if (!trace > 1)
    then fprintf stderr "%ss_eval_rule result = \n%s\n%s----------------------\n" (spaces !level) (toString 120 (indent (!level) (pp_rule R))) (spaces !level)

    R_eval


//--------------------------------------------------------------------
// convert partially evaluated terms and rules to regular ones

let rec reconvert_value (eng : ENGINE) x =
    match x with
    |   UNDEF    -> Value eng x
    |   BOOL b   -> Value eng x
    |   INT i    -> Value eng x
    |   STRING s -> Value eng x
    |   SET (_, fs) -> //AppTerm (FctName "asSet", ?????)
                    failwith "reconvert_value: SET not implemented yet"
    |   CELL (tag, args) -> AppTerm eng (get_fct_id eng tag, args >>| reconvert_value eng)

let reconvert_term (eng : ENGINE) t =
    term_induction eng (fun x -> x) {
        Value      = fun x -> reconvert_value eng x;
        Initial    = fun (f, xs) -> AppTerm eng (f, xs >>| Value eng);
        AppTerm    = AppTerm eng;
        CondTerm   = CondTerm eng;
        VarTerm    = VarTerm eng;
        QuantTerm  = QuantTerm eng;
        LetTerm    = LetTerm eng;
        DomainTerm = DomainTerm eng;
    } t

let reconvert_rule (eng : ENGINE) R = 
    rule_induction eng (reconvert_term eng) {
        UpdateRule = UpdateRule eng;
        CondRule   = CondRule eng;
        ParRule    = ParRule eng;
        SeqRule    = SeqRule eng;
        IterRule   = IterRule eng;
        LetRule    = LetRule eng;
        MacroRuleCall = MacroRuleCall eng;
        ForallRule = ForallRule eng;
        S_Updates  = fun upds -> ParRule eng (List.map (fun ((f, xs), t_rhs) -> UpdateRule eng ((f, xs >>| Value eng), reconvert_term eng t_rhs)) (s_update_set_to_list eng upds))
    } R

//--------------------------------------------------------------------

let count_s_updates eng = rule_induction eng (fun _ -> ()) {
    UpdateRule = fun _ -> failwith "there should be no UpdateRule here";
    CondRule  = fun (_, R1, R2) -> R1 + R2;
    ParRule   = fun _ -> failwith "there should be no ParRule here";
    SeqRule   = fun _ -> failwith "there should be no SeqRule here";
    IterRule  = fun _ -> failwith "there should be no IterRule here";
    LetRule   = fun _ -> failwith "there should be no LetRule here";
    MacroRuleCall = fun _ -> failwith "there should be no MacroRuleCall here";
    ForallRule = fun _ -> failwith "there should be no ForallRule here";
    S_Updates = fun _ -> 1;   // not relevant, but define somehow to allow printing for debugging
}

//--------------------------------------------------------------------

let name_size name = 1

let term_size eng =
    term_induction eng name_size {
        Value = fun _ -> 1;
        AppTerm = fun (f, ts : int list) -> 1 + f + List.sum ts;
        CondTerm = fun (G, t1, t2) -> 1 + G + t1 + t2;
        Initial = fun _ -> 1;
        VarTerm = fun _ -> 1;
        QuantTerm = fun (q_kind, v, t_set, t_cond) -> 1 + t_set + t_cond;
        LetTerm = fun (v, t1, t2) -> 1 + t1 + t2;
        DomainTerm = fun _ -> 1;
    }

let rule_size eng =
    rule_induction eng (term_size eng) {
        S_Updates = fun U -> Set.count (get_s_update_set' eng U);   // not relevant, but define somehow to allow printing for debugging
        UpdateRule = fun ((f, ts), t) -> 1 + 1 + List.sum ts + t;
        CondRule = fun (G, R1, R2) -> 1 + G + R1 + R2;
        ParRule = fun Rs -> 1 + List.sum Rs;
        SeqRule = fun Rs -> 1 + List.sum Rs;
        IterRule = fun R' -> 1 + R';
        LetRule = fun (_, t, R) -> 1 + t + R;
        ForallRule = fun (_, t_set, t_filter, R) -> 1 + t_set + t_filter + R;
        MacroRuleCall = fun (r, ts) -> 1 + 1 + List.sum ts;
    }

//--------------------------------------------------------------------
// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution (eng : ENGINE) (R_in : RULE) (steps : int) : int * RULE =
    if (!trace > 2) then fprintf stderr "symbolic_execution\n"
    if (steps <= 0) then failwith "Engine.symbolic_execution: number of steps must be >= 1"
    //  if (!trace > 2) then fprintf stderr "---\n%s\n---\n" (Signature.signature_to_string (signature_of C))
    let R_in_n_times = [ for _ in 1..steps -> R_in ]
    let R_in' = SeqRule eng (R_in_n_times @ [ skipRule eng ])      // this is to force the application of the symbolic update sets of R_in, thus identifying any inconsistent update sets
    let R_out = s_eval_rule R_in' eng (Map.empty, Map.empty, Set.empty)
    (count_s_updates eng R_out, reconvert_rule eng R_out)

let symbolic_execution_for_invariant_checking (eng : ENGINE) (opt_steps : int option) (R_in : RULE) : unit =
    let (CondRule, UpdateRule, S_Updates) = (CondRule eng, UpdateRule eng, S_Updates eng)
    let (ParRule, SeqRule, IterRule, skipRule) = (ParRule eng, SeqRule eng, IterRule eng, skipRule eng)
    let proc = Process.GetCurrentProcess()
    let capture_cpu_time (proc : Process) =
        (proc.TotalProcessorTime, proc.UserProcessorTime, proc.PrivilegedProcessorTime)
    let measure_cpu_time (proc : Process) (cpu0, usr0, sys0) =
        let (cpu1, usr1, sys1) = capture_cpu_time proc
        ( (cpu1 - cpu0).TotalMilliseconds, (usr1 - usr0).TotalMilliseconds, (sys1 - sys0).TotalMilliseconds )
    let (cpu0, usr0, sys0) = capture_cpu_time proc
    if (!trace > 2) then fprintf stderr "symbolic_execution_for_invariant_checking\n"
    let with_extended_path_cond = with_extended_path_cond eng
    match opt_steps with
    |   Some n -> if n < 0 then failwith "Engine.symbolic_execution_for_invariant_checking: number of steps must be >= 0"
    |   None -> ()
    let UM0 = Map.empty
    let invs = Map.toList (invariants_of eng)
    let counters = ref Map.empty
    let reset_counters () = counters := Map.empty
    let update_counters f inv_id = counters := Map.change inv_id (function Some (m, v, u) -> Some (f (m, v, u)) | None -> Some (f (0, 0, 0))) (!counters)
    let print_counters i () =
        printf "\n--- S_%d summary:\n\n" i
        Map.map (fun inv_id (m, v, u) -> printf "'%s': met on %d paths / definitely violated on %d paths / possibly violated on %d paths\n" inv_id m v u) !counters |> ignore
        let (cpu, usr, sys) = measure_cpu_time proc (cpu0, usr0, sys0)
        print_time (cpu, usr, sys)
        |> ignore
    let rec traverse i conditions R (UM, env, pc) =
        let initial_state_conditions_to_reach_this_state ts =
            sprintf "- this path is taken when the following conditions hold in the initial state:\n%s"
                (String.concat "\n" (List.rev ts >>| fun t -> term_to_string eng (reconvert_term eng t)))
        let show_cumulative_updates sign updates =
            "- cumulative update set for this path:\n" ^
            String.concat "\n"
                (Set.toList updates >>| fun ((f, xs), t) ->
                    sprintf "%s%s := %s"
                        (fct_name eng f) (if List.isEmpty xs then "" else "("^(String.concat ", " (xs >>| value_to_string))^")")
                        (term_to_string sign t))
        let met inv_id =
            update_counters (function (m, v, u) -> (m + 1, v, u)) inv_id
            ""
        let possibly_violated inv_id conditions (updates : UPDATE_SET) t t' = 
            update_counters (function (m, v, u) -> (m, v, u + 1)) inv_id
            sprintf "\n!!! invariant '%s' possibly violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string eng t) (term_to_string eng t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates eng updates)
        let definitely_violated inv_id conditions updates t t' =
            update_counters (function (m, v, u) -> (m, v + 1, u)) inv_id
            sprintf "\n!!! invariant '%s' definitely violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string eng t) (term_to_string eng t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates eng updates)
        let check_invariants invs S0 conditions updates =
            let check_one (inv_id, t) =
                let t' = s_eval_term t eng (apply_s_update_set eng S0 updates, Map.empty, Set.empty)
                if smt_formula_is_true eng t'
                then met inv_id
                else if smt_formula_is_false eng t' then definitely_violated inv_id conditions updates t t'
                else possibly_violated inv_id conditions updates t t'
            printf "%s" (String.concat "" (List.filter (fun s -> s <> "") (List.map check_one invs)))
        match get_rule' eng R with      // check invariants on all paths of state S' = S0 + R by traversing tree of R
        |   CondRule' (G, R1, R2) ->
                with_extended_path_cond G           (fun _ _ -> traverse i (G::conditions) R1) (UM, env, pc)
                with_extended_path_cond (s_not eng G) (fun _ _ -> traverse i ((s_not eng G)::conditions) R2) (UM, env, pc)
        |   S_Updates' updates    ->
                check_invariants invs UM0 conditions (get_s_update_set' eng updates)
        |   R -> failwith (sprintf "symbolic_execution_for_invariant_checking: there should be no such rule here: %s\n" (rule_to_string eng (get_rule eng R)))
    let state_header i = printf "\n=== state S_%d =====================================\n" i
    let rec F R_acc R_in i =
        reset_counters ()
        state_header i
        traverse i [] R_acc  (UM0, Map.empty, Set.empty)
        print_counters i ()
        if (match opt_steps with Some n -> i < n | None -> true)
        then let R_acc = s_eval_rule (SeqRule ([ R_acc; R_in; skipRule ])) eng (UM0, Map.empty, Set.empty)
             F R_acc R_in (i+1)
    F (S_Updates (s_update_set_empty eng)) (SeqRule ([ R_in; skipRule ])) 0
    printf "\n=================================================\n"
