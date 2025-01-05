module SymbState

open Common
open Signature
open AST
open Background

//--------------------------------------------------------------------

let trace = ref 0

//--------------------------------------------------------------------

type S_DYNAMIC_STATE = Map<string, Map<VALUE list, TYPED_TERM>>

type S_STATE = { _signature : SIGNATURE; _carrier_sets : State.CARRIER_SETS; _static : STATIC_STATE; _dynamic : S_DYNAMIC_STATE; _dynamic_initial : STATIC_STATE * MACRO_DB; }

let signature_of (S : S_STATE) : SIGNATURE =
    S._signature

let state_with_signature S sign = {
    _signature  = sign;
    _carrier_sets = S._carrier_sets;
    _static     = S._static;
    _dynamic    = S._dynamic;
    _dynamic_initial = S._dynamic_initial;
}

let state_to_s_state (S : State.STATE) : S_STATE = {
    _signature = S._signature;
    _carrier_sets = S._carrier_sets;
    _static    = S._static;
    _dynamic   = Map.map (fun f -> fun f_table -> Map.map (fun loc -> fun x -> mkValue (S._signature) x) f_table) S._dynamic;
    _dynamic_initial = S._dynamic_initial;
}

let state_to_s_state_only_static (S : State.STATE) : S_STATE = {
    _signature = S._signature;
    _carrier_sets = S._carrier_sets;
    _static    = S._static;
    _dynamic   = Map.empty;
    _dynamic_initial = (Map.empty, empty_macro_db);
}

let show_s_state (S : S_STATE) =
    let (sign, dS) = (signature_of S, S._dynamic)
    let show_function f =
        let show_loc_val_pair (xs, t) =
            sprintf "%s = %s"
                (if List.isEmpty xs then f else sprintf "%s (%s)" f (String.concat ", " (List.map value_to_string xs)))
                (PrettyPrinting.toString 80 (pp_term sign t))
        List.map show_loc_val_pair (Map.toList (Map.find f dS))
    let all_locations = List.concat (Seq.map show_function (Map.keys dS))
    "{ " + ( all_locations |> String.concat ", "   ) + " }"

//--------------------------------------------------------------------

let enum_finite_type (ty : TYPE) (S : S_STATE) =
    State.enum_finite_type ty {
        _signature = S._signature;
        _carrier_sets = S._carrier_sets;
        _static = Map.empty;
        _dynamic = Map.empty;
        _dynamic_initial = (Map.empty, empty_macro_db);
    }

//--------------------------------------------------------------------

let fct_name_has_interpretation (S : S_STATE) (f : string) =
    Map.containsKey f (S._static) || Map.containsKey f (S._dynamic)

let has_interpretation (S : S_STATE) (name : NAME) =
    match name with
    |   FctName f -> fct_name_has_interpretation S f
    |   _ -> true    // the interpretation of the various special constants always exists

//--------------------------------------------------------------------

let fct_name_interpretation (S : S_STATE) (f : string) (args : VALUE list) =
    let sign = signature_of S
    let Value = mkValue sign
    let kind =
        try fct_kind f (signature_of S)
        with _ -> failwith (sprintf "SymbState.fct_name_interpretation: function '%s' not defined in signature" f)
    if !trace > 0 then fprintfn stderr "SymbState.fct_name_interpretation: %s kind=%s" f (fct_kind_to_string kind)
    match kind with
    |   Constructor ->
            if !trace > 0 then fprintfn stderr "SymbState.fct_name_interpretation: constructor '%s'" f
            Value (CELL (f, args))
    |   Static -> 
            let f' = try Map.find f (S._static) with _ -> failwith (sprintf "SymbState.fct_name_interpretation: static function name '%s' has no interpretation" f)
            match f' args with 
            |   UNDEF -> failwith (sprintf "SymbState.fct_name_interpretation: static function '%s' not defined on (%s)" f (String.concat ", " (args >>| value_to_string)))
            |   x -> Value x 
    |   Controlled ->
        (   try Map.find args (Map.find f (S._dynamic))
            with _ ->
                try Value (Map.find f (fst S._dynamic_initial) args)
                with _ -> mkInitial sign (f, args)  )
    |   _ ->
        failwith (sprintf "SymbState.fct_name_interpretation: unsupported function kind '%s' for function name '%s'" (fct_kind_to_string kind) f)


let interpretation (S : S_STATE) (name : NAME) =
    match name with
    |   UndefConst -> (fun _ -> Value' (Undef, UNDEF))
    |   BoolConst b -> (fun _ -> Value' (Boolean, BOOL b))
    |   IntConst i -> (fun _ -> Value' (Integer, INT i))
    |   StringConst s -> (fun _ -> Value' (String, STRING s))
    |   FctName f -> (fun (args : VALUE list) -> (fct_name_interpretation S) f args)
  
//--------------------------------------------------------------------
