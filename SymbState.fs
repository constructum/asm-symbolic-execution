module SymbState

open Common
open Signature
open AST
open Background

//--------------------------------------------------------------------

type S_DYNAMIC_STATE = Map<string, Map<VALUE list, TERM>>

type S_STATE = { _signature : SIGNATURE; _static : STATIC_STATE; _dynamic : S_DYNAMIC_STATE }

let signature_of (S : S_STATE) : SIGNATURE =
    S._signature

let state_with_signature S sign = {
    _signature  = sign;
    _static     = S._static;
    _dynamic    = S._dynamic;
}

let state_to_s_state (S : State.STATE) : S_STATE = {
    _signature = S._signature;
    _static    = S._static;
    _dynamic   = Map.map (fun f -> fun f_table -> Map.map (fun loc -> fun x -> Value x) f_table) S._dynamic;
}

let state_to_s_state_only_static (S : State.STATE) : S_STATE = {
    _signature = S._signature;
    _static    = S._static;
    _dynamic   = Map.empty;
}

let background_state = {
    _signature = Background.signature;
    _static    = Background.state;
    _dynamic   = Map.empty;
}

let empty_state = {
    _signature  = Signature.empty_signature;
    _static     = Map.empty;
    _dynamic    = Map.empty;
}

let state_override S0 S' = {
    _signature  = Common.map_override (signature_of S0) (signature_of S');
    _static     = Common.map_override S0._static  S'._static;
    _dynamic    = Common.map_override S0._dynamic S'._dynamic;     
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

let fct_name_has_interpretation (S : S_STATE) (f : string) =
    Map.containsKey f (S._static) || Map.containsKey f (S._dynamic)

let has_interpretation (S : S_STATE) (name : NAME) =
    match name with
    |   FctName f -> fct_name_has_interpretation S f
    |   _ -> true    // the interpretation of the various special constants always exists

//--------------------------------------------------------------------
let fct_name_interpretation (S : S_STATE) (f : string) (args : VALUE list) =
    let kind = fct_kind f (signature_of S)
    match kind with
    |   Static -> 
        (   try
                match Map.find f (S._static) args with 
                |   UNDEF -> failwith (sprintf "static function '%s' not defined on (%s)" f (String.concat ", " (args >>| value_to_string)))
                |   x -> Value x
            with _ -> failwith (sprintf "static function name '%s' has no interpretation" f)    )
    |   Controlled ->
        (   try Map.find args (Map.find f (S._dynamic))
            with _ -> Initial (f, args)     )
    |   _ ->
        failwith (sprintf "unsupported function kind '%A' for function name '%s'" kind f)

let interpretation (S : S_STATE) (name : NAME) =
    match name with
    |   UndefConst -> (fun _ -> Value UNDEF)
    |   BoolConst b -> (fun _ -> Value (BOOL b))
    |   IntConst i -> (fun _ -> Value (INT i))
    |   StringConst s -> (fun _ -> Value (STRING s))
    |   FctName f -> (fun (args : VALUE list) -> (fct_name_interpretation S) f args)
  
//--------------------------------------------------------------------
