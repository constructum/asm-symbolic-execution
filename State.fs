module State

open Signature
open Background

//--------------------------------------------------------------------

type DYNAMIC_STATE = Map<string, Map<VALUE list, VALUE>>

type STATE = { _signature : SIGNATURE; _static : STATIC_STATE; _dynamic : DYNAMIC_STATE }

let signature_of (S : STATE) : SIGNATURE =
    S._signature

let state_with_signature S sign = {
    _signature  = sign;
    _static     = S._static;
    _dynamic    = S._dynamic;
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

let state_override_dynamic S0 f_table = {
    _signature  = S0._signature;
    _static     = S0._static;
    _dynamic    = Common.map_override S0._dynamic f_table;     
}

//--------------------------------------------------------------------

let fct_name_has_interpretation (S : STATE) (f : string) =
    Map.containsKey f (S._static) || Map.containsKey f (S._dynamic)

let has_interpretation (S : STATE) (name : NAME) =
    match name with
    |   FctName f -> fct_name_has_interpretation S f
    |   _ -> true    // the interpretation of the various special constants always exists

//--------------------------------------------------------------------
let fct_name_interpretation (S : STATE) (f : string) (args : VALUE list) =
    try
        let f_map = Map.find f (S._dynamic)
        try Map.find args f_map with _ -> UNDEF
    with _ ->
        try (Map.find f (S._static)) args
        with _ -> failwith (sprintf "function name '%s' has no interpretation" f)

let interpretation (S : STATE) (name : NAME) =
    match name with
    |   UndefConst -> (fun _ -> UNDEF)
    |   BoolConst b -> (fun _ -> BOOL b)
    |   IntConst i -> (fun _ -> INT i)
    |   StringConst s -> (fun _ -> STRING s)
    |   FctName f -> (fun (args : VALUE list) -> (fct_name_interpretation S) f args)
  
//--------------------------------------------------------------------
