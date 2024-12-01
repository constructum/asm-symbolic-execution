module State

open Common
open Signature
open Background

//--------------------------------------------------------------------

type DYNAMIC_STATE = Map<string, Map<VALUE list, VALUE>>

type STATE = { _signature : SIGNATURE; _static : STATIC_STATE; _dynamic : DYNAMIC_STATE; _dynamic_initial : STATIC_STATE; }

let signature_of (S : STATE) : SIGNATURE =
    S._signature

let state_with_signature S sign = {
    _signature  = sign;
    _static     = S._static;
    _dynamic    = S._dynamic;
    _dynamic_initial = S._dynamic_initial;
}

let background_state = {
    _signature = Background.signature;
    _static    = Background.state;
    _dynamic   = Map.empty;
    _dynamic_initial = Map.empty;
}

let empty_state = {
    _signature  = Signature.empty_signature;
    _static     = Map.empty;
    _dynamic    = Map.empty;
    _dynamic_initial = Map.empty;
}

let state_override S0 S' = {
    _signature  = Common.map_override (signature_of S0) (signature_of S');
    _static     = Common.map_override S0._static  S'._static;
    _dynamic    = Common.map_override S0._dynamic S'._dynamic;     
    _dynamic_initial = Common.map_override S0._dynamic_initial S'._dynamic_initial;
}

let state_override_dynamic S0 f_table = {
    _signature  = S0._signature;
    _static     = S0._static;
    _dynamic    = Common.map_override S0._dynamic f_table;     
    _dynamic_initial = S0._dynamic_initial;
}

let state_override_dynamic_initial S0 f_def = {
    _signature  = S0._signature;
    _static     = S0._static;
    _dynamic    = S0._dynamic
    _dynamic_initial = Common.map_override S0._dynamic_initial f_def;
}

let state_override_static S0 f_def = {
    _signature  = S0._signature;
    _static     = Common.map_override S0._static f_def;
    _dynamic    = S0._dynamic;
    _dynamic_initial = S0._dynamic_initial;
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
    match fct_kind f S._signature with
    |   Static ->
            try (Map.find f (S._static)) args
            with _ -> failwith (sprintf "static function name '%s' has no interpretation" f)
    |   Controlled ->
            let f_map = Map.find f (S._dynamic)
            try Map.find args f_map
            with _ ->
                try Map.find f (S._dynamic_initial) args
                with _ -> failwith (sprintf "dynamic function '%s' not defined on (%s)" f (String.concat ", " (args >>| value_to_string)))
    |   _ -> failwith (sprintf "fct_name_interpretation: function '%s' is not static nor controlled" f)

let interpretation (S : STATE) (name : NAME) =
    match name with
    |   UndefConst -> (fun _ -> UNDEF)
    |   BoolConst b -> (fun _ -> BOOL b)
    |   IntConst i -> (fun _ -> INT i)
    |   StringConst s -> (fun _ -> STRING s)
    |   FctName f -> (fun (args : VALUE list) -> (fct_name_interpretation S) f args)
  
//--------------------------------------------------------------------
