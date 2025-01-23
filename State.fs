module State

open Common
open Signature
open Background
open AST

//--------------------------------------------------------------------

let trace = ref 0

//--------------------------------------------------------------------

type CARRIER_SETS = Map<string, VALUE Set option>       // list of all elements (only for types with finite cardinality)
type DYNAMIC_STATE = Map<string, Map<VALUE list, VALUE>>

type STATE = { _signature : SIGNATURE; _carrier_sets : CARRIER_SETS; _static : STATIC_STATE; _dynamic : DYNAMIC_STATE; _dynamic_initial : STATIC_STATE * MACRO_DB; }

let signature_of (S : STATE) : SIGNATURE =
    S._signature

let state_with_signature S sign = {
    _signature  = sign;
    _carrier_sets = S._carrier_sets;
    _static     = S._static;
    _dynamic    = S._dynamic;
    _dynamic_initial = S._dynamic_initial;
}

let background_state = {
    _signature = Background.signature;
    _carrier_sets = Background.carrier_sets;
    _static    = Background.state;
    _dynamic   = Map.empty;
    _dynamic_initial = (Map.empty, empty_macro_db);
}

let empty_state = {
    _signature  = Signature.empty_signature;
    _carrier_sets = Map.empty;
    _static     = Map.empty;
    _dynamic    = Map.empty;
    _dynamic_initial = (Map.empty, empty_macro_db);
}

let state_override S0 S' = {
    _signature  = Common.map_override (signature_of S0) (signature_of S');
    _carrier_sets = Common.map_override S0._carrier_sets S'._carrier_sets;
    _static     = Common.map_override S0._static  S'._static;
    _dynamic    = Common.map_override S0._dynamic S'._dynamic;     
    _dynamic_initial = (Common.map_override (fst S0._dynamic_initial) (fst S'._dynamic_initial), macro_db_override (snd S0._dynamic_initial) (snd S'._dynamic_initial));
}

let state_override_dynamic S0 f_table = {
    _signature  = S0._signature;
    _carrier_sets = S0._carrier_sets;
    _static     = S0._static;
    _dynamic    = Common.map_override S0._dynamic f_table;     
    _dynamic_initial = S0._dynamic_initial;
}

let state_override_dynamic_initial S0 f_def = {
    _signature  = S0._signature;
    _carrier_sets = S0._carrier_sets;
    _static     = S0._static;
    _dynamic    = S0._dynamic
    _dynamic_initial = (Common.map_override (fst S0._dynamic_initial) (fst f_def), macro_db_override (snd S0._dynamic_initial) (snd f_def));
}

let state_override_static S0 f_def = {
    _signature  = S0._signature;
    _carrier_sets = S0._carrier_sets;
    _static     = Common.map_override S0._static f_def;
    _dynamic    = S0._dynamic;
    _dynamic_initial = S0._dynamic_initial;
}

//--------------------------------------------------------------------

let extend_with_carrier_sets (sign : SIGNATURE, S : STATE) : STATE =
    let type_names =
        Signature.type_names sign
        |> Set.filter
            (fun tyname -> let k = type_kind tyname sign in (k = EnumType || k = SubsetType) && type_arity tyname sign = 0)
    let add_carrier_set_for_enum_type S tyname =
        let constructor_names =
            fct_names sign
            |>  Set.filter (fun f ->
                    fct_kind f sign = Constructor &&
                    match fct_type f sign with
                    |   ([], TypeCons (t, [])) -> t = tyname
                    |   _ -> failwith (sprintf "State.extend_with_carrier_set: not supported: constructor '%s' with arity > 0" f))
        if Set.count constructor_names = 0
        then    (if !trace > 0 then fprintf stderr "State.extend_with_carrier_set: skipping abstract type '%s', because it has no elements (%s = { })\n" tyname tyname)
                S
        else    (if !trace > 0 then fprintf stderr "State.extend_with_carrier_set: %s = { %s }\n" tyname (String.concat ", " constructor_names))
                { S with _carrier_sets = Map.add tyname (Some (Set.map (fun c -> CELL (c, [])) constructor_names)) S._carrier_sets }
    let add_carrier_set_for_subset_type S tyname =
        if !trace > 0 then fprintf stderr "State.extend_with_carrier_set: subset domain '%s'\n" tyname
        match Map.tryFind tyname (S._static) with
        |   Some f ->
                match f [] with
                |   SET elems -> { S with _carrier_sets = Map.add tyname (Some (Set elems)) S._carrier_sets }
                |   _ -> failwith (sprintf "State.extend_with_carrier_set: subset domain '%s' domain must be defined by specifying a finite set" tyname)
        |   None -> failwith (sprintf "State.extend_with_carrier_set: subset domain '%s' declared, but not defined" tyname)
    let add_carrier_set S tyname =
        let k = type_kind tyname sign
        if      k = EnumType   then add_carrier_set_for_enum_type S tyname
        else if k = SubsetType then add_carrier_set_for_subset_type S tyname
        else failwith (sprintf "State.extend_with_carrier_set: not supported: type '%s' with kind '%s'" tyname (type_kind_to_string k))
    Set.fold add_carrier_set S type_names


let boolean_carrier_set = Set.ofList [ BOOL true; BOOL false ];
let undef_carrier_set = Set.ofList [ UNDEF ];

let enum_finite_type (ty : TYPE) (S : STATE) =
    match ty with
    |   Boolean -> Some boolean_carrier_set
    |   Integer -> None
    |   String  -> None
    |   Undef   -> Some undef_carrier_set
    |   Rule    ->
            try Some (Option.get (Map.find "Rule" (S._carrier_sets)))
            with _ -> failwith "SymbState.enum_finite_type: carrier set of 'Rule' not found or not defined"  // not found: not in map; not defined: None
    |   TypeParam _ -> None
    |   TypeCons (tyname, []) ->
            try Some (Option.get (Map.find tyname (S._carrier_sets)))
            with _ -> failwith (sprintf "SymbState.enum_finite_type: carrier set of '%s' not found" tyname)
    |   Subset (tyname, _) ->
            try Some (Option.get (Map.find tyname (S._carrier_sets)))
            with _ -> failwith (sprintf "SymbState.enum_finite_type: carrier set of '%s' not found" tyname)
    |   TypeCons (tyname, _)  -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for user-defined type '%s' with type arity > 0" tyname)
    |   Prod _  -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for '%s'" (type_to_string ty))
    |   Seq _   -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for '%s'" (type_to_string ty))
    |   Powerset _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for '%s'" (type_to_string ty))
    |   Bag _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for '%s'" (type_to_string ty))
    |   Map _ -> failwith (sprintf "SymbState.enum_finite_type: not yet implemented for '%s'" (type_to_string ty))

//--------------------------------------------------------------------

let fct_name_has_interpretation (S : STATE) (f : string) =
    Map.containsKey f (S._static) || Map.containsKey f (S._dynamic)

let has_interpretation (S : STATE) (name : NAME) =
    match name with
    |   FctName f -> fct_name_has_interpretation S f
    |   _ -> true    // the interpretation of the various special constants always exists

//--------------------------------------------------------------------

let fct_name_interpretation (S : STATE) (f : string) (args : VALUE list) =
    let kind = fct_kind f (signature_of S)
    if !trace > 0 then fprintfn stderr "State.fct_name_interpretation: %s kind=%s" f (kind |> fct_kind_to_string)
    match kind with
    |   Constructor ->
            CELL (f, args)
    |   Static ->
            try (Map.find f (S._static)) args
            with _ -> failwith (sprintf "State.fct_name_interpretation: static function name '%s' has no interpretation" f)
    |   Controlled ->
            try Map.find args (Map.find f (S._dynamic))
            with _ ->
                try Map.find f (fst S._dynamic_initial) args
                with _ -> failwith (sprintf "State.fct_name_interpretation: dynamic function '%s' not defined on (%s)" f (String.concat ", " (args >>| value_to_string)))
    |   _ -> failwith (sprintf "State.fct_name_interpretation: function '%s' is not static nor controlled" f)

let interpretation (S : STATE) (name : NAME) =
    match name with
    |   UndefConst -> (fun _ -> UNDEF)
    |   BoolConst b -> (fun _ -> BOOL b)
    |   IntConst i -> (fun _ -> INT i)
    |   StringConst s -> (fun _ -> STRING s)
    |   FctName f -> (fun (args : VALUE list) -> (fct_name_interpretation S) f args)
  
//--------------------------------------------------------------------
