module TopLevel

//--------------------------------------------------------------------

open Common
open Signature
open State
open AST
open SmtInterface

let trace = ref 0

//--------------------------------------------------------------------
// 'regular' initial environment (language used for ABZ 2024 paper)
let signature_0_default     = Background.signature
let initial_state_0_default = State.background_state
let rules_0_default         = Map.empty
let macros_0_default        = Map.empty

//--------------------------------------------------------------------
// AsmetaL initial environment
// Note: the AsmetaL signature mostly defined in imported files,
//   such as 'StandardLibrary.asm'

let signature_0_asmeta     = Background.signature
let initial_state_0_asmeta = State.background_state
let rules_0_asmeta         = Map.empty
let macros_0_asmeta        = Map.empty

//--------------------------------------------------------------------

let make_signature_0 asmeta_flag     = if not asmeta_flag then signature_0_default else signature_0_asmeta
let make_initial_state_0 asmeta_flag = if not asmeta_flag then initial_state_0_default else initial_state_0_asmeta
let make_rules_0 asmeta_flag         = if not asmeta_flag then rules_0_default else rules_0_asmeta
let make_macros_0 asmeta_flag        = if not asmeta_flag then macros_0_default else macros_0_asmeta
 
//--------------------------------------------------------------------

let signature_     : Signature.SIGNATURE option ref = ref None
let initial_state_ : State.STATE option ref = ref None
let rules_         : AST.RULES_DB option ref = ref None
let macros_        : AST.MACRO_DB option ref = ref None
let invariants_    : Map<string, TYPED_TERM> option ref = ref None

let initially     : Set<TYPED_TERM> ref = ref Set.empty     // conditions in initial state (specified by 'initially')

let smt_ctx       : SMT_CONTEXT = new_smt_context ()

//--------------------------------------------------------------------

let signature ()     = match !signature_     with Some s -> s | None -> failwith "signature not initialised"
let initial_state () = match !initial_state_ with Some s -> s | None -> failwith "initial state not initialised"    
let rules ()         = match !rules_         with Some r -> r | None -> failwith "rules not initialised"
let macros ()        = match !macros_        with Some m -> m | None -> failwith "macros not initialised"
let invariants ()    = match !invariants_    with Some i -> i | None -> failwith "invariants not initialised"

//--------------------------------------------------------------------

let init asmeta_flag =
    signature_     := make_signature_0 asmeta_flag |> Some
    initial_state_ := make_initial_state_0 asmeta_flag |> Some
    rules_         := make_rules_0 asmeta_flag |> Some
    macros_        := make_macros_0 asmeta_flag |> Some
    //smt_add_functions smt_ctx (Background.signature, State.background_state)

let reset asmeta_flag =
    init asmeta_flag
    smt_ctx_reset smt_ctx

//--------------------------------------------------------------------

let load (asmeta_flag : bool) (asmeta_initial_state : string option) initial_location contents =
    let parse_definitions (sign : SIGNATURE, S : STATE) s : SIGNATURE * STATE * RULES_DB * MACRO_DB * Map<string, TYPED_TERM> * (string * Map<string, STATE>) option =
        if not asmeta_flag
        then (fun (sign, S, rules_db) -> (sign, S, rules_db, Map.empty, Map.empty, None)) (Parser.parse_definitions initial_location (sign, S) s)
        else AsmetaL.parse_definitions initial_location ((sign, S), ((Map.empty : RULES_DB), (Map.empty : MACRO_DB))) s |> AsmetaL.extract_definitions_from_asmeta
    // note: exceptions are thrown if the environment (signature, initial state, rules) is not initialised (by 'Option.get')
    let (new_sign, new_state, new_rules_db, new_macro_db, invariants, initial_states) = parse_definitions (signature (), initial_state ()) contents
    signature_     := Some (signature_override (signature ()) new_sign)  //
    if not asmeta_flag
    then initial_state_ := Some (state_with_signature (state_override (initial_state ()) new_state) (signature ()))
    else match initial_states with
            |   None -> initial_state_ := Some (state_with_signature (state_override (initial_state ()) new_state) (signature ()))
            |   Some (default_init_name, initial_states_map) ->
                    let initial_state_name = asmeta_initial_state |> Option.defaultValue default_init_name
                    let initial_state_map = match initial_states with None -> Map.empty | Some (_, m) -> m
                    let selected_initial_state =
                        match Map.tryFind initial_state_name initial_state_map with
                        |   Some state -> state
                        |   None -> failwithf "No initial state with name '%s' has been defined (using AsmetaL \"init\").\nAvailable initial states: %s.\n"
                                        initial_state_name (Map.keys initial_state_map |> List.ofSeq >>| (fun s -> sprintf "'%s'" s) |> String.concat ", ")
                    let new_state_extended_with_selected_initial_state = state_override (state_override (initial_state ()) new_state) selected_initial_state
                    initial_state_ := Some (state_with_signature new_state_extended_with_selected_initial_state (signature ()))
    // note: the rules and macros are overridden, not merged
    rules_         := Some (rules_db_override (rules ()) new_rules_db)
    macros_        := Some (macro_db_override (macros ()) new_macro_db)
    invariants_    := Some invariants
    smt_add_types_and_functions smt_ctx (signature()) (new_sign, new_state)

let loadstr (asmeta_flag : bool) asmeta_initial_state contents =
    load asmeta_flag asmeta_initial_state (ParserCombinators.Strg (ref contents)) contents

let loadfile (asmeta_flag : bool) asmeta_initial_state filename =
    if (!trace > 0) then fprintf stderr "load_file: %s\n" filename
    Common.readfile (filename) |> load asmeta_flag asmeta_initial_state (ParserCombinators.File (ref filename))
    // fprintf stderr "invariants:\n%s\n"  (Map.fold (fun acc (inv_id : string) (t : TYPED_TERM) -> (acc ^ inv_id ^ ": " ^ (term_to_string (signature()) t))) "" (invariants ()))
    if (!trace > 0) then fprintf stderr "---\n%s\n---\n" (signature_to_string (signature ()))

//--------------------------------------------------------------------
