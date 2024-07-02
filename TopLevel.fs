module TopLevel

//--------------------------------------------------------------------

open Signature
open State
open AST
open SmtInterface

//--------------------------------------------------------------------

let signature_0     = Background.signature
let initial_state_0 = State.background_state
let rules_0         = Map.empty

let signature     : Signature.SIGNATURE ref = ref signature_0
let initial_state : State.STATE ref = ref initial_state_0
let rules         : AST.RULES_DB ref = ref rules_0
let initially     : Set<TERM> ref = ref Set.empty     // conditions in initial state (specified by 'initially')

let smt_ctx       : SMT_CONTEXT = new_smt_context ()

//--------------------------------------------------------------------

let reset () =
    signature     := signature_0
    initial_state := initial_state_0
    rules         := rules_0
    smt_ctx_reset smt_ctx
    //smt_add_functions smt_ctx (Background.signature, State.background_state)

//--------------------------------------------------------------------

let loadstr (asmeta_flag : bool) contents =
    let parse_definitions = if not asmeta_flag then Parser.parse_definitions else AsmetaL.parse_definitions
    let (new_sign, new_state, new_rules_db) = parse_definitions (!signature, !initial_state) contents
    signature     := signature_override !signature new_sign
    initial_state := state_with_signature (state_override (!initial_state) new_state) !signature
    rules         := rules_db_override !rules new_rules_db
    smt_add_functions smt_ctx (new_sign, new_state)

let loadfile (asmeta_flag : bool) filename = Common.readfile (filename) |> loadstr asmeta_flag

//--------------------------------------------------------------------
