module SymbEval

//--------------------------------------------------------------------

open Common
open Background
open AST
open PrettyPrinting
open Signature
open SymbState
open SymbUpdates
open SmtInterface

//--------------------------------------------------------------------

let trace = ref 0
let level = ref 0
let rec spaces level = if level = 0 then "" else "    " + spaces (level-1)
let rec indent level ppt = if level = 0 then ppt else blo4 [ indent (level-1) ppt ]

//--------------------------------------------------------------------
// flags to control the simplification strategy

let simplify_cond = true
let use_smt_solver = ref true     // this only has an effect if 'simplify_cond' is true

//--------------------------------------------------------------------

type ENV = Map<string, TERM>

type CONTEXT = Set<TERM>    // boolean formulas (facts) that are true in current branch of conditional rule

//--------------------------------------------------------------------

let empty : ENV =
    Map.empty

let defined_in (env : ENV) var =
    Map.containsKey var env

let get_env (env : ENV) (var : string) =
    Map.find var env

let add_binding (env : ENV) (var : string, t : TERM) =
    Map.add var t env

//--------------------------------------------------------------------

let get_values (ts : TERM list) : VALUE list option =    // only if all arguments are values
    List.fold ( function
                |   Some ts -> (function Value v -> Some(v :: ts) | _ -> None)
                |   None -> (fun _ -> None) ) (Some []) (List.rev ts)

//--------------------------------------------------------------------
// rewrite rules for boolean terms

let s_equals = function
|   (Value x1, Value x2) -> Value ((Map.find "=" Background.state) [ x1; x2 ])
|   (t1, t2) -> if t1 = t2 then Value (BOOL true) else AppTerm (FctName "=", [t1; t2])

let s_not = function
|   Value (BOOL b) -> Value (BOOL (not b))
//|   AppTerm (FctName "not", [phi']) -> phi'
|   phi -> AppTerm (FctName "not", [phi])

let s_and = function
|   (Value (BOOL false), _) -> Value (BOOL false)
|   (Value (BOOL true), phi2) -> phi2
|   (_, Value (BOOL false)) -> Value (BOOL false)
|   (phi1, Value (BOOL true)) -> phi1
|   (phi1, phi2) -> if phi1 = phi2 then phi1 else AppTerm (FctName "and", [phi1; phi2])

let s_or = function
|   (Value (BOOL false), phi2) -> phi2
|   (Value (BOOL true), _) -> Value (BOOL true)
|   (phi1, Value (BOOL false)) -> phi1
|   (_, Value (BOOL true)) -> Value (BOOL true)
|   (phi1, phi2) -> if phi1 = phi2 then phi1 else AppTerm (FctName "or", [phi1; phi2])

let s_xor = function
|   (Value (BOOL false), phi2) -> phi2
|   (Value (BOOL true), phi2) -> s_not phi2
|   (phi1, Value (BOOL false)) -> phi1
|   (phi1, Value (BOOL true)) -> s_not phi1
|   (phi1, phi2) -> if phi1 = phi2 then Value (BOOL false) else AppTerm (FctName "xor", [phi1; phi2])

let s_implies = function
|   (Value (BOOL b1), phi2) -> s_or (Value (BOOL (not b1)), phi2)
|   (phi1, Value (BOOL b2)) -> s_or (s_not phi1, Value (BOOL b2))
|   (phi1, phi2) -> if phi1 = phi2 then Value (BOOL true) else AppTerm (FctName "implies", [phi1; phi2])

let s_iff = function
|   (Value (BOOL false), phi2) -> s_not phi2
|   (Value (BOOL true), phi2) -> phi2
|   (phi1, Value (BOOL false)) -> s_not phi1
|   (phi1, Value (BOOL true)) -> phi1
|   (phi1, phi2) -> if phi1 = phi2 then Value (BOOL true) else AppTerm (FctName "iff", [phi1; phi2])

//--------------------------------------------------------------------
// simplify terms by applying rewrite rules above

let apply_rewrite_rules = function
    |   ("=", [t1; t2])     -> s_equals (t1, t2)
    |   ("not", [t])        -> s_not (t)
    |   ("and", [t1; t2])   -> s_and (t1, t2)
    |   ("or", [t1; t2])    -> s_or (t1, t2)
    |   ("xor", [t1; t2])   -> s_xor (t1, t2)
    |   ("implies", [t1; t2]) -> s_implies (t1, t2)
    |   ("iff", [t1; t2])   -> s_iff (t1, t2)
    |   (f, ts)             -> AppTerm (FctName f, ts)

//--------------------------------------------------------------------

let ctx_condition C =
    List.fold (fun a -> fun b -> s_and (a, b)) (Value (BOOL true)) (Set.toList C)

let smt_assert_update (S, env, C) ((f, xs), t) =
    smt_assert (signature_of S) TopLevel.smt_ctx (s_equals (AppTerm (FctName f, xs >>| Value), t))

let ctx_to_smt (S, env, C)=
    // !!!! tbd: if there is any initialisation in S0, it should be mapped as well: for the moment there is none
    // !!!! List.map (fun ((f, xs), t) -> smt_assert_update (S, env, C) (f, xs), t) (Map.toList C.U) |> ignore
    Set.map (fun phi -> smt_assert (signature_of S) TopLevel.smt_ctx phi) C |> ignore

let smt_eval_formula (phi : TERM) (S, env, C) =
    // precondition: term_type (signature_of S) phi = Boolean
    // old version before using solver push and pop: // ctx_to_smt (S, env, C)
    let result =
        if (!use_smt_solver && smt_formula_is_true (signature_of S) TopLevel.smt_ctx phi)
        then Value (BOOL true)
        else if (!use_smt_solver && smt_formula_is_true (signature_of S) TopLevel.smt_ctx (s_not phi))
        then Value (BOOL false)
        else phi
    // old version before using solver push and pop: // smt_solver_reset TopLevel.smt_ctx
    result

//--------------------------------------------------------------------

// this returns the type of an already type-checked term (i.e. it assumes that the term is type-correct)
let term_type sign =
    term_induction (fun x -> x) {
        Value = function
                |   UNDEF   -> Undef
                |   BOOL _  -> Boolean
                |   INT _   -> Integer
                |   STRING _ -> String;
        Initial  = fun (f, ts) -> let (_, T_ran) = fct_type f sign in T_ran;
        AppTerm = function
                    |   (UndefConst, _)    -> Undef
                    |   (IntConst _, _)    -> Integer
                    |   (BoolConst _, _)   -> Boolean
                    |   (StringConst _, _) -> String
                    |   (FctName f, ts)    -> let (_, T_ran) = fct_type f sign in T_ran;
        CondTerm = function (G, t1, t2) -> t1;
    }

//---------------------------------------------------

let eval_app_term (S : S_STATE, env : ENV, C : CONTEXT) (fct_name : NAME, ts) = 
    let ts = ts >>| fun t -> t (S, env, C)
    match get_values ts with
    |   Some xs -> interpretation S fct_name xs
    |   None ->
            let f = match fct_name with FctName f -> f | _ -> failwith "special constant not expected"
            if fct_kind f (signature_of S) = Static
            then let t = apply_rewrite_rules (f, ts)
                 match t with
                 | Value (BOOL _) -> t
                 | _ ->
                    let (_, T_ran) = fct_type f (signature_of S)
                    if T_ran = Boolean
                    then if Set.contains t C
                            then Value (BOOL true)
                            else if Set.contains (s_not t) C
                            then Value (BOOL false)
                            else t
                    else t
                    (* if there is nothing to simplify by rewriting or using context, it would return AppTerm (FctName f, ts) *)
            else failwith (sprintf "arguments of dynamic function '%s' must be fully evaluable for unambiguous determination of a location\n(term '%s' found instead)"
                                        f (term_to_string (signature_of S) (AppTerm (FctName f, ts))))

let eval_cond_term (S : S_STATE, env : ENV, C : CONTEXT) (G, t1, t2) = 
    let term_to_string = term_to_string (signature_of S)
    match G (S, env, C) with
    |   Value (BOOL true)  -> t1 (S, env, C)
    |   Value (BOOL false) -> t2 (S, env, C)
    |   G ->    if (!trace > 1)
                then fprintfn stderr "\n%sctx_condition: %s" (spaces !level) (term_to_string (ctx_condition C))
                if not simplify_cond then
                    // version 1: no simplification whatsoever (inefficient, but useful for debugging)
                    CondTerm (G, t1 (S, env, Set.add G C), t2 (S, env, Set.add (s_not G) C))
                else 
                    // version 2: with simplification
                    if Set.contains G C
                    then t1 (S, env, C)
                    else if Set.contains (s_not G) C
                    then t2 (S, env, C)
                    else
                        let (t1', t2') = (t1 (S, env, Set.add G C), t2 (S, env, Set.add (s_not G) C))
                        if t1' = t2' then t1' else CondTerm (G, t1', t2')

let s_eval_term_ t : S_STATE * ENV * CONTEXT-> TERM =
    term_induction (fun x -> x) {
        Value    = fun x _ -> Value x;
        Initial  = fun (f, xs)  _ -> Initial (f, xs);
        AppTerm  = fun (f, ts) -> fun (S, env, C) -> eval_app_term (S, env, C) (f, ts);
        CondTerm = fun (G, t1, t2) -> fun (S, env, C) -> eval_cond_term (S, env, C) (G, t1, t2);
        // VarTerm = fun v -> fun (S, env) -> get_env env v;
        // LetTerm = fun (v, t1, t2) -> fun (S, env) -> t2 (S, add_binding env (v, t1 (S, env)))
    } t

let s_eval_term (t : TERM) (S : S_STATE, env : ENV, C : CONTEXT) : TERM =
    let sign = signature_of S
    if term_type sign t = Boolean
    then
        let t = s_eval_term_ t (S, env, C)
        match t with
        |   Value (BOOL _)  -> t
        |   _ -> smt_eval_formula t (S, env, C)
    else s_eval_term_ t (S, env, C)

//--------------------------------------------------------------------

let rec s_eval_rule (R : RULE) (S : S_STATE, env : ENV, C : CONTEXT) : RULE =
    let (rule_to_string, term_to_string, pp_rule) =
         (rule_to_string (signature_of S), term_to_string (signature_of S), pp_rule (signature_of S))

    if (!trace > 1)
    then fprintf stderr "%s----------------------\n%ss_eval_rule %s\n%s\n\n"
            (spaces !level) (spaces !level) (show_s_state S) (toString 80 (indent (!level) (pp_rule R)))
    level := !level + 1

    let eval_update ((f, ts), t_rhs) (S, env, C) =
        match get_values (ts >>| fun t -> s_eval_term t (S, env, C)) with
        |   Some xs -> S_Updates (Set.singleton ((f, xs), s_eval_term t_rhs (S, env, C)));
        |   None -> failwith (sprintf "location %A on the lhs of update cannot be fully evaluated" (f, ts))

    let eval_cond (G, R1, R2) (S, env, C) = 
        match s_eval_term G (S, env, C) with
        |   Value (BOOL true)  -> s_eval_rule R1 (S, env, C)
        |   Value (BOOL false) -> s_eval_rule R2 (S, env, C)
        |   G ->    //let (R1', R2') = (s_eval_rule R1 (S, env, Set.add G C), s_eval_rule R2 (S, env, Set.add (s_not G) C))
                    let sign = signature_of S
                    smt_solver_push TopLevel.smt_ctx
                    smt_assert sign TopLevel.smt_ctx G
                    let R1' = s_eval_rule R1 (S, env, Set.add G C)
                    smt_solver_pop TopLevel.smt_ctx
                    smt_solver_push TopLevel.smt_ctx
                    smt_assert sign TopLevel.smt_ctx (s_not G)
                    let R2' = s_eval_rule R2 (S, env, Set.add (s_not G) C)
                    smt_solver_pop TopLevel.smt_ctx
                    if R1' = R2' then R1' else CondRule (G, R1', R2')

    let rec eval_par Rs (S, env, C) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> s_eval_rule R1 (S, env, C)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_par R1 R2 (S, env, C)) R1 Rs

    and eval_binary_par R1 R2 (S, env, C) : RULE =
        match s_eval_rule R1 (S, env, C) with
        |   S_Updates U1 ->
            (   match s_eval_rule R2 (S, env, C) with
                |   S_Updates U2 ->
                        S_Updates (Set.union U1 U2)
                |   CondRule (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, ParRule [ S_Updates U1; R21 ], ParRule [ S_Updates U1; R22 ])) (S, env, C)
                |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R2)) )
        |   CondRule (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, ParRule [ R11; R2 ], ParRule [ R12; R2 ])) (S, env, C)
        |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R1))

    and eval_seq Rs (S, env, C) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> s_eval_rule R1 (S, env, C)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_seq R1 R2 (S, env, C)) R1 Rs

    and eval_binary_seq R1 R2 (S, env, C): RULE = 
        match s_eval_rule R1 (S, env, C) with
        |   S_Updates U1 ->
            (   let S' = sequel_s_state S U1
                match s_eval_rule R2 (S', env, C) with
                |   S_Updates U2 ->
                        S_Updates (seq_merge_2 U1 U2)
                |   CondRule (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, SeqRule [ S_Updates U1; R21 ], SeqRule [ S_Updates U1; R22 ])) (S, env, C)
                |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R2)) )
        |   CondRule (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, SeqRule [ R11; R2 ], SeqRule [ R12; R2 ])) (S, env, C)
        |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R1))

    and eval_iter R (S, env, C) =
        match s_eval_rule R (S, env, C) with
        |   S_Updates U ->
                if Set.isEmpty U
                then S_Updates Set.empty
                else s_eval_rule (SeqRule [ S_Updates U; IterRule R ]) (S, env, C)
        |   (CondRule (G, R1, R2)) ->
                //s_eval_rule (SeqRule [ CondRule (G, R1, R2); IterRule R ]) (S, env, C)
                s_eval_rule (CondRule (G, SeqRule [R1; IterRule R], SeqRule [R2; IterRule R])) (S, env, C)
        |   R' -> failwith (sprintf "SymEvalRules.s_eval_rule: eval_iter_rule - R'' = %s" (rule_to_string R'))

    let R =
        match R with
        |   UpdateRule ((f, ts), t) -> eval_update ((f, ts), t) (S, env, C)
        |   CondRule (G, R1, R2)    -> eval_cond (G, R1, R2) (S, env, C)
        |   ParRule Rs              -> eval_par Rs (S, env, C)
        |   SeqRule Rs              -> eval_seq Rs (S, env, C)
        |   IterRule R              -> eval_iter R (S, env, C)
        |   S_Updates S             -> S_Updates S

    level := !level - 1
    if (!trace > 1)
    then fprintf stderr "%ss_eval_rule result = \n%s\n%s----------------------\n" (spaces !level) (toString 120 (indent (!level) (pp_rule R))) (spaces !level)

    R

//--------------------------------------------------------------------
// convert partially evaluated terms and rules to regular ones

let reconvert_value x =
    let special_const =
        match x with
        |   UNDEF   -> UndefConst
        |   BOOL b  -> BoolConst b
        |   INT i   -> IntConst i
        |   STRING s -> StringConst s
    AppTerm (special_const, [])

let reconvert_term t =
    term_induction (fun x -> x) {
        Value    = fun x -> reconvert_value x;
        Initial  = fun (f, xs) -> AppTerm (FctName f, xs >>| Value);
        AppTerm  = AppTerm;
        CondTerm = CondTerm;
    } t

let reconvert_rule R = 
    rule_induction reconvert_term {
        UpdateRule = UpdateRule;
        CondRule   = CondRule;
        ParRule    = ParRule;
        SeqRule    = SeqRule;
        IterRule   = IterRule;
        S_Updates  = fun upds -> ParRule (List.map (fun ((f, xs), t_rhs) -> UpdateRule ((f, xs >>| Value), reconvert_term t_rhs)) (Set.toList upds))
    } R

//--------------------------------------------------------------------

let count_s_updates = rule_induction (fun _ -> ()) {
    UpdateRule = fun _ -> failwith "there should be no UpdateRule here";
    CondRule  = fun (_, R1, R2) -> R1 + R2;
    ParRule   = fun _ -> failwith "there should be no ParRule here";
    SeqRule   = fun _ -> failwith "there should be no SeqRule here";
    IterRule  = fun _ -> failwith "there should be no IterRule here";
    S_Updates = fun _ -> 1;   // not relevant, but define somehow to allow printing for debugging
}

//--------------------------------------------------------------------

// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution (R_in : RULE) : int * RULE =
    let S0 = !TopLevel.initial_state
    let R_out = s_eval_rule R_in (state_to_s_state S0, Map.empty, Set.empty)
    (count_s_updates R_out, reconvert_rule R_out)

//--------------------------------------------------------------------
// this version sets all non-static functions to be uninterpreted,
//   as needed for translation turbo ASM-> basic ASM (see paper
//   https://github.com/constructum/asm-symbolic-execution/blob/main/doc/2024--Del-Castillo--extended-version-of-ABZ-2024-paper--Using-Symbolic-Execution-to-Transform-Turbo-ASM-into-Basic-ASM.pdf
//   - section 4)
//
// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution_for_turbo_asm_to_basic_asm_transformation (R_in : RULE) : int * RULE =
    let S0 = !TopLevel.initial_state
    let R_out = s_eval_rule R_in (state_to_s_state_only_static S0, Map.empty, Set.empty)
    (count_s_updates R_out, reconvert_rule R_out)
