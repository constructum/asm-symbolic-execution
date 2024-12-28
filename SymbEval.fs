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

type ENV = Map<string, TERM * TYPE>

type CONTEXT = Set<TERM>    // boolean formulas (facts) that are true in current branch of conditional rule

//--------------------------------------------------------------------

let empty : ENV =
    Map.empty

let defined_in (env : ENV) var =
    Map.containsKey var env

let get_env (env : ENV) (var : string) =
    Map.find var env

let add_binding (env : ENV) (var : string, t : TERM, ty : TYPE) =
    Map.add var (t, ty) env

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

//--------------------------------------------------------------------

// this returns the type of an already type-checked term (i.e. it assumes that the term is type-correct)
let term_type sign (env : ENV) =
    term_induction (fun x -> x) {
        Value = Background.type_of_value sign;
        Initial  = fun (f, ts) -> let (_, T_ran) = fct_type f sign in T_ran;
                        // !!! (1) not very efficient due to unnecessarily calling fct_type every time - note: term is already been type checked!
                        // !!! (2) does not work for overloaded functions
        AppTerm = function
                    |   (UndefConst, _)    -> Undef
                    |   (IntConst _, _)    -> Integer
                    |   (BoolConst _, _)   -> Boolean
                    |   (StringConst _, _) -> String
                    |   (FctName f, ts)    -> let (_, T_ran) = fct_type f sign in T_ran;
                            // !!! (1) not very efficient due to unnecessarily calling fct_type every time - note: term is already been type checked!
                            // !!! (2) does not work for overloaded functions
        CondTerm = function (G, t1, t2) -> t1;
        VarTerm  = fun v -> get_env env v |> snd;
        LetTerm  = fun _ -> failwith "term_type: LetTerm not implemented yet";
        DomainTerm = fun ty -> Powerset ty
    }

//---------------------------------------------------

let rec smt_eval_formula (phi : TERM) (S, env, C) =
    // precondition: term_type (signature_of S) phi = Boolean
    // old version before using solver push and pop: // ctx_to_smt (S, env, C)
    if !trace > 0 then fprintf stderr "smt_eval_formula(%s) -> " (term_to_string (signature_of S) phi)
    let phi = expand_term phi (S, env, C)
    let result =
        if (!use_smt_solver && smt_formula_is_true (signature_of S) TopLevel.smt_ctx phi)
        then Value (BOOL true)
        else if (!use_smt_solver && smt_formula_is_true (signature_of S) TopLevel.smt_ctx (s_not phi))
        then Value (BOOL false)
        else phi
    // old version before using solver push and pop: // smt_solver_reset TopLevel.smt_ctx
    if !trace > 0 then fprintf stderr "%s\n" (term_to_string (signature_of S) result)
    result

and expand_term t (S, env, C) =
    term_induction (fun x -> x) {
        Value = fun x -> fun (S, env, C) -> Value x;
        Initial = fun (f, xs) -> fun (S, env, C) -> Initial (f, xs);
        AppTerm = fun (f, ts) -> fun (S, env, C) ->
            let sign = signature_of S
            match f with
            |   FctName fct_name ->
                    // static functions that are not primitive functions (i.e. not in the 'background') are expanded like macros
                    if fct_kind fct_name sign = Static && not (Map.containsKey fct_name Background.state) then
                        let (formals, body) =
                            try Map.find fct_name (TopLevel.macros ())     // !!! should not use global TopLevel.macros
                            with _ -> failwith (sprintf "SymbEval.expand_term: definition of static function '%s' not found in macros database" fct_name)
                        let ts = ts >>| fun t -> t (S, env, C)
                        let env' =
                            List.fold2 (fun env' formal arg -> add_binding env' (formal, s_eval_term arg (S, env, C), term_type (signature_of S) env arg)) env formals ts
                        s_eval_term body (S, env', C)
                    else AppTerm (f, ts >>| fun t -> t (S, env, C))
            |   _ -> AppTerm (f, ts >>| fun t -> t (S, env, C));
        CondTerm = fun (G, t1, t2) -> fun (S, env, C) -> CondTerm (G (S, env, C), t1 (S, env, C), t2 (S, env, C));
        VarTerm = fun v -> fun (S, env, C) -> VarTerm v;
        LetTerm = fun (v, t1, t2) -> fun (S, env, C) ->
                    let t1_val = t1 (S, env, C)
                    t2 (S, add_binding env (v, t1_val, term_type (signature_of S) env t1_val), C);
        DomainTerm = fun ty -> fun (S, env, C) -> match enum_finite_type ty S with Some xs -> Value (SET xs) | _ -> failwith (sprintf "SymbEval.expand_term: domain of type '%s' is not enumerable" (ty |> type_to_string))
    } t (S, env, C)

and try_reducing_term_with_finite_range (S : S_STATE, env : ENV, C : CONTEXT) (t : TERM) : TERM =
    let opt_elems = try enum_finite_type (term_type (signature_of S) env t) S with _ -> None
    match t with
    |   Initial _ ->
        match opt_elems with
        |   None -> t
        |   Some elems ->
                let folder result elem =
                    match result with
                    |   Some _ -> result
                    |   None -> if smt_eval_formula (AppTerm (FctName "=", [t; Value elem])) (S, env, C) = Value TRUE then Some elem else None
                let opt_elem = Set.fold folder None elems
                match opt_elem with
                |   None -> t
                |   Some x -> Value x
    |   _ -> t

and try_case_distinction_for_term_with_finite_range (S : S_STATE, env : ENV, C : CONTEXT) (f : FCT_NAME) (ts0 : TERM list) : TERM =
    let make_case_distinction (t : TERM) (elem_term_pairs : (VALUE * TERM) list) =
        if List.isEmpty elem_term_pairs
        then failwith (sprintf "SymbEval.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string (signature_of S) t))
        let (elem_term_pairs_without_last, last_elem_term_pair) = List.splitAt (List.length elem_term_pairs - 1) elem_term_pairs
        Parser.switch_to_cond_term (t, List.map (fun (elem, term) -> (Value elem, term)) elem_term_pairs_without_last, snd (List.head (last_elem_term_pair)))
    let rec F past_args = function
    |   [] -> AppTerm (FctName f, List.rev past_args)
    |   t1 :: ts' ->
            let t1 = s_eval_term t1 (S, env, C)
            match t1 with
            |   Value x1 -> F (Value x1 :: past_args) ts'
            |   t1 ->
                    match (try enum_finite_type (term_type (signature_of S) env t1) S with _ -> None) with
                    |   None ->
                            failwith (sprintf "arguments of dynamic function '%s' must be fully evaluable for unambiguous determination of a location\n('%s' found instead)"
                                        f (term_to_string (signature_of S) (AppTerm (FctName f, ts0))))
                    |   Some elems ->
                            let case_dist = make_case_distinction t1 (List.map (fun elem -> (elem, F (Value elem :: past_args) ts')) (Set.toList elems))
                            s_eval_term_ case_dist (S, env, C)    // simplify generated conditional term
    let result = F [] ts0
    result

and eval_app_term (S : S_STATE, env : ENV, C : CONTEXT) (fct_name, ts) = 
    //if !trace > 0 then fprintfn stderr "|signature|=%d | eval_app_term %s%s\n" (Map.count (signature_of S)) (spaces !level) (term_to_string (signature_of S) (AppTerm (fct_name, [])))
    let ts = ts >>| fun t -> t (S, env, C)
    let rec F ts_past = function
        |   (t as Value x1 :: ts_fut)            -> F (t :: ts_past) ts_fut
        |   (t as Initial (f, xs) :: ts_fut)     -> F (t :: ts_past) ts_fut
        |   (CondTerm (G1, t11, t12) :: ts_fut)  -> s_eval_term_ (CondTerm (G1, F ts_past (t11 :: ts_fut), F ts_past (t12 :: ts_fut))) (S, env, C)
        |   (t1 as QuantTerm :: ts_fut)          -> failwith "SymbEval.eval_app_term: QuantTerm not implemented"
        |   (t as LetTerm (v, t1, t2) :: ts_fut) -> F (t :: ts_past) ts_fut
        |   (t as VarTerm v :: ts_fut)           -> F (t :: ts_past) ts_fut
        |   (t as AppTerm (_, _) :: ts_fut)      -> F (t :: ts_past) ts_fut
        |   (t as DomainTerm _ :: ts_fut)        -> failwith "SymbEval.eval_app_term: DomainTerm not implemented"
        |   [] ->
                match (fct_name, ts) with
                |   (FctName f, ts)    ->
                    match get_values ts with
                    |   Some xs -> interpretation S fct_name xs
                    |   None ->
                        match (fct_kind f (signature_of S)) with
                        |   Static ->
                                match fct_type f (signature_of S) with
                                |   (_, Boolean) ->
                                        let t = apply_rewrite_rules (f, ts)
                                        if      t = Value (BOOL true)       then t
                                        else if t = Value (BOOL false)      then t
                                        else if Set.contains t C            then Value (BOOL true)
                                        else if Set.contains (s_not t) C    then Value (BOOL false)
                                        else smt_eval_formula t (S, env, C)
                                |   (_, _) -> AppTerm (FctName f, ts)    // nothing left to simplify
                        |   Controlled ->
                                try_case_distinction_for_term_with_finite_range (S, env, C) f ts
                        |   other_kind -> failwith (sprintf "SymbEval.eval_app_term: kind '%s' of function '%s' not implemented" (fct_kind_to_string other_kind) f)
                |   (UndefConst, _)    -> Value UNDEF
                |   (BoolConst b, _)   -> Value (BOOL b)
                |   (IntConst i, _)    -> Value (INT i)
                |   (StringConst s, _) -> Value (STRING s)
    F [] ts

and eval_cond_term (S : S_STATE, env : ENV, C : CONTEXT) (G, t1, t2) = 
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

and eval_let_term (S, env, C) (v, t1, t2) =
    let t1 = t1 (S, env, C)
    t2 (S, add_binding env (v, t1, term_type (signature_of S) env t1), C)       // !!!!! is this one correct at all?

and s_eval_term_ t ((S, env, C) : S_STATE * ENV * CONTEXT) =
    //  if !trace > 0 then fprintfn stderr "|signature|=%d | s_eval_term %s%s\n" (Map.count (signature_of S)) (spaces !level) (term_to_string (signature_of S) t)
    //let t = try_reducing_term_with_finite_domain (S, env, C) t
    term_induction (fun x -> x) {
        Value    = fun x _ -> Value x;
        Initial  = fun (f, xs)  _ -> Initial (f, xs); //Initial (f, xs);
        AppTerm  = fun (f, ts) -> fun (S, env, C) -> try_reducing_term_with_finite_range (S, env, C) (eval_app_term (S, env, C) (f, ts));
        CondTerm = fun (G, t1, t2) -> fun (S, env, C) -> eval_cond_term (S, env, C) (G, t1, t2);
        VarTerm  = fun v -> fun (S, env, _) -> fst (get_env env v);
        LetTerm  = fun (v, t1, t2) -> fun (S, env, _) -> eval_let_term (S, env, C) (v, t1, t2) //failwith "s_eval_term: LetTerm: not implemented yet";
        DomainTerm = fun ty -> fun (S, env, C) -> match enum_finite_type ty S with Some xs -> Value (SET xs) | None -> failwith (sprintf "SymbEval.expand_term: domain of type '%s' is not enumerable" (ty |> type_to_string))
    } t (S, env, C)

and s_eval_term (t : TERM) (S : S_STATE, env : ENV, C : CONTEXT) : TERM =
    let sign = signature_of S
    let t = s_eval_term_ t (S, env, C)
    if term_type sign env t = Boolean
    then    match t with
            |   Value (BOOL _)  -> t
            |   _ -> smt_eval_formula t (S, env, C)
    else    match t with
            |   Initial (f, xs) -> try_reducing_term_with_finite_range (S, env, C) t
            |   _ -> t

//--------------------------------------------------------------------

let rec try_case_distinction_for_update_with_finite_domain (S : S_STATE, env : ENV, C : CONTEXT) (f : FCT_NAME) (ts0 : TERM list) (t_rhs : TERM): RULE =
    let make_case_distinction (t : TERM) (elem_term_pairs : (VALUE * RULE) list) =
        if List.isEmpty elem_term_pairs
        then failwith (sprintf "SymbEval.try_case_distinction_for_update_with_finite_domain: empty range for term %s" (term_to_string (signature_of S) t))
        let (elem_term_pairs_without_last, last_elem_term_pair) = List.splitAt (List.length elem_term_pairs - 1) elem_term_pairs
        Parser.switch_to_cond_rule (t, List.map (fun (elem, term) -> (Value elem, term)) elem_term_pairs_without_last, snd (List.head (last_elem_term_pair)))
    let rec F past_args = function
        |   [] -> UpdateRule ((f, List.rev past_args), t_rhs)
        |   t1 :: ts' ->
            let t1 = s_eval_term t1 (S, env, C)
            match t1 with
            |   Value x1 -> F (Value x1 :: past_args) ts'
            |   t1 ->
                    match (try enum_finite_type (term_type (signature_of S) env t1) S with _ -> None) with
                    |   None ->
                            failwith (sprintf "location (%s, (%s)) on the lhs of update cannot be fully evaluated"
                                        f (String.concat ", " (ts0 >>| term_to_string (signature_of S))))
                    |   Some elems ->
                            let case_dist = make_case_distinction t1 (List.map (fun elem -> (elem, F (Value elem :: past_args) ts')) (Set.toList elems))
                            s_eval_rule case_dist (S, env, C)    // simplify generated conditional rule
    F [] ts0

and s_eval_rule (R : RULE) (S : S_STATE, env : ENV, C : CONTEXT) : RULE =
    let (rule_to_string, term_to_string, pp_rule) =
         (rule_to_string (signature_of S), term_to_string (signature_of S), pp_rule (signature_of S))

    if (!trace > 1)
    then fprintf stderr "%s----------------------\n%ss_eval_rule %s\n%s\n\n"
            (spaces !level) (spaces !level) (show_s_state S) (toString 80 (indent (!level) (pp_rule R)))
    level := !level + 1

    let eval_update ((f, ts), t_rhs) (S, env, C) =
        if !trace > 0 then fprintf stderr "eval_update: %s\n" (rule_to_string (UpdateRule ((f, ts), t_rhs)))
        match s_eval_term t_rhs (S, env, C) with
        |   CondTerm (G, t1, t2) ->
                s_eval_rule (CondRule (G, UpdateRule ((f, ts), t1), UpdateRule ((f, ts), t2))) (S, env, C)
        |   _ ->
            let rec F ts_past = function
            |   (t1 as Value x1 :: ts_fut)        -> F (t1 :: ts_past) ts_fut
            |   (t1 as Initial (f, xs) :: ts_fut) -> F (t1 :: ts_past) ts_fut
            |   (CondTerm (G1, t11, t12) :: ts_fut) ->
                    s_eval_rule (CondRule (G1, F ts_past (t11 :: ts_fut), F ts_past (t12 :: ts_fut))) (S, env, C)
            |   (QuantTerm :: ts_fut)            -> failwith "SymbEval.eval_app_term: QuantTerm not implemented"
            |   (LetTerm (v, t1, t2) :: ts_fut)  -> failwith "SymbEval.eval_app_term: LetTerm not implemented"
            |   (t1 as VarTerm v :: ts_fut)      -> F (s_eval_term_ t1 (S, env, C) :: ts_past) ts_fut
            |   (t1 as AppTerm (_, _) :: ts_fut) -> F (s_eval_term_ t1 (S, env, C) :: ts_past) ts_fut
            |   (t1 as DomainTerm _ :: ts_fut)   -> failwith "SymbEval.eval_app_term: DomainTerm not implemented"
            |   [] ->
                match get_values (ts_past >>| fun t -> s_eval_term t (S, env, C)) with
                |   Some xs -> S_Updates (Set.singleton ((f, List.rev xs), s_eval_term t_rhs (S, env, C)));
                |   None -> try_case_distinction_for_update_with_finite_domain (S, env, C) f ts t_rhs
            F [] ts

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
    
    and eval_let (v, t, R) (S, env, C) =
        s_eval_rule R (S, add_binding env (v, s_eval_term t (S, env, C), term_type (signature_of S) env t), C)       // !!!!! is this one correct at all?

    and eval_forall (v, ts, G, R) (S, env, C) =
        match s_eval_term ts (S, env, C) with
        |   Value (SET xs) ->
                let eval_instance x =
                    let env' = add_binding env (v, Value x, term_type (signature_of S) env (Value x))
                    CondRule (s_eval_term G (S, env', C), s_eval_rule R (S, env', C), skipRule)
                let Rs = List.map (fun x -> eval_instance x) (Set.toList xs)
                s_eval_rule (ParRule Rs) (S, env, C)
        |   x -> failwith (sprintf "SymbEval.forall_rule: not a set (%A): %A v" ts x)

    and eval_macro_rule_call (r, args) (S, env, C) =
        let (formals, body) =
            try Map.find r (TopLevel.rules ())     // !!! should not use global TopLevel.rules
            with _ -> failwith (sprintf "SymbEval.s_eval_rule: macro rule %s not found" r)
        let env' =
            List.fold2 (fun env' formal arg -> add_binding env' (formal, s_eval_term arg (S, env, C), term_type (signature_of S) env arg)) env formals args
        s_eval_rule body (S, env', C)
 
    let R =
        match R with
        |   UpdateRule ((f, ts), t) -> eval_update ((f, ts), t) (S, env, C)
        |   CondRule (G, R1, R2)    -> eval_cond (G, R1, R2) (S, env, C)
        |   ParRule Rs              -> eval_par Rs (S, env, C)
        |   SeqRule Rs              -> eval_seq Rs (S, env, C)
        |   IterRule R              -> eval_iter R (S, env, C)
        |   LetRule (v, t, R)       -> eval_let (v, t, R) (S, env, C) 
        |   ForallRule (v, t, G, R) -> eval_forall (v, t, G, R) (S, env, C) 
        |   MacroRuleCall (r, args) -> eval_macro_rule_call (r, args) (S, env, C)
        |   S_Updates S             -> S_Updates S

    level := !level - 1
    if (!trace > 1)
    then fprintf stderr "%ss_eval_rule result = \n%s\n%s----------------------\n" (spaces !level) (toString 120 (indent (!level) (pp_rule R))) (spaces !level)

    R

//--------------------------------------------------------------------
// convert partially evaluated terms and rules to regular ones

let rec reconvert_value x =
    match x with
    |   UNDEF    -> AppTerm (UndefConst, [])
    |   BOOL b   -> AppTerm (BoolConst b, [])
    |   INT i    -> AppTerm (IntConst i, [])
    |   STRING s -> AppTerm (StringConst s, [])
    |   SET fs   -> //AppTerm (FctName "asSet", ?????)
                    failwith "reconvert_value: SET not implemented yet"
    |   CELL (tag, args) -> AppTerm (FctName tag, args >>| reconvert_value)

let reconvert_term t =
    term_induction (fun x -> x) {
        Value    = fun x -> reconvert_value x;
        Initial  = fun (f, xs) -> AppTerm (FctName f, xs >>| Value);
        AppTerm  = AppTerm;
        CondTerm = CondTerm;
        VarTerm  = VarTerm;
        LetTerm  = LetTerm;
        DomainTerm = DomainTerm;
    } t

let reconvert_rule R = 
    rule_induction reconvert_term {
        UpdateRule = UpdateRule;
        CondRule   = CondRule;
        ParRule    = ParRule;
        SeqRule    = SeqRule;
        IterRule   = IterRule;
        LetRule    = LetRule;
        MacroRuleCall = MacroRuleCall;
        ForallRule = ForallRule;
        S_Updates  = fun upds -> ParRule (List.map (fun ((f, xs), t_rhs) -> UpdateRule ((f, xs >>| Value), reconvert_term t_rhs)) (Set.toList upds))
    } R

//--------------------------------------------------------------------

let count_s_updates = rule_induction (fun _ -> ()) {
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

// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution (R_in : RULE) (steps : int): int * RULE =
    if (!trace > 2) then fprintf stderr "symbolic_execution\n"
    if (steps <= 0) then failwith "SymbEval.symbolic_execution: number of steps must be >= 1"
    let S0 = TopLevel.initial_state ()
    if (!trace > 2) then fprintf stderr "---\n%s\n---\n" (signature_to_string (signature_of (state_to_s_state S0)))
    let R_in_n_times = [ for _ in 1..steps -> R_in ]
    let R_in' = SeqRule (R_in_n_times @ [ skipRule ])      // this is to force the application of the symbolic update sets of R_in, thus identifying any inconsistent update sets
    let R_out = s_eval_rule R_in' (state_to_s_state S0, Map.empty, Set.empty)
    (count_s_updates R_out, reconvert_rule R_out)

//--------------------------------------------------------------------
// this version sets all non-static functions to be uninterpreted,
//   as needed for translation turbo ASM-> basic ASM (see paper
//   https://github.com/constructum/asm-symbolic-execution/blob/main/doc/2024--Del-Castillo--extended-version-of-ABZ-2024-paper--Using-Symbolic-Execution-to-Transform-Turbo-ASM-into-Basic-ASM.pdf
//   - section 4)
//
// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution_for_turbo_asm_to_basic_asm_transformation (R_in : RULE) : int * RULE =
    let S0 = TopLevel.initial_state ()
    let R_in' = SeqRule [ R_in; skipRule ]      // this is to force the application of the symbolic update sets of R_in, thus identifying any inconsistent update sets
    let R_out = s_eval_rule R_in' (state_to_s_state_only_static S0, Map.empty, Set.empty)
    (count_s_updates R_out, reconvert_rule R_out)
