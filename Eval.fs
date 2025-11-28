module Eval

//--------------------------------------------------------------------

open Common
open Background
open State
open AST

//--------------------------------------------------------------------

type ENV = Map<string, VALUE>

//--------------------------------------------------------------------

let empty : ENV =
    Map.empty

let defined_in (env : ENV) var =
    Map.containsKey var env

let get_env (env : ENV) (var : string) =
    Map.find var env

let add_binding (env : ENV) (var : string, value : VALUE) =
    Map.add var value env

//--------------------------------------------------------------------

let eval_name name S = interpretation S name

let eval_quantifier (q_kind, v, t_set, t_cond) (S, env) =
    match t_set (S, env) with
    |   SET (_, xs) ->
            let eval_cond x = (t_cond (S, add_binding env (v, x)) = BOOL true)
            match q_kind with
            |   Forall -> if Set.forall eval_cond xs then BOOL true else BOOL false
            |   Exist  -> if Set.exists eval_cond xs then BOOL true else BOOL false
            |   ExistUnique -> if Set.count (Set.filter (fun y -> eval_cond y) xs) = 1 then BOOL true else BOOL false
    |   _ -> failwith "Eval.eval_term: not a set"

let eval_domain ty S =
    match enum_finite_type ty S with
    |   Some finset -> SET (Signature.main_type_of ty, finset)
    |   None -> failwith (sprintf "Eval.eval_term: domain of type '%s' is not enumerable" (ty |> Signature.type_to_string));

//--------------------------------------------------------------------

let rec eval_term (t : TYPED_TERM) =
    ann_term_induction eval_name {
        Value      = fun (_, x) (_ : STATE, _ : ENV) -> x;
        AppTerm    = fun (_, (f, ts)) (S, env) -> (f S) (ts >>| fun t -> t (S, env))
        CondTerm   = fun (_, (G, t1, t2)) (S, env) -> if G (S, env) = BOOL true then t1 (S, env) else t2 (S, env);
        TupleTerm  = fun (_, ts) (S, env) -> TUPLE (ts >>| fun t -> t (S, env));
        Initial    = fun (_, _) -> failwith "Eval.eval_term not defined on 'InitLoc' terms";
        VarTerm    = fun (_, v) (_, env) -> get_env env v;
        QuantTerm  = fun (_, (q_kind, v, t_set, t_cond)) (S, env) -> eval_quantifier (q_kind, v, t_set, t_cond) (S, env);
        LetTerm    = fun (_, (v, t1, t2)) (S, env) -> t2 (S, add_binding env (v, t1 (S, env)));
        DomainTerm = fun (_, ty) (S, _) -> eval_domain ty S;
    } t

//--------------------------------------------------------------------

let binary_seq R1 R2 (S : STATE, env : ENV) =
    let U1 = R1 (S, env)
    in Updates.seq_merge_2 U1 (R2 (Updates.sequel_state S U1, env))

let rec iterate R (S : STATE, env : ENV) =
    let U = R (S, env)
    in  if Set.isEmpty U
        then U
        else Updates.seq_merge_2 U (iterate R (Updates.sequel_state S U, env))

let forall_rule (v, ts, G, R) (S : STATE, env : ENV) : Updates.UPDATE_SET=
    match ts (S, env) with
    |   SET (_, xs) ->
            let eval_instance x =
                let env' = add_binding env (v, x)
                in if G (S, env') = BOOL true then R (S, env') else Set.empty
            Set.fold (fun U1 x -> Set.union U1 (eval_instance x)) Set.empty xs
    |   _ -> failwith "Eval.forall_rule: not a set"

let eval_rule = rule_induction eval_term ({
    S_Updates = fun s_updates -> fun (S, env) -> Set.unionMany (List.map (fun (loc, t_rhs) -> Set.singleton (loc, eval_term t_rhs (S, env))) (Set.toList s_updates))
    UpdateRule = fun ((f, ts), t) -> fun (S : STATE, env : ENV) -> Set.singleton ((f, ts >>| fun t -> t (S, env)), t (S, env));
    CondRule  = fun (G, R1, R2) -> fun (S, env) -> if G (S, env) = BOOL true then R1 (S, env) else R2 (S, env);
    ParRule   = fun Rs -> fun (S, env) -> Set.unionMany (Rs >>| fun R -> R (S, env));
    SeqRule   = fun Rs -> List.fold binary_seq (fun (S, env) -> Set.empty) Rs;
    IterRule  = iterate;
    LetRule   = fun (v, t, R) -> fun (S, env) -> R (S, add_binding env (v, t (S, env)));
    ForallRule = fun (v, t_set, t_filter, R) -> fun (S, env) -> forall_rule (v, t_set, t_filter, R) (S, env);
    MacroRuleCall = fun (r, ts) -> fun (S, env) -> failwith (sprintf "Eval.eval_rule not implemented on MacroRuleCall '%s'" r);
})

//--------------------------------------------------------------------
