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

//--------------------------------------------------------------------

let rec eval_term t =
    term_induction eval_name {
        Value    = fun x -> fun (S : STATE, env : ENV) -> x;
        AppTerm  = fun (f, ts) -> fun (S, env) -> (f S) (ts >>| fun t -> t (S, env))
        CondTerm = fun (G, t1, t2) -> fun (S, env) -> if G (S, env) = BOOL true then t1 (S, env) else t2 (S, env);
        Initial  = fun _ -> failwith "Eval.eval_term not defined on 'InitLoc' terms";
        VarTerm  = fun v -> fun (S, env) -> get_env env v;
        // LetTerm = fun (v, t1, t2) -> fun (S, env) -> t2 (S, add_binding env (v, t1 (S, env)))
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

let eval_rule = rule_induction eval_term ({
    UpdateRule = fun ((f, ts), t) -> fun (S : STATE, env : ENV) -> Set.singleton ((f, ts >>| fun t -> t (S, env)), t (S, env));
    CondRule = fun (G, R1, R2) -> fun (S, env) -> if G (S, env) = BOOL true then R1 (S, env) else R2 (S, env);
    ParRule = fun Rs -> fun (S, env) -> Set.unionMany (Rs >>| fun R -> R (S, env));
    SeqRule = fun Rs -> List.fold binary_seq (fun (S, env) -> Set.empty) Rs;
    IterRule = iterate;
    LetRule = fun (v, t, R) -> fun (S, env) -> R (S, add_binding env (v, t (S, env)));
    S_Updates = fun s_updates -> fun (S, env) -> Set.unionMany (List.map (fun (loc, t_rhs) -> Set.singleton (loc, eval_term t_rhs (S, env))) (Set.toList s_updates))
})

//--------------------------------------------------------------------
