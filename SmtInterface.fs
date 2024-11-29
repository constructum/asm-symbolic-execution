module SmtInterface

open Common
open Signature
open State
open AST
open Background
open Microsoft.Z3

type SMT_CONTEXT = {
    ctx : Context ref;
    slv : Solver ref;
    fct : Map<string, FuncDecl> ref;
}

type SMT_EXPR =
|   SMT_BoolExpr of BoolExpr
|   SMT_IntExpr of IntExpr

let new_smt_context () : SMT_CONTEXT =
    let ctx = ref (new Context ())
    let slv = ref ((!ctx).MkSolver());
    let fct = ref Map.empty
    { ctx = ctx; slv = slv; fct = fct; }

let smt_ctx_reset (C : SMT_CONTEXT) =
    (!C.ctx).Dispose ();
    C.ctx := new Context ()
    (!C.slv).Reset ();
    C.fct := Map.empty

let smt_solver_reset (C : SMT_CONTEXT) =
    (!C.slv).Reset ()

let smt_solver_push (C : SMT_CONTEXT) =
    (!C.slv).Push ()

let smt_solver_pop (C : SMT_CONTEXT) =
    (!C.slv).Pop ()

let smt_map_type C (T : TYPE) : Sort =
    assert(match T with Boolean -> true | Integer -> true | String -> true | _ -> false)
    let ctx = !C.ctx
    match T with
    |   Boolean -> ctx.BoolSort
    |   Integer -> ctx.IntSort
    |   String  -> ctx.StringSort
    |   _       -> failwith (sprintf "smt_map_type: unsupported type %s" (type_to_string T))

let smt_add_functions C (new_sign : SIGNATURE, new_state : STATE) : unit =
    let ctx = !C.ctx
    let fct_names = Signature.fct_names new_sign
    let add_function C fct_name =
        let (Ts_dom, T_ran) = fct_type fct_name new_sign
        let func_decl = ctx.MkFuncDecl (fct_name, Array.ofList (Ts_dom >>| smt_map_type C), smt_map_type C T_ran)
        C.fct := Map.add fct_name func_decl (!C.fct)
    Set.map (add_function C) fct_names |> ignore
    // !!! state tbd, but there is no syntax for defining initial interpretation of functions yet

//--------------------------------------------------------------------

let convert_to_expr = function
    |   SMT_BoolExpr e -> e :> Expr
    |   SMT_IntExpr e  -> e :> Expr

let rec smt_map_term_background_function sign C (f, ts) : SMT_EXPR =
    let ctx = !C.ctx
    let es = ts >>| smt_map_term sign C
    match (f, es) with
    |   ("=",       [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("=",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("!=",      [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
    |   ("!=",      [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
    |   ("not",     [ SMT_BoolExpr e ])                   -> SMT_BoolExpr (ctx.MkNot e)
    |   ("and",     [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkAnd (e1, e2))
    |   ("or",      [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkOr (e1, e2))
    |   ("xor",     [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkXor (e1, e2))
    |   ("implies", [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkImplies (e1, e2))
    |   ("iff",     [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkIff (e1, e2))
    |   (">",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkGt (e1, e2))
    |   (">=",      [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkGe (e1, e2))
    |   ("<",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkLt (e1, e2))
    |   ("<=",      [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkLe (e1, e2))
    |   ("+",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_IntExpr (ctx.MkAdd (e1, e2) :?> IntExpr)
    |   ("-",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_IntExpr (ctx.MkSub (e1, e2) :?> IntExpr)
    |   ("*",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_IntExpr (ctx.MkMul (e1, e2) :?> IntExpr)
    |   _ -> //failwith (sprintf "smt_map_term_background_function: error (t = %s)\n%A\n" (term_to_string sign (AppTerm (FctName f, ts))) es)
             failwith (sprintf "smt_map_term_background_function: error (t = %s)" (term_to_string sign (AppTerm (FctName f, ts))))

and smt_map_term_user_defined_function sign C (f, ts) : SMT_EXPR =
    let (ctx, fct) = (!C.ctx, !C.fct)
    match (f, fct_type f sign, ts >>| fun t -> smt_map_term sign C t) with
    |   (f, (_, Boolean), es) -> SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> BoolExpr)
    |   (f, (_, Integer), es) -> SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> IntExpr)
    |   _ -> failwith (sprintf "smt_map_term_user_defined_function : error (t = %s)" (term_to_string sign (AppTerm (FctName f, ts))))

and smt_map_ITE sign C (G, t1, t2) : SMT_EXPR =
    let ctx = !C.ctx
    let typecheck t = Parser.typecheck_term t (sign, Map.empty)
    match (smt_map_term sign C G, typecheck G, smt_map_term sign C t1, typecheck t1, smt_map_term sign C t2, typecheck t2) with
    |   (SMT_BoolExpr G, Boolean, SMT_BoolExpr t1, Boolean, SMT_BoolExpr t2, Boolean) ->
            SMT_BoolExpr (ctx.MkITE (G, t1 :> Expr, t2 :> Expr) :?> BoolExpr)
    |   (SMT_BoolExpr G, Boolean, SMT_IntExpr t1, Integer, SMT_IntExpr t2, Integer) ->
            SMT_IntExpr (ctx.MkITE (G, t1 :> Expr, t2 :> Expr) :?> IntExpr)
    |   (_, T_G, _, T_t1, _, T_t2) ->
            failwith (sprintf "smt_map_ITE: type error: for term %s the expected type is (Boolean, T, T) with T in { Boolean, Integer }, type (%s, %s, %s) found instead"
                (term_to_string sign (CondTerm (G, t1, t2))) (type_to_string T_G) (type_to_string T_t1) (type_to_string T_t2) )

and smt_map_app_term sign C (f, ts) : SMT_EXPR =
    if (Set.contains f (fct_names Background.signature))
    then smt_map_term_background_function sign C (f, ts)
    else if Signature.fct_kind f sign = Static
         then smt_map_term_user_defined_function sign C (f, ts)
         else failwith (sprintf "smt_map_app_term: '%s' is not a static function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_initial sign C (f, ts) : SMT_EXPR =
    if Signature.fct_kind f sign = Controlled
    then smt_map_term_user_defined_function sign C (f, ts)
    else failwith (sprintf "smt_map_app_term: '%s' is not a controlled function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_term sign C (t : TERM) : SMT_EXPR =
    let ctx = !C.ctx
    match t with
    |   AppTerm (IntConst i, [])    -> SMT_IntExpr (ctx.MkInt i)
    |   Value (INT i)               -> SMT_IntExpr (ctx.MkInt i)
    |   AppTerm (BoolConst b, [])   -> SMT_BoolExpr (ctx.MkBool b)
    |   Value (BOOL b)              -> SMT_BoolExpr (ctx.MkBool b)
    |   Initial (f, xs)             -> smt_map_initial sign C (f, xs >>| Value)
    |   CondTerm (G, t1, t2)        -> smt_map_ITE sign C (G, t1, t2)
    |   AppTerm (FctName f, ts)     -> smt_map_app_term sign C (f, ts)
    |   t -> failwith (sprintf "smt_map_term: not supported (t = %s)" (term_to_string sign t))

//--------------------------------------------------------------------

let smt_assert sign C (phi : TERM) =
    if Parser.typecheck_term phi (sign, Map.empty) = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> (!C.slv).Assert be
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_assert' expects a Boolean term, %s found instead " (term_to_string sign phi))

let smt_formula_is_true sign C (phi : TERM) =
    if Parser.typecheck_term phi (sign, Map.empty) = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> ((!C.slv).Check ((!C.ctx).MkNot be) = Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_check' expects a Boolean term, %s found instead " (term_to_string sign phi))

let smt_formula_is_false sign C (phi : TERM) =
    if Parser.typecheck_term phi (sign, Map.empty) = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> ((!C.slv).Check be = Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_check' expects a Boolean term, %s found instead " (term_to_string sign phi))
