module SmtInterface

open Common
open Signature
open State
open AST
open Background
open Microsoft.Z3

let trace = ref 1

type SMT_CONTEXT = {
    ctx : Context ref;
    slv : Solver ref;
    typ : Map<string, Sort> ref;
    fct : Map<string, FuncDecl> ref;
    con : Map<string, Expr> ref;            // expressions corresponding to constants of enumerated types
}

type SMT_EXPR =
|   SMT_BoolExpr of BoolExpr
|   SMT_IntExpr of IntExpr
|   SMT_Expr of Expr

let new_smt_context () : SMT_CONTEXT =
    let ctx = ref (new Context ())
    let slv = ref ((!ctx).MkSolver());
    let typ = ref Map.empty
    let fct = ref Map.empty
    let con = ref Map.empty
    { ctx = ctx; slv = slv; typ = typ; fct = fct; con = con; }

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

let smt_map_type (C : SMT_CONTEXT) (sign : SIGNATURE) (T : TYPE) : Sort =
    assert(match T with Boolean -> true | Integer -> true | String -> true | TypeCons(tyname,[]) -> type_kind tyname sign = EnumType | _ -> false)
    let ctx = !C.ctx
    match T with
    |   Boolean -> ctx.BoolSort
    |   Integer -> ctx.IntSort
    |   String  -> ctx.StringSort
    |   TypeCons (tyname, []) -> Map.find tyname (!C.typ)   // !!! currently all user-defined domains are of finite cardinality (enum-like), may need to be changed in the future
    |   _       -> failwith (sprintf "smt_map_type: unsupported type %s" (type_to_string T))

let smt_add_types_and_functions (C : SMT_CONTEXT) sign (new_sign : SIGNATURE, new_state : STATE) : unit =
    let ctx = !C.ctx
    let type_names = Signature.type_names new_sign |> Set.filter (fun tyname -> let k = type_kind tyname new_sign in k <> BasicType && k <> AnyType)   // only user-defined types, i.e. not BasicType's, are of interest here
    let fct_names = Signature.fct_names new_sign
    //!!! filter to avoid problems due to AsmetaL standard library functions that cannot be mapped
    //!!!  ad-hoc exclusion of AsmetaL controlled function 'result' and 'self', this should be done only for AsmetaL - tbd:
    //!!!    --> tbd: AsmetaL flag
    let fct_names = Set.filter (fun f -> fct_kind f new_sign = Controlled && f <> "result" && f <> "self") fct_names
    let add_type C tyname =
        let (kind, ar) = (type_kind tyname new_sign, type_arity tyname new_sign)
        if kind <> EnumType || ar <> 0 then failwith (sprintf "smt_add_types_and_functions: add_type: only enumerated types without type parameters are supported (type '%s' is of kind '%A' and has arity %d)" tyname kind ar)
        let constructor_names = Signature.fct_names new_sign |> Set.filter (fun f -> fct_kind f new_sign = Signature.Constructor && fct_type f new_sign = ([], TypeCons (tyname, []))) |> Set.toArray
        if Array.length constructor_names > 0
        then    if !trace > 0 then fprintf stderr "SmtInterface.add_type: %s = { %s }\n" tyname (String.concat ", " constructor_names)
                let enum_sort = ctx.MkEnumSort (tyname, constructor_names)
                C.typ := Map.add tyname enum_sort (!C.typ)
                C.con := Common.map_override (!C.con) (Array.fold2 (fun m cons_name smt_expr -> Map.add cons_name smt_expr m) Map.empty constructor_names (enum_sort.Consts))
        else    fprintf stderr "SmtInterface.add_type: warning: skipping abstract type '%s', because it has no elements (%s = { })\n" tyname tyname
    let add_function C fct_name =
        if !trace > 0 then fprintf stderr "SmtInterface.add_function: %s : %s\n" fct_name (fct_type fct_name new_sign |> fct_type_to_string)
        let (Ts_dom, T_ran) = fct_type fct_name new_sign
        let func_decl = ctx.MkFuncDecl (fct_name, Array.ofList (Ts_dom >>| smt_map_type C sign), smt_map_type C sign T_ran)
        C.fct := Map.add fct_name func_decl (!C.fct)
    Set.map (add_type C) type_names |> ignore
    Set.map (add_function C) fct_names |> ignore

//--------------------------------------------------------------------

let convert_to_expr = function
    |   SMT_BoolExpr e -> e :> Expr
    |   SMT_IntExpr e  -> e :> Expr
    |   SMT_Expr e     -> e

let rec smt_map_term_background_function sign C (f, ts) : SMT_EXPR =
    let ctx = !C.ctx
    let es = ts >>| smt_map_term sign C
    match (f, es) with
    |   ("=",       [ SMT_BoolExpr e1; SMT_BoolExpr e2 ]) -> SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("=",       [ SMT_IntExpr e1;  SMT_IntExpr e2 ])  -> SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("=",       [ SMT_Expr e1;     SMT_Expr e2 ])     -> SMT_BoolExpr (ctx.MkEq (e1, e2))
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
    |   (f, (dom, (ran as TypeCons (tyname, []))), es) ->
            let (kind, ar) = (type_kind tyname sign, type_arity tyname sign)
            if kind <> EnumType || ar <> 0 then failwith (sprintf "smt_map_term_user_defined_function: types in function '%s : %s -> %s' not supported" f (type_list_to_string dom) (type_to_string ran))
            SMT_Expr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)))
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
    |   Value (CELL (cons, []))     -> SMT_Expr (Map.find cons (!C.con))
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
