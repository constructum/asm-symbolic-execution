module SmtInterface

open Common
open Signature
open State
open AST
open Background
open Microsoft.Z3

let trace = ref 0

type SMT_CONTEXT = {
    ctx : Context ref;
    slv : Solver ref;
    typ : Map<string, Sort> ref;
    fct : Map<string, FuncDecl> ref;
    con : Map<string, Expr> ref;            // expressions corresponding to constants of enumerated types
    ctr : int ref;                          // SMT call counter
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
    let ctr = ref 0
    { ctx = ctx; slv = slv; typ = typ; fct = fct; con = con; ctr = ctr }

let smt_ctx_reset (C : SMT_CONTEXT) =
    (!C.ctx).Dispose ();
    C.ctx := new Context ()
    (!C.slv).Reset ();
    C.typ := Map.empty
    C.fct := Map.empty
    C.con := Map.empty
    C.ctr := 0

let smt_solver_reset (C : SMT_CONTEXT) =
    (!C.slv).Reset ()

let smt_solver_push (C : SMT_CONTEXT) =
    (!C.slv).Push ()

let smt_solver_pop (C : SMT_CONTEXT) =
    (!C.slv).Pop ()

let rec smt_map_type (C : SMT_CONTEXT) (sign : SIGNATURE) (T : TYPE) : Sort =
    //assert(match T with Boolean -> true | Integer -> true | String -> true | TypeCons(tyname,[]) -> type_kind tyname sign = EnumType | _ -> false)
    let ctx = !C.ctx
    match T with
    |   Boolean -> ctx.BoolSort
    |   Integer -> ctx.IntSort
    |   String  -> ctx.StringSort
    |   TypeCons (tyname, []) -> Map.find tyname (!C.typ)
    |   Subset (_, main_type) -> smt_map_type C sign main_type   // !!! currently all user-defined domains are of finite cardinality (enum-like), may need to be changed in the future
    |   _       -> failwith (sprintf "smt_map_type: unsupported type %s" (type_to_string T))

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
    |   ("!=",      [ SMT_Expr e1;     SMT_Expr e2 ])     -> SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
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
    |   _ -> failwith (sprintf "smt_map_term_background_function: error (t = %s)" (term_to_string sign (AppTerm' (snd (fct_type f sign), (FctName f, ts)))))

and smt_map_term_user_defined_function sign C (f, ts) : SMT_EXPR =
    let (ctx, fct) = (!C.ctx, !C.fct)
    let fail (f, dom, ran) =
        failwith (sprintf "smt_map_term_user_defined_function: function '%s : %s -> %s' not found" f (type_list_to_string dom) (type_to_string ran))
    if fct_kind f sign = Controlled
    then
        match (f, fct_type f sign, ts >>| fun t -> smt_map_term sign C t) with
        |   (f, (dom, Boolean), es) ->
                try SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> BoolExpr) with _ -> fail (f, dom, Boolean)
        |   (f, (dom, Subset (_, Boolean)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                try SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> BoolExpr) with _ -> fail (f, dom, Boolean)
        |   (f, (dom, Integer), es) ->
                try SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> IntExpr) with _ -> fail (f, dom, Integer)
        |   (f, (dom, Subset (_, Integer)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                try SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr)) :?> IntExpr) with _ -> fail (f, dom, Integer)
        |   (f, (dom, (ran as TypeCons (tyname, []))), es) ->
                let (kind, ar) = (type_kind tyname sign, type_arity tyname sign)
                if kind <> EnumType || ar <> 0 then failwith (sprintf "smt_map_term_user_defined_function: types in function '%s : %s -> %s' not supported" f (type_list_to_string dom) (type_to_string ran))
                try SMT_Expr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| convert_to_expr))) with _ -> fail (f, dom, ran)
        |   (f, (_, ran), _) -> failwith (sprintf "smt_map_term_user_defined_function : error (t = %s)" (term_to_string sign (AppTerm' (ran, (FctName f, ts)))))
    else failwith (sprintf "smt_map_term_user_defined_function: unsupported function kind '%s' of function '%s'" (fct_kind f sign |> fct_kind_to_string) f)

and smt_map_ITE sign C (G_, t1_, t2_) : SMT_EXPR =
    let ctx = !C.ctx
    let err_msg (G, T_G, t1, T_t1, t2, T_t2) =
        failwith (sprintf "smt_map_ITE: type error: for term %s the expected type is (Boolean, T, T), where T is Boolean, Integer or a user-defined type; type (%s, %s, %s) found instead"
            (term_to_string sign (CondTerm' (get_type t1, (G, t1, t2)))) (type_to_string T_G) (type_to_string T_t1) (type_to_string T_t2) )
    match (smt_map_term sign C G_, get_type G_, smt_map_term sign C t1_, get_type t1_, smt_map_term sign C t2_, get_type t2_) with
    |   (SMT_BoolExpr G, Boolean, SMT_BoolExpr t1, Boolean, SMT_BoolExpr t2, Boolean) ->
            SMT_BoolExpr (ctx.MkITE (G, t1 :> Expr, t2 :> Expr) :?> BoolExpr)
    |   (SMT_BoolExpr G, Boolean, SMT_IntExpr t1, Integer, SMT_IntExpr t2, Integer) ->
            SMT_IntExpr (ctx.MkITE (G, t1 :> Expr, t2 :> Expr) :?> IntExpr)
    |   (SMT_BoolExpr G, Boolean, SMT_Expr t1, TypeCons (tyname1, []), SMT_Expr t2, TypeCons (tyname2, [])) ->
            if tyname1 = tyname2
            then SMT_Expr (ctx.MkITE (G, (t1 : Expr), (t2 : Expr)) : Expr)
            else err_msg (G_, Boolean, t1_, TypeCons (tyname1, []), t2_, TypeCons (tyname2, []))
    |   (_, T_G, _, T_t1, _, T_t2) -> err_msg (G_, T_G, t1_, T_t1, t2_, T_t2)

and smt_map_app_term sign C (f, ts) : SMT_EXPR =
    if (Set.contains f (fct_names Background.signature))
    then smt_map_term_background_function sign C (f, ts)
    else failwith (sprintf "smt_map_app_term: '%s' is not a background function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_initial sign C (f, ts) : SMT_EXPR =
    if Signature.fct_kind f sign = Controlled
    then smt_map_term_user_defined_function sign C (f, ts)
    else failwith (sprintf "smt_map_app_term: '%s' is not a controlled function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_term sign C (t : TYPED_TERM) : SMT_EXPR =
    //if !trace > 0 then fprintf stderr "smt_map_term: %s -> " (term_to_string sign t)
    let ctx = !C.ctx
    let result = 
        match t with
        |   AppTerm' (_, (IntConst i, []))    -> SMT_IntExpr (ctx.MkInt i)
        |   Value' (_, (INT i))               -> SMT_IntExpr (ctx.MkInt i)
        |   AppTerm' (_, (BoolConst b, []))   -> SMT_BoolExpr (ctx.MkBool b)
        |   Value' (_, (BOOL b))              -> SMT_BoolExpr (ctx.MkBool b)
        |   Value' (_, (CELL (cons, [])))     -> SMT_Expr (Map.find cons (!C.con))
        |   Initial' (_, (f, xs))             -> smt_map_initial sign C (f, xs >>| mkValue sign)
        |   CondTerm' (_, (G, t1, t2))        -> smt_map_ITE sign C (G, t1, t2)
        |   AppTerm' (_, (FctName f, ts)) -> smt_map_app_term sign C (f, ts)
        |   t -> failwith (sprintf "smt_map_term: not supported (t = %s)" (term_to_string sign t))
    result

//--------------------------------------------------------------------

let smt_assert sign C (phi : TYPED_TERM) =
    if get_type phi = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> C.ctr := !C.ctr + 1; (!C.slv).Assert be
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_assert' expects a Boolean term, %s found instead " (term_to_string sign phi))

let smt_formula_is_true sign C (phi : TYPED_TERM) =
    if get_type phi = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check ((!C.ctx).MkNot be) = Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_true: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_formula_is_true' expects a Boolean term, %s found instead " (term_to_string sign phi))

let smt_formula_is_false sign C (phi : TYPED_TERM) =
    if get_type phi = Boolean
    then match smt_map_term sign C phi with
         | SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check be = Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_false: error converting Boolean term (term = %s)" (term_to_string sign phi))
    else failwith (sprintf "'smt_formula_is_false' expects a Boolean term, %s found instead " (term_to_string sign phi))

//--------------------------------------------------------------------

let smt_add_types_and_functions (C : SMT_CONTEXT) sign (new_sign : SIGNATURE, new_state : STATE) : unit =
    let ctx = !C.ctx
    let type_names = Signature.type_names new_sign |> Set.filter (fun tyname -> let k = type_kind tyname new_sign in k <> BasicType && k <> AnyType)   // only user-defined types, i.e. not BasicType's, are of interest here
    let fct_names = Signature.fct_names new_sign
    //!!! filter to avoid problems due to AsmetaL standard library functions that cannot be mapped
    //!!!  ad-hoc exclusion of AsmetaL controlled function 'result' and 'self', this should be done only for AsmetaL - tbd:
    //!!!    --> tbd: AsmetaL flag
    let fct_names = Set.filter (fun f -> fct_kind f new_sign = Controlled && f <> "result" && f <> "self") fct_names
    let init_macros = snd new_state._dynamic_initial        // initialisation of controlled functions defined in AsmetaL init sections by (args, term) pairs
    let add_type C tyname =
        let (kind, ar) = (type_kind tyname new_sign, type_arity tyname new_sign)
        if kind = EnumType && ar = 0
        then    let constructor_names = Signature.fct_names new_sign |> Set.filter (fun f -> fct_kind f new_sign = Signature.Constructor && fct_type f new_sign = ([], TypeCons (tyname, []))) |> Set.toArray
                if Array.length constructor_names > 0
                then    if !trace > 0 then fprintf stderr "SmtInterface.add_type: %s = { %s }\n" tyname (String.concat ", " constructor_names)
                        let enum_sort = ctx.MkEnumSort (tyname, constructor_names)
                        C.typ := Map.add tyname enum_sort (!C.typ)
                        C.con := Common.map_override (!C.con) (Array.fold2 (fun m cons_name smt_expr -> Map.add cons_name smt_expr m) Map.empty constructor_names (enum_sort.Consts))
                else    fprintf stderr "SmtInterface.add_type: warning: skipping abstract type '%s', because it has no elements (%s = { })\n" tyname tyname
        else if kind = SubsetType
        then ()   // simply ignore, subset types are mapped to their main type by smt_map_type
        else fprintf stderr "SmtInterface.add_type: unsupported type '%s' is ignored\n" tyname
    let add_function C fct_name =
        let (Ts_dom, T_ran) = fct_type fct_name new_sign
        let func_decl = ctx.MkFuncDecl (fct_name, Array.ofList (Ts_dom >>| smt_map_type C sign), smt_map_type C sign T_ran)
        C.fct := Map.add fct_name func_decl (!C.fct)
        // // mapping of init
        // match Map.tryFind fct_name init_macros with
        // |   Some ([], t_rhs) ->
        //         let equals t1 t2 = AppTerm' (Boolean, (FctName "=", [t1; t2]))
        //         let t_lhs = Initial' (T_ran, (fct_name, []))
        //         smt_assert sign C (equals t_lhs t_rhs)
        // |   Some (_, _) -> fprintf stderr "SMT initialisation of non-nullary function '%s' not yet implemented\n" fct_name
        // |   None -> ()
    Set.map (add_type C) type_names |> ignore
    Set.map (add_function C) fct_names |> ignore

//--------------------------------------------------------------------
