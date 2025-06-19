module DAG

//--------------------------------------------------------------------

open System.Collections.Generic

open Common
open PrettyPrinting
open Background
//open Signature
// open AST
// open SmtInterface

//--------------------------------------------------------------------

let trace = ref 0
let level = ref 0
let module_name = "DAG"

let rec spaces level = if level = 0 then "" else "    " + spaces (level-1)
let rec indent level ppt = if level = 0 then ppt else blo4 [ indent (level-1) ppt ]

//--------------------------------------------------------------------

type TERM_ATTRS = {
    term_id   : int
    term_type : Signature.TYPE
}

type GLOBAL_CTX' = {
    signature    : Signature.SIGNATURE
    s_state      : SymbState.S_STATE            // use only for initial state in this module, keep track of updates separately
    fwdTermTable : Dictionary<TERM', TERM>
    bwdTermTable : Dictionary<TERM, TERM' * TERM_ATTRS>
}

and GLOBAL_CTX = GlobalCtx of int

and GLOBAL_CTX_TABLE = {
    ctx_table : Dictionary<int, GLOBAL_CTX'>
    next_ctx  : int ref
}

and TERM' =
|   Value'      of (VALUE)                     // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   Initial'    of (Signature.FCT_NAME * VALUE list)   // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   AppTerm'    of (Signature.NAME * TERM list)
|   CondTerm'   of (TERM * TERM * TERM)
|   VarTerm'    of (string)
|   QuantTerm'  of (AST.QUANT_KIND * string * TERM * TERM)
|   LetTerm'    of (string * TERM * TERM)
|   DomainTerm' of Signature.TYPE                  // AsmetaL construct: finite type (e.g. enum, abstract, subsetof) used as finite set
//  | TupleTerm   of 'annotation * ('annotation ANN_TERM list)

and TERM = Term of int

let global_ctxs : GLOBAL_CTX_TABLE = {
    ctx_table = new Dictionary<int, GLOBAL_CTX'>()
    next_ctx  = ref 0
}

let new_global_ctx (sign : Signature.SIGNATURE, s_state : SymbState.S_STATE) =
    let ctx_id = !global_ctxs.next_ctx
    global_ctxs.next_ctx := ctx_id + 1
    let new_ctx = {
        signature    = sign
        s_state      = s_state
        fwdTermTable = new Dictionary<TERM', TERM>(HashIdentity.Structural)
        bwdTermTable = new Dictionary<TERM, TERM' * TERM_ATTRS>(HashIdentity.Structural)
    }
    global_ctxs.ctx_table.[ctx_id] <- new_ctx
    GlobalCtx ctx_id

let get_global_ctx' (GlobalCtx gctx_id) =
    if global_ctxs.ctx_table.ContainsKey gctx_id then
        global_ctxs.ctx_table.[gctx_id]
    else
        failwith (sprintf "get_global_ctx': context %d not found" gctx_id)

let signature_of (GlobalCtx gctx_id) =
    global_ctxs.ctx_table.[gctx_id].signature

let s_state_of (GlobalCtx gctx_id) =
    global_ctxs.ctx_table.[gctx_id].s_state

let rec compute_type gctx (t' : TERM') : Signature.TYPE =
    let (sign, get_type) = (signature_of gctx, get_type gctx)
    match t' with
    |   Value' x -> Background.type_of_value sign x
    |   Initial' (f, xs) -> Signature.match_fct_type f (xs >>| Background.type_of_value sign) (Signature.fct_types f sign)
    |   AppTerm' (Signature.UndefConst, _)    -> Signature.Undef
    |   AppTerm' (Signature.BoolConst _, _)   -> Signature.Boolean
    |   AppTerm' (Signature.IntConst _, _)    -> Signature.Integer
    |   AppTerm' (Signature.StringConst _, _) -> Signature.String
    |   AppTerm' (Signature.FctName f, ts)    -> Signature.match_fct_type f (ts >>| get_type) (Signature.fct_types f sign)
    |   CondTerm' (G, t1, t2) -> if get_type t1 = get_type t2 then get_type t1 else failwith "compute_type: types of branches of conditional term do not match"
    |   VarTerm' v -> failwith (sprintf "compute_type: variable '%s' does not have a type" v)
    |   QuantTerm' (_, _, t_set, _) -> get_type t_set
    |   LetTerm' (_, t1, _) -> get_type t1
    |   DomainTerm' tyname -> tyname

and get_type (gctx as GlobalCtx gctx_id) (t : TERM) : Signature.TYPE =
    let ctx = global_ctxs.ctx_table.[gctx_id]
    if ctx.bwdTermTable.ContainsKey t then
        let (_, attrs) = ctx.bwdTermTable.[t]
        attrs.term_type
    else
        failwith (sprintf "get_type: term %A not found in context %d" t gctx_id)

let make_term (GlobalCtx gctx_id) (t' : TERM') : TERM =
    let ctx = global_ctxs.ctx_table.[gctx_id]
    if ctx.fwdTermTable.ContainsKey t' then
        ctx.fwdTermTable.[t']
    else
        let term_id = ctx.fwdTermTable.Count
        let attrs = {
            term_id   = term_id
            term_type = compute_type (GlobalCtx gctx_id) t'
        }
        ctx.fwdTermTable.[t'] <- Term term_id
        ctx.bwdTermTable.[Term term_id] <- (t', attrs)
        Term term_id

let get_term'_attrs (gctx: GLOBAL_CTX) (Term term_id) =
    let (GlobalCtx gctx_id) = gctx
    let ctx = global_ctxs.ctx_table.[gctx_id]
    if ctx.bwdTermTable.ContainsKey (Term term_id) then
        ctx.bwdTermTable.[Term term_id]
    else
        failwith (sprintf "get_term': term %d not found in context %d" term_id gctx_id)

let get_term' (gctx: GLOBAL_CTX) (Term term_id) = get_term'_attrs gctx (Term term_id) |> fst
let get_attrs (gctx: GLOBAL_CTX) (Term term_id) = get_term'_attrs gctx (Term term_id) |> snd


let Value gctx x = make_term gctx (Value' x)
let Initial gctx (f, xs) = make_term gctx (Initial' (f, xs))
let AppTerm gctx (f, ts) = make_term gctx (AppTerm' (f, ts))
let CondTerm gctx (G, t1, t2) = make_term gctx (CondTerm' (G, t1, t2))
let VarTerm gctx v = make_term gctx (VarTerm' v)
let QuantTerm gctx (q_kind, v, t_set, t_cond) = make_term gctx (QuantTerm' (q_kind, v, t_set, t_cond))
let LetTerm gctx (x, t1, t2) = make_term gctx (LetTerm' (x, t1, t2))
let DomainTerm gctx tyname = make_term gctx (DomainTerm' tyname)    

//--------------------------------------------------------------------

type TERM_INDUCTION<'name, 'term> = {
    Value      : (VALUE) -> 'term;
    Initial    : (string * VALUE list) -> 'term;
    AppTerm    : ('name * 'term list) -> 'term;
    CondTerm   : ('term * 'term * 'term) -> 'term;
    VarTerm    : (string) -> 'term;
    QuantTerm  : (AST.QUANT_KIND * string * 'term * 'term) -> 'term;
    LetTerm    : (string * 'term * 'term) -> 'term;
    DomainTerm : (Signature.TYPE) -> 'term;
}
let rec term_induction (gctx: GLOBAL_CTX) (name : Signature.NAME -> 'name) (F : TERM_INDUCTION<'name, 'term>) (t : TERM) :'term =
    let term_ind = term_induction gctx name F
    match get_term' gctx t with
    |   Value' x              -> F.Value x
    |   Initial' (f, xs)      -> F.Initial (f, xs)
    |   AppTerm' (f, ts)      -> F.AppTerm (name f, List.map (fun t -> term_ind t) ts)
    |   CondTerm' (G, t1, t2) -> F.CondTerm (term_ind G, term_ind t1, term_ind t2)
    |   VarTerm' v            -> F.VarTerm v
    |   QuantTerm' (q_kind, v, t_set, t_cond) -> F.QuantTerm (q_kind, v, term_ind t_set, term_ind t_cond)
    |   LetTerm' (x, t1, t2)  -> F.LetTerm (x, term_ind t1, term_ind t2)
    |   DomainTerm' tyname    -> F.DomainTerm tyname

//--------------------------------------------------------------------

type RULE =
| S_Updates of Set<(Signature.FCT_NAME * VALUE list) * TERM>  //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
| UpdateRule of (Signature.FCT_NAME * TERM list) * TERM
| CondRule of TERM * RULE * RULE
| ParRule of RULE list
| SeqRule of RULE list
| IterRule of RULE
| LetRule of string * TERM * RULE
| ForallRule of string * TERM * TERM * RULE
| MacroRuleCall of Signature.RULE_NAME * TERM list

let skipRule = ParRule []

//--------------------------------------------------------------------

type RULE_INDUCTION<'term, 'rule> = {
    S_Updates : Set<(Signature.FCT_NAME * VALUE list) * TERM> -> 'rule;     // what not ""... * 'term>" ?
    UpdateRule : (Signature.FCT_NAME * 'term list) * 'term -> 'rule;
    CondRule : 'term * 'rule * 'rule -> 'rule;
    ParRule : 'rule list -> 'rule;
    SeqRule : 'rule list -> 'rule;
    IterRule : 'rule -> 'rule;
    LetRule : string * 'term * 'rule -> 'rule;
    ForallRule : string * 'term * 'term * 'rule -> 'rule;
    MacroRuleCall : Signature.RULE_NAME * 'term list -> 'rule;     // Map<FCT_NAME * VALUE list, 'term> -> 'rule;
}

let rec rule_induction (term : TERM -> 'term) (F : RULE_INDUCTION<'term, 'rule>) (R : RULE) : 'rule =
    let rule_ind = rule_induction term
    match R with
    |   S_Updates U -> F.S_Updates U   // F.S_Updates (Map.map (fun loc -> fun t_rhs -> term t_rhs) U)
    |   UpdateRule ((f: Signature.FCT_NAME, ts), t) -> F.UpdateRule ((f, List.map term ts), term t)
    |   CondRule (G, R1, R2: RULE) -> F.CondRule (term G, rule_ind F R1, rule_ind F R2)
    |   ParRule Rs -> F.ParRule (List.map (rule_ind F) Rs)
    |   SeqRule Rs -> F.SeqRule (List.map (rule_ind F) Rs)
    |   IterRule R -> F.IterRule (rule_ind F R)
    |   LetRule (v, t, R) -> F.LetRule (v, term t, (rule_ind F) R)
    |   ForallRule (v, t_set, t_filter, R) -> F.ForallRule (v, term t_set, term t_filter, (rule_ind F) R)
    |   MacroRuleCall (r, ts) -> F.MacroRuleCall (r, List.map term ts)

//--------------------------------------------------------------------
//
//  pretty printing
//
//--------------------------------------------------------------------

let rec pp_list sep = function
|   []         -> []
|   [x]        -> [ x ]
|   (x :: xs') -> x :: (sep @ (pp_list sep xs'))

let pp_name (name : Signature.NAME) =
    (   match name with
    |   Signature.UndefConst -> "undef"
    |   Signature.BoolConst b -> if b then "true" else "false"
    |   Signature.IntConst i -> i.ToString()
    |   Signature.StringConst s -> "\"" + s + "\""
    |   Signature.FctName f -> f ) |> str

let pp_app_term sign = function
    |   (Signature.FctName f, [t1; t2]) when Signature.infix_status f sign <> Signature.NonInfix ->
            blo0 [ str "("; blo0 [ t1; brk 1; str (sprintf "%s " f); t2 ]; str ")" ]
    |   (Signature.FctName f, ts) when ts <> [] ->
            blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] ts); str ")" ]
    |   (name, _) -> pp_name name

let pp_location_term sign prefix = function
    |   (f : string, xs : VALUE list) when xs <> [] ->
            blo0 [ str (prefix+"["); str f; str "("; blo0 (pp_list [str",";brk 1] (List.map (fun x -> str (value_to_string x)) xs)); str ")]" ]
    |   (f, _) -> blo0 [ str $"{prefix}[{f}]" ]

let rec pp_term (gctx as GlobalCtx _) (t : TERM) =
    let sign = (get_global_ctx' gctx).signature
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    term_induction gctx (fun x -> x) {
        AppTerm  = fun (f, ts) -> pp_app_term (f, ts);
        CondTerm = fun (G, t1, t2) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun x -> str (value_to_string x);
        Initial  = fun (f, xs) -> pp_location_term "initial" (f, xs);
        VarTerm = fun x -> str x;
        QuantTerm = fun (q_kind, v, t_set, t_cond) ->
            blo0 [ str ("("^(AST.quant_kind_to_str q_kind)^" "); str v; str " in "; t_set; str " with "; t_cond; str ")" ];
        LetTerm = fun (v, t1, t2) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
        DomainTerm = fun tyname -> str (Signature.type_to_string tyname);
    } t

let rec pp_rule (gctx as GlobalCtx _)  (R : RULE) =
    let sign = (get_global_ctx' gctx).signature
    let (pp_app_term, pp_term) = (pp_app_term sign, pp_term gctx)
    rule_induction pp_term {
        S_Updates = fun U ->
                        let pp_elem ((f, xs), t) = blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] (xs >>| fun x -> str (value_to_string x))); str ") := "; (pp_term t) ]
                        let L = Set.toList U >>| pp_elem
                        blo0 [ str "{"; line_brk; blo2 ( pp_list [line_brk] L); line_brk; str "}" ];
        UpdateRule = fun ((f, ts), t) -> blo0 [ pp_app_term (Signature.FctName f, ts); str " := "; t ];
        CondRule = fun (G, R1, R2) -> blo0 ( str "if " :: G:: str " then " :: line_brk :: blo2 [ R1 ] :: line_brk ::
                                             (if R2 <> str "skip" then [ str "else "; line_brk; blo2 [ R2 ]; line_brk; str "endif" ] else [ str "endif"]) );
        ParRule = fun Rs -> if Rs <> [] then blo0 [ str "par"; line_brk; blo2 ( pp_list [line_brk] Rs); line_brk; str "endpar" ] else str "skip";
        SeqRule = fun Rs -> blo0 [ str "seq"; line_brk; blo2 (pp_list [line_brk] Rs); line_brk; str "endseq" ];
        IterRule = fun R' -> blo0 [ str "iterate "; line_brk; blo2 [ R' ]; line_brk; str "enditerate" ];
        LetRule = fun (v, t, R) -> blo0 [ str "let "; str v; str " = "; t; line_brk; str "in "; R; line_brk; str "endlet" ];
        ForallRule = fun (v, t_set, t_filter, R) -> blo0 [ str "forall "; str v; str " in "; t_set; str " with "; t_filter; str " do"; line_brk; blo2 [ R ]; line_brk; str "endforall" ];
        MacroRuleCall = fun (r, ts) -> blo0 [ str r; str "["; blo0 (pp_list [str",";brk 1] ts); str "]" ];
    } R


let name_to_string t    = t |> pp_name |> PrettyPrinting.toString 80

let term_to_string sign t    = t |> pp_term sign |> PrettyPrinting.toString 80
let rule_to_string sign t    = t |> pp_rule sign |> PrettyPrinting.toString 80


//--------------------------------------------------------------------

type ENV = Map<string, TERM * Signature.TYPE>

let empty : ENV =
    Map.empty

let defined_in (env : ENV) var =
    Map.containsKey var env

let get_env (env : ENV) (var : string) =
    Map.find var env

let add_binding (env : ENV) (var : string, t : TERM, ty : Signature.TYPE) =
    Map.add var (t, ty) env

//--------------------------------------------------------------------

let get_values S (ts : TERM list) : VALUE list option =    // only if all arguments are values
    List.fold ( function
                |   Some ts -> (fun t -> match get_term' S t with Value' v -> Some(v :: ts) | _ -> None)
                |   None -> (fun _ -> None) ) (Some []) (List.rev ts)

//--------------------------------------------------------------------

type CONTEXT = Set<TERM> // * S_UPDATE_MAP

//let empty_context : CONTEXT = (Set.empty, Map.empty)
//let add_cond (G : TERM) (C : CONTEXT as (C1, C2)) = (Set.add G C1, C2)
let add_cond (G : TERM) (C : CONTEXT) = (Set.add G C)
//let add_intp (f : string, xs : VALUE list, t : TERM) (C : CONTEXT as (C1, C2)) = (C1, SymbUpdates.add_s_update C2 ((f, xs), t))

let interpretation_in_context (S : SymbState.S_STATE) (C : CONTEXT) (f : Signature.NAME) (xs : VALUE list) =
    SymbState.interpretation S f xs
(*
    match f with
    |   Signature.FctName f_name ->
        match Map.tryFind f_name (snd C) with
        |   Some f_table ->
            match Map.tryFind xs f_table with
            |   Some t -> t
            |   None -> SymbState.interpretation S f xs
        |   None -> SymbState.interpretation S f xs
    |   _ -> SymbState.interpretation S f xs
*)
//--------------------------------------------------------------------
//
//  symbolic evaluator
//  
//  through the symbolic evaluation functions:
//  - S or gctx  stands for global context
//  - env        stands for variable environment
//  - C or lctx  stands for local context
//
//--------------------------------------------------------------------

let s_not S t =
    match get_term' S t with
    |   Value' (BOOL b) -> Value S (BOOL (not b))
    |   _ -> AppTerm S (Signature.FctName "not", [t])

let s_equals S (t1, t2) =
    match (get_term' S t1, get_term' S t2) with
    |   (Value' x1, Value' x2) -> Value S (BOOL (x1 = x2))
    |   (_, _) -> AppTerm S (Signature.FctName "=", [t1; t2])

let s_and S (phi1, phi2)=
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> Value S FALSE
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> Value S FALSE
    |   (_, Value' (BOOL true)) -> phi1
    |   (phi1', phi2') -> if phi1 = phi2 then phi1 else AppTerm S (Signature.FctName "and", [phi1; phi2])

let s_or S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> Value S TRUE
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> Value S TRUE
    |   (_, _) -> if phi1 = phi2 then phi1 else AppTerm S (Signature.FctName "or", [phi1; phi2])

let s_xor S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> s_not S phi2
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> s_not S phi1
    |   (_, _) -> if phi1 = phi2 then Value S FALSE else AppTerm S (Signature.FctName "xor", [phi1; phi2])

let s_implies S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL b1), _) -> s_or S (Value S (BOOL (not b1)), phi2)
    |   (_, Value' (BOOL b2)) -> s_or S (s_not S phi1, Value S (BOOL b2))
    |   (_, _) -> if phi1 = phi2 then Value S TRUE else AppTerm S (Signature.FctName "implies", [phi1; phi2])

let s_iff S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> s_not S phi2
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> s_not S phi1
    |   (_, Value' (BOOL true)) -> phi1
    |   (_, _) -> if phi1 = phi2 then Value S TRUE else AppTerm S (Signature.FctName "iff", [phi1; phi2])

//--------------------------------------------------------------------

let ctx_condition S C =
    List.fold (fun a -> fun b -> s_and S (a, b)) (Value S TRUE) (Set.toList C)

// let smt_assert_update (S, env, C) ((f, xs), t) =
//     smt_assert (signature_of S) TopLevel.smt_ctx (s_equals (AppTerm (FctName f, xs >>| Value), t))

(*
let ctx_to_smt (S, env, C) =
    // !!!! tbd: if there is any initialisation in S0, it should be mapped as well: for the moment there is none
    // !!!! List.map (fun ((f, xs), t) -> smt_assert_update (S, env, C) (f, xs), t) (Map.toList C.U) |> ignore
    Set.map (fun phi -> smt_assert (signature_of S) TopLevel.smt_ctx phi) C |> ignore
*)

let with_extended_path_cond sign (G : TERM) eval_fct (S : SymbState.S_STATE, env : ENV, C : CONTEXT) =
    SmtInterface.smt_solver_push TopLevel.smt_ctx
    SmtInterface.smt_assert sign TopLevel.smt_ctx G
    let result = eval_fct () (S, env, add_cond G C)
    SmtInterface.smt_solver_pop TopLevel.smt_ctx
    result

//--------------------------------------------------------------------

let smt_formula_is_true (S : GLOBAL_CTX) (C : SmtInterface.SMT_CONTEXT) (phi : TERM) =
    let get_type = get_type S
    if get_type phi = Signature.Boolean
    then match smt_map_term sign C phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check ((!C.ctx).MkNot be) = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_true: error converting Boolean term (term = %s)" (term_to_string S phi))
    else failwith (sprintf "'smt_formula_is_true' expects a Boolean term, %s found instead " (term_to_string S phi))

let smt_formula_is_false (S : GLOBAL_CTX) (C : SmtInterface.SMT_CONTEXT) (phi : TERM) =
    let get_type = get_type S
    if get_type phi = Signature.Boolean
    then match smt_map_term sign C phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check be = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_false: error converting Boolean term (term = %s)" (term_to_string S phi))
    else failwith (sprintf "'smt_formula_is_false' expects a Boolean term, %s found instead " (term_to_string S phi))

let rec smt_eval_formula (phi : TERM) (S : GLOBAL_CTX, env, C) =
    // precondition: term_type sign phi = Boolean
    let sign = signature_of S
    if !trace > 0 then fprintf stderr "smt_eval_formula(%s) -> " (term_to_string S phi)
    let phi = expand_term phi (S, env, C)
    let result =
        if (!SymbEval.use_smt_solver && smt_formula_is_true S TopLevel.smt_ctx phi)
        then Value S (BOOL true)
        else if (!SymbEval.use_smt_solver && smt_formula_is_true S TopLevel.smt_ctx (s_not S phi))
        then Value S (BOOL false)
        else phi
    // old version before using solver push and pop: // smt_solver_reset TopLevel.smt_ctx
    if !trace > 0 then fprintf stderr "%s\n" (term_to_string S result)
    result

and expand_term t (S : GLOBAL_CTX, env, C) : TERM =
    let (s_state, get_type) = (s_state_of S, get_type S)
    term_induction S (fun x -> x) {
        Value   = fun x (S, env, C) -> Value S x;
        Initial = fun (f, xs) (S, env, C) -> Initial S (f, xs)
        AppTerm = fun (f, ts) (S, env, C) ->
            let sign = signature_of S
            match f with
            |   Signature.FctName fct_name ->
                    // static functions that are not primitive functions (i.e. not in the 'background') are expanded like macros
                    if Signature.fct_kind fct_name sign = Signature.Static && not (Map.containsKey fct_name Background.state) then
                        let (formals, body) =
                            try Map.find fct_name (TopLevel.macros ())     // !!! should not use global TopLevel.macros
                            with _ -> failwith (sprintf "SymbEval.expand_term: definition of static function '%s' not found in macros database" fct_name)
                        let ts = ts >>| fun t -> t (S, env, C)
                        let env' =
                            List.fold2 (fun env' formal arg -> add_binding env' (formal, s_eval_term arg (S, env, C), get_type arg)) env formals ts
                        s_eval_term body (S, env', C)
                    else AppTerm S (f, ts >>| fun t -> t (S, env, C))
            |   _ -> AppTerm S (f, ts >>| fun t -> t (S, env, C));
        CondTerm  = fun (G, t1, t2) (S, env, C) -> CondTerm S (G (S, env, C), t1 (S, env, C), t2 (S, env, C));
        VarTerm   = fun v           (S, env, C) -> fst (get_env env v);
        QuantTerm = fun (q_kind, v, t_set, t_cond) (S, env, C) -> expand_quantifier (q_kind, v, t_set, t_cond) (S, env, C);
        LetTerm   = fun (v, t1, t2) (S, env, C) ->
                        let t1_val = t1 (S, env, C)
                        t2 (S, add_binding env (v, t1_val, get_type t1_val), C);
        DomainTerm = fun dom (S, env, C) -> match SymbState.enum_finite_type dom s_state with Some xs -> Value S (SET xs) | _ -> failwith (sprintf "SymbEval.expand_term: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))
    } t (S, env, C)

and expand_quantifier (q_kind, v, t_set, t_cond) (S, env, C) : TERM =
    let t_set = t_set (S, env, C)
    let t_set_type = get_type S t_set
    let elem_type =
        match t_set_type with
        |   Signature.Powerset tyname -> tyname
        |   _ -> failwith (sprintf "SymbEval.expand_quantifier: expected a set or domain type, %s found instead" (Signature.type_to_string t_set_type))
    match get_term' S t_set with
    |   Value' (Background.SET xs) ->
            let eval_instance x = t_cond (S, add_binding env (v, Value S x, elem_type), C)
            let t_conds = List.map eval_instance (Set.toList xs)
            match q_kind with
            |   AST.Forall -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_and S (t_accum, t1)) (Value S (BOOL true))  t_conds
            |   AST.Exist  -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_or  S (t_accum, t1)) (Value S (BOOL false)) t_conds
            |   AST.ExistUnique -> failwith "SymbEval.expand_quantifier: 'ExistUnique' not implemented"
    |   x -> failwith (sprintf "SymbEval.expand_quantifier: not a set (%A): %A v" t_set x)

and try_case_distinction_for_term_with_finite_range (S, env, C) (f : Signature.FCT_NAME) (ts0 : TERM list) : TERM =
    let generate_cond_term (t, cases : (VALUE * TERM) list) =
        let mkCondTerm (G, t1, t2) = CondTerm S (G, t1, t2)
        let mkEq t1 t2 = s_equals S (t1, t2)
        let rec mk_cond_term (cases : (VALUE * TERM) list) =
            match cases with
            |   [] -> failwith "mk_cond_term: empty list of cases"
            |   [(t1, t2)] -> t2
            |   (t1, t2) :: cases' ->
                    let eq_term  = s_eval_term (mkEq t (Value S t1)) (S, env, C)
                    match get_term' S eq_term with
                    |   Value' (BOOL true) -> t2
                    |   Value' (BOOL false) -> mk_cond_term cases'
                    |   _ -> mkCondTerm (eq_term, t2, mk_cond_term cases')
        mk_cond_term cases
    let make_case_distinction (t : TERM) (elem_term_pairs : (VALUE * TERM) list) =
        if List.isEmpty elem_term_pairs
        then failwith (sprintf "SymbEval.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string S t))
        generate_cond_term (t, elem_term_pairs)
    let rec F past_args = function
    |   [] -> AppTerm S (Signature.FctName f, List.rev past_args)
    |   t1 :: ts' ->
            let t1 = s_eval_term t1 (S, env, C)
            match get_term' S t1 with
            |   Value' x1 -> F (Value S x1 :: past_args) ts'
            |   _ ->
                    match (try SymbState.enum_finite_type (get_type S t1) (s_state_of S) with _ -> None) with
                    |   None ->
                            failwith (sprintf "arguments of dynamic function '%s' must be fully evaluable for unambiguous determination of a location\n('%s' found instead)"
                                        f (term_to_string S (AppTerm S (Signature.FctName f, ts0))))
                    |   Some elems ->
                            make_case_distinction t1 (List.map (fun elem -> (elem, F (Value S elem :: past_args) ts')) (Set.toList elems))
    let result = F [] ts0
    result

and eval_app_term (S, env : ENV, C) (fct_name, ts) : TERM = 
    let sign = signature_of S
    let with_extended_path_cond = with_extended_path_cond sign
    //if !trace > 0 then fprintfn stderr "|signature|=%d | eval_app_term %s%s\n" (Map.count sign) (spaces !level) (term_to_string sign (AppTerm (fct_name, [])))
    let rec F (ts_past : TERM list) ts =
        match ts with
        |   t :: ts_fut ->
                let t = t (S, env, C)
                match get_term' S t with
                |   Value' x1             -> F (t :: ts_past) ts_fut
                |   Initial'  (f, xs)     -> F (t :: ts_past) ts_fut
                |   CondTerm' (G1, t11, t12) -> s_eval_term_ (CondTerm S (G1, F ts_past ((fun (S, env, C) -> t11) :: ts_fut), F ts_past ((fun (S, env, C) -> t12) :: ts_fut))) (S, env, C)
                |   LetTerm'  (v, t1, t2) -> F (t :: ts_past) ts_fut
                |   VarTerm'  v           -> F (t :: ts_past) ts_fut
                |   AppTerm'  _           -> F (t :: ts_past) ts_fut
                |   QuantTerm' _          -> failwith "SymbEval.eval_app_term: QuantTerm not implemented"
                |   DomainTerm' _         -> failwith "SymbEval.eval_app_term: DomainTerm not implemented"
        |   [] ->
                match (fct_name, List.rev ts_past) with
                |   (Signature.FctName "and", [ t1; t2 ]) -> s_and S (t1, t2)
                |   (Signature.FctName "or", [ t1; t2 ])  -> s_or S (t1, t2)
                |   (Signature.FctName "xor", [ t1; t2 ]) -> s_xor S (t1, t2)
                |   (Signature.FctName "implies", [ t1; t2 ]) -> s_implies S (t1, t2)
                |   (Signature.FctName "iff", [ t1; t2 ]) -> s_iff S (t1, t2)
                |   (Signature.FctName "=", [ t1; t2 ])   -> s_equals S (t1, t2)
                |   (Signature.FctName f, ts)    ->
                    match get_values S ts with
                    |   Some xs -> interpretation_in_context (s_state_of S) C fct_name xs
                    |   None ->
                        match (Signature.fct_kind f sign) with
                        |   Signature.Static -> 
                                match Signature.fct_type f sign with
                                |   (_, Signature.Boolean) ->
                                        let t = AppTerm S (Signature.FctName f, ts)
                                        if Set.contains t C                  then Value S TRUE
                                        else if Set.contains (s_not S t) C   then Value S FALSE
                                        else smt_eval_formula t (S, env, C)
                                | _ -> AppTerm S (Signature.FctName f, ts)
                        |   Signature.Controlled ->  s_eval_term (try_case_distinction_for_term_with_finite_range (S, env, C) f ts) (S, env, C)
                        |   other_kind -> failwith (sprintf "SymbEval.eval_app_term: kind '%s' of function '%s' not implemented" (Signature.fct_kind_to_string other_kind) f)
                |   (Signature.UndefConst, _)    -> Value S (Background.UNDEF)
                |   (Signature.BoolConst b, _)   -> Value S (BOOL b)
                |   (Signature.IntConst i, _)    -> Value S (INT i)
                |   (Signature.StringConst s, _) -> Value S (STRING s)
    match (fct_name, ts) with
    |   (Signature.FctName "and", [ t1; t2 ]) ->
            let t1 = t1 (S, env, C)
            match get_term' S t1 with
            |   Value' (BOOL false) -> Value S (BOOL false)
            |   Value' (BOOL true)  -> t2 (S, env, C)        // alternative: with_extended_path_cond t1' (fun _ -> t2) (S, env, C)
            |   t1' ->
                let t2 = t2 (S, env, C)
                match get_term' S t2 with
                |   Value' (BOOL false) -> Value S (BOOL false)
                |   Value' (BOOL true) -> t1    // with_extended_path_cond t2' (fun _ -> t1) (S, env, C)
                |   t2' -> if t1' = t2' then t1 else F [] [(fun _ -> t1); (fun _ -> t2)]
    |   (Signature.FctName "or", [ t1; t2 ]) ->
            match get_term' S (t1 (S, env, C)) with
            |   Value' (BOOL true) -> Value S (BOOL true)
            |   Value' (BOOL false) -> t2 (S, env, C)
            |   t1' ->
                match get_term' S (t2 (S, env, C)) with
                |   Value' (BOOL true) -> Value S (BOOL true)
                |   Value' (BOOL false) -> make_term S t1'
                |   t2' -> if t1' = t2' then make_term S t1' else F [] [(fun _ -> make_term S t1'); (fun _ -> make_term S t2')]
    |   (Signature.FctName "implies", [ t1; t2 ]) ->
            match get_term' S (t1 (S, env, C)) with
            |   Value' (BOOL false) -> Value S (BOOL true)
            |   t1' as Value' (BOOL true)  -> t2 (S, env, C)       // with_extended_path_cond t1' (fun _ -> t2) (S, env, C)
            |   t1' ->
                match get_term' S (t2 (S, env, C)) with
                |   Value' (BOOL false) -> s_not S (make_term S t1')
                |   Value' (BOOL true)  -> Value S (BOOL true)
                |   t2' -> if t1' = t2' then Value S (BOOL true) else F [] [(fun _ -> make_term S t1'); (fun _ -> make_term S t2')]
    |   (Signature.FctName "iff", [ t1; t2 ]) ->
        match get_term' S (t1 (S, env, C)) with
        |   Value' (BOOL false) -> s_not S (t2 (S, env, C))
        |   Value' (BOOL true)  -> t2 (S, env, C)
        |   t1' ->
            match get_term' S (t2 (S, env, C)) with
            |   Value' (BOOL false) -> s_not S (make_term S t1')
            |   Value' (BOOL true)  -> make_term S t1'
            |   t2' -> if t1' = t2' then Value S (BOOL true) else F [] [(fun _ -> make_term S t1'); (fun _ -> make_term S t2')]
    |   (Signature.FctName "=", [ t1; t2 ]) ->
        match get_term' S (t1 (S, env, C)) with
        |   t1' as Value' x1 ->
            match get_term' S (t2 (S, env, C)) with
            |   Value' x2 -> Value S (BOOL (x1 = x2))
            |   t2' -> F [] [(fun _ -> make_term S t1'); fun _ -> make_term S t2']
        |   t1' -> F [] [(fun _ -> make_term S t1'); fun _ -> t2 (S, env, C)]
    |   _ ->
    F [] ts

and eval_cond_term (S, env : ENV, C) (G, t1, t2) = 
    let (sign, get_type) = (signature_of S, get_type S)
    let with_extended_path_cond = with_extended_path_cond sign
    let term_to_string = term_to_string S
    match get_term' S (G (S, env, C)) with
    |   Value' (BOOL true)  -> t1 (S, env, C)
    |   Value' (BOOL false) -> t2 (S, env, C)
    |   CondTerm' (G', G1, G2) ->
            if get_type G1 <> Signature.Boolean || get_type G2 <> Signature.Boolean
            then failwith (sprintf "eval_cond_term: '%s' and '%s' must be boolean terms" (term_to_string G1) (term_to_string G2))
            else let t1_G'     = t1 (S, env, add_cond G' (add_cond G1 C))
                 let t1_not_G' = t1 (S, env, add_cond (s_not S G') (add_cond G1 C))
                 let t2_G'     = t2 (S, env, add_cond G' (add_cond G2 C))
                 let t2_not_G' = t2 (S, env, add_cond (s_not S G') (add_cond G2 C))
                 s_eval_term (CondTerm S (G', CondTerm S (G1, t1_G', t2_G'), CondTerm S (G2, t1_not_G', t2_not_G'))) (S, env, C)
    |   G ->    let G = make_term S G
                if (!trace > 1)
                then fprintfn stderr "\n%sctx_condition: %s" (spaces !level) (term_to_string (ctx_condition S C))
                if not SymbEval.simplify_cond then
                    // version 1: no simplification whatsoever (inefficient, but useful for debugging)
                    CondTerm S (G, t1 (S, env, add_cond G C), t2 (S, env, add_cond (s_not S G) C))
                else 
                    // version 2: with simplification
                    if Set.contains G C
                    then t1 (S, env, C)
                    else if Set.contains (s_not S G) C
                    then t2 (S, env, C)
                    else let (t1', t2') = (t1 (S, env, add_cond G C), t2 (S, env, add_cond (s_not S G) C))
                         if t1' = t2' then t1'
                         else let sign = signature_of S
                              if not !SymbEval.use_smt_solver
                              then  let t1' = s_eval_term t1' (S, env, add_cond G C)
                                    let t2' = s_eval_term t2' (S, env, add_cond (s_not S G) C)
                                    if t1' = t2' then t1' else CondTerm S (G, t1', t2')
                              else  let t1' = with_extended_path_cond G         (fun _ -> s_eval_term t1') (S, env, C)  
                                    let t2' = with_extended_path_cond (s_not S G) (fun _ -> s_eval_term t2') (S, env, C)  
                                    if t1' = t2' then t1' else CondTerm S (G, t1', t2')

and eval_let_term (S, env, C) (v, t1, t2) =
    let t1 = t1 (S, env, C)
    t2 (S, add_binding env (v, t1, get_type S t1), C)

and s_eval_term_ (t : TERM) (S, env, C) =
    term_induction S (fun x -> x) {
        Value      = fun x _ -> Value S x;
        Initial    = fun (f, xs) _ -> Initial S (f, xs);
        AppTerm    = fun (f, ts) (S, env, C) -> eval_app_term (S, env, C) (f, ts)
        CondTerm   = fun (G, t1, t2) (S, env, C) -> eval_cond_term (S, env, C) (G, t1, t2);
        VarTerm    = fun v -> fun (S, env, _) -> fst (get_env env v);
        QuantTerm  = fun (q_kind, v, t_set, t_cond) (S, env, C) -> expand_quantifier (q_kind, v, t_set, t_cond) (S, env, C);
        LetTerm    = fun (v, t1, t2) -> fun (S, env, _) -> eval_let_term (S, env, C) (v, t1, t2) 
        DomainTerm = fun dom -> fun (S, env, C) -> match SymbState.enum_finite_type dom (s_state_of S) with Some xs -> Value S (SET xs) | None -> failwith (sprintf "SymbEval.s_eval_term_: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))
    } t (S, env, C)

and s_eval_term (t : TERM) (S : GLOBAL_CTX, env : ENV, C) : TERM =
    let sign = signature_of S
    let t = s_eval_term_ t (S, env, C)
    if get_type S t = Signature.Boolean
    then    match get_term' S t with
            |   Value' (BOOL _)  -> t
            |   _ -> smt_eval_formula t (S, env, C)
    else    t
