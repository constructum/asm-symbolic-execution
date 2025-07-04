module DAG

//--------------------------------------------------------------------

open System.Diagnostics
open System.Collections.Generic

open Common
open PrettyPrinting
open Background

//--------------------------------------------------------------------

let trace = ref 0
let level = ref 0
let module_name = "DAG"

let rec spaces level = if level = 0 then "" else "    " + spaces (level-1)
let rec indent level ppt = if level = 0 then ppt else blo4 [ indent (level-1) ppt ]

//--------------------------------------------------------------------

type FUNCTION_INTERPRETATION =
|   Constructor of (VALUE list -> VALUE)
|   StaticSymbolic of (TERM list -> TERM)       // rewriting rules for term simplification, e.g. for boolean functions 
|   StaticBackground of (VALUE list -> VALUE)
|   StaticUserDefined of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledInitial of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledUninitialized
|   Derived of (string list * TERM)             // string list is the list of arguments, TERM is the body of the derived function

and FUNCTION' = {
    fct_id   : int;
    fct_name : string;
    fct_kind : Signature.FCT_KIND;
    // fct_type : (Signature.TYPE list * Signature.TYPE);   // !!! to be implemented together with monomorphization
    fct_interpretation : FUNCTION_INTERPRETATION
}
and FCT_ID =
|   FctId of int

and TERM_ATTRS = {
    term_id   : int
    term_type : Signature.TYPE
    smt_expr  : SmtInterface.SMT_EXPR option ref  // for SMT solver
}

and GLOBAL_CTX' = {
    signature     : Signature.SIGNATURE
    initial_state : State.STATE         // use only for initial state in this module, never use '_dynamic' field - also the second elem. of _dynamic_initial seems not to be used !
    macros        : MACRO_DB
    rules         : RULES_DB
    invariants    : Map<string, TERM>   // Added invariants field
    fctIdxTable   : Dictionary<string, int>
    fctTable      : ResizeArray<FUNCTION'>
    termIdxTable  : Dictionary<TERM', TERM>
    termTable     : ResizeArray<TERM' * TERM_ATTRS>
    TRUE_         : TERM option ref
    FALSE_        : TERM option ref
    AND_          : FCT_ID option ref
    OR_           : FCT_ID option ref
    NOT_          : FCT_ID option ref
}

and GLOBAL_CTX = GlobalCtx of int

and GLOBAL_CTX_TABLE = ResizeArray<GLOBAL_CTX'>

and TERM' =
|   Value'      of (VALUE)                  // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   Initial'    of (FCT_ID * VALUE list)    // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   AppTerm'    of (FCT_ID * TERM list)
|   CondTerm'   of (TERM * TERM * TERM)
|   VarTerm'    of (string)
|   QuantTerm'  of (AST.QUANT_KIND * string * TERM * TERM)
|   LetTerm'    of (string * TERM * TERM)
|   DomainTerm' of Signature.TYPE                  // AsmetaL construct: finite type (e.g. enum, abstract, subsetof) used as finite set
//  | TupleTerm   of 'annotation * ('annotation ANN_TERM list)

and TERM = Term of int

and RULE =
| S_Updates of Set<(Signature.FCT_NAME * VALUE list) * TERM>  //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
| UpdateRule of (Signature.FCT_NAME * TERM list) * TERM
| CondRule of TERM * RULE * RULE
| ParRule of RULE list
| SeqRule of RULE list
| IterRule of RULE
| LetRule of string * TERM * RULE
| ForallRule of string * TERM * TERM * RULE
| MacroRuleCall of Signature.RULE_NAME * TERM list

and MACRO_DB = Map<Signature.FCT_NAME, string list * TERM>     // for derived functions ("macros")
and RULES_DB = Map<Signature.RULE_NAME, string list * RULE>   // for rule macros

and LOCATION = string * VALUE list
and S_UPDATE = LOCATION * TERM
and S_UPDATE_SET = Set<S_UPDATE>
and S_UPDATE_MAP = Map<string, Map<VALUE list, TERM>>

let global_ctxs = new ResizeArray<GLOBAL_CTX'>()


let rec get_fct_id (GlobalCtx gctx_id) (fct_name : string) : FCT_ID =
    let ctx = global_ctxs.[gctx_id]
    if ctx.fctIdxTable.ContainsKey fct_name then
        FctId ctx.fctIdxTable.[fct_name]
    else
        failwith (sprintf "DAG.get_fct_id: function '%s' not found in global context #%d" fct_name gctx_id)

and get_function' (GlobalCtx gctx_id) (FctId fct_id : FCT_ID) : FUNCTION' =
    let fctTable = global_ctxs.[gctx_id].fctTable
    if fct_id < fctTable.Count then
        fctTable.[fct_id]
    else
        failwith (sprintf "DAG.get_function': function with id #%d not found in global context #%d" fct_id gctx_id)

and inline make_term_with_opt_type (GlobalCtx gctx_id) (t' : TERM') (opt_ty : Signature.TYPE option) : TERM =
    let ctx = global_ctxs.[gctx_id]
    if ctx.termIdxTable.ContainsKey t' then
        ctx.termIdxTable.[t']
    else
        let term_id = ctx.termIdxTable.Count
        let attrs = {
            term_id   = term_id
            term_type = match opt_ty with None -> compute_type (GlobalCtx gctx_id) t' | Some ty -> ty
            smt_expr  = ref None
        }
        ctx.termIdxTable.[t'] <- Term term_id
        ctx.termTable.Add (t', attrs)
        Term term_id

and inline make_term_with_type C (t' : TERM') ty : TERM = make_term_with_opt_type C t' (Some ty)
and inline make_term C (t' : TERM') : TERM              = make_term_with_opt_type C t' None

and inline get_term'_attrs (gctx: GLOBAL_CTX) (Term term_id) =
    let (GlobalCtx gctx_id) = gctx
    let ctx = global_ctxs.[gctx_id]
    if term_id < ctx.termTable.Count then
        ctx.termTable.[term_id]
    else
        failwith (sprintf "get_term': term %d not found in context %d" term_id gctx_id)

and inline get_term' (gctx: GLOBAL_CTX) (Term term_id) = get_term'_attrs gctx (Term term_id) |> fst
and inline get_attrs (gctx: GLOBAL_CTX) (Term term_id) = get_term'_attrs gctx (Term term_id) |> snd

and compute_type (gctx as GlobalCtx gctx_id) (t' : TERM') : Signature.TYPE =
    let (sign, get_type) = (global_ctxs.[gctx_id].signature, get_type gctx)
    match t' with
    |   Value' x -> Background.type_of_value sign x
    |   Initial' (f, xs) -> let f_name = (get_function' gctx f).fct_name in Signature.match_fct_type f_name (xs >>| Background.type_of_value sign) (Signature.fct_types f_name sign)
    //!!!|   AppTerm' (Signature.UndefConst, _)    -> Signature.Undef
    //!!!|   AppTerm' (Signature.BoolConst _, _)   -> Signature.Boolean
    //!!!|   AppTerm' (Signature.IntConst _, _)    -> Signature.Integer
    //!!!|   AppTerm' (Signature.StringConst _, _) -> Signature.String
    |   AppTerm' (f, ts)    -> let f_name = (get_function' gctx f).fct_name in Signature.match_fct_type f_name (ts >>| get_type) (Signature.fct_types f_name sign)
    |   CondTerm' (G, t1, t2) -> if get_type t1 = get_type t2 then get_type t1 else failwith "compute_type: types of branches of conditional term do not match"
    |   VarTerm' v -> failwith (sprintf "compute_type: variable '%s' does not have a type" v)
    |   QuantTerm' (_, _, t_set, _) -> Signature.Boolean
    |   LetTerm' (_, t1, t2) -> get_type t2
    |   DomainTerm' tyname -> Signature.Powerset tyname

and get_type (gctx as GlobalCtx gctx_id) (t as Term term_id : TERM) : Signature.TYPE =
    let termTable = global_ctxs.[gctx_id].termTable
    if term_id < termTable.Count then
        (snd termTable.[term_id]).term_type
    else
        failwith (sprintf "get_type: term %A not found in context %d" (get_term' gctx t) gctx_id)

and get_smt_expr (gctx as GlobalCtx gctx_id) (t as Term term_id : TERM) : SmtInterface.SMT_EXPR option =
    let termTable = global_ctxs.[gctx_id].termTable
    if term_id < termTable.Count then
        !(snd termTable.[term_id]).smt_expr
    else
        failwith (sprintf "get_type: term %A not found in context %d" (get_term' gctx t) gctx_id)

and set_smt_expr (gctx as GlobalCtx gctx_id) (t as Term term_id : TERM) (smt_expr : SmtInterface.SMT_EXPR) =
    let termTable = global_ctxs.[gctx_id].termTable
    if term_id < termTable.Count then
        (snd termTable.[term_id]).smt_expr := Some smt_expr
    else
        failwith (sprintf "set_smt_expr: term %A not found in context %d" (get_term' gctx t) gctx_id)

and inline Value gctx x = make_term gctx (Value' x)
and inline Initial gctx (f, xs) = make_term gctx (Initial' (f, xs))
and inline AppTerm gctx (f, ts) = make_term gctx (AppTerm' (f, ts))
and inline CondTerm gctx (G, t1, t2) = make_term gctx (CondTerm' (G, t1, t2))
and inline VarTerm gctx v = make_term gctx (VarTerm' v)
and inline QuantTerm gctx (q_kind, v, t_set, t_cond) = make_term gctx (QuantTerm' (q_kind, v, t_set, t_cond))
and inline LetTerm gctx (x, t1, t2) = make_term gctx (LetTerm' (x, t1, t2))
and inline DomainTerm gctx tyname = make_term gctx (DomainTerm' tyname)    
and inline TRUE (GlobalCtx gctx_id) = !global_ctxs.[gctx_id].TRUE_ |> Option.get
and inline FALSE (GlobalCtx gctx_id) = !global_ctxs.[gctx_id].FALSE_ |> Option.get
and inline AND (GlobalCtx gctx_id) = !global_ctxs.[gctx_id].AND_ |> Option.get
and inline OR (GlobalCtx gctx_id) = !global_ctxs.[gctx_id].OR_ |> Option.get
and inline NOT (GlobalCtx gctx_id) = !global_ctxs.[gctx_id].NOT_ |> Option.get

and convert_term (C : GLOBAL_CTX) (t : AST.TYPED_TERM) : TERM =
    AST.ann_term_induction (fun x -> x) {
        Value      = fun (_, x) -> Value C x;
        Initial    = fun (_, (f, xs)) -> Initial C (get_fct_id C f, xs);
        AppTerm    = fun (ty, (f, ts)) ->
                        match f with
                        |   Signature.UndefConst    -> make_term_with_type C (Value' UNDEF) ty
                        |   Signature.BoolConst b   -> make_term_with_type C (Value' (BOOL b)) ty
                        |   Signature.IntConst i    -> make_term_with_type C (Value' (INT i)) ty
                        |   Signature.StringConst s -> make_term_with_type C (Value' (STRING s)) ty
                        |   Signature.FctName f ->
                                let f_id = get_fct_id C f
                                try
                                    AppTerm C (f_id, ts)
                                with ex as Signature.Error (Signature.NoMatchingFunctionType (f, tys)) ->
                                    fprintf stderr "convert_term: in term %A\n" (AppTerm C (f_id, ts))
                                    raise ex
        CondTerm   = fun (_, (G, t1, t2)) -> CondTerm C (G, t1, t2);
        VarTerm    = fun (ty, v) -> make_term_with_type C (VarTerm' v) ty
        QuantTerm  = fun (ty, (q_kind, v, t_set, t_cond)) -> fprintf stderr "QuantTerm type: %s" (Signature.type_to_string ty); QuantTerm C (q_kind, v, t_set, t_cond);
        LetTerm    = fun (_, (v, t1, t2)) -> LetTerm C (v, t1, t2);
        DomainTerm = fun (_, D) -> DomainTerm C D;
    } t

and convert_rule (C : GLOBAL_CTX) (R : AST.RULE) : RULE =
    AST.rule_induction (convert_term C) {
        UpdateRule = fun ((f, ts), t_rhs) -> UpdateRule ((f, ts), t_rhs);
        CondRule   = fun (G, R1, R2) -> CondRule (G, R1, R2);
        ParRule    = fun Rs -> ParRule Rs;
        SeqRule    = fun Rs -> SeqRule Rs;
        IterRule   = fun R' -> IterRule R';
        LetRule    = fun (v, t1, R') -> LetRule (v, t1, R');
        MacroRuleCall = fun (r, args) -> MacroRuleCall (r, args);
        ForallRule = fun (v, t_set, G, R') -> ForallRule (v, t_set, G, R');
        S_Updates  = fun upds -> S_Updates (Set.map (fun ((f, xs), t_rhs) -> (f, xs), convert_term C t_rhs) upds)
    } R

and convert_macros (C : GLOBAL_CTX) (rdb : AST.MACRO_DB) : MACRO_DB =
    Map.map (fun _ (args, t) -> (args, convert_term C t)) rdb

and convert_rules (C : GLOBAL_CTX) (rdb : AST.RULES_DB) : RULES_DB =
    Map.map (fun _ (args, R) -> (args, convert_rule C R)) rdb

and new_global_ctx (sign : Signature.SIGNATURE, initial_state : State.STATE, macros : AST.MACRO_DB, rules : AST.RULES_DB, invariants : Map<string, AST.TYPED_TERM>) : GLOBAL_CTX =
    let ctx_id = global_ctxs.Count
    let new_ctx = {
        signature     = sign
        initial_state = initial_state
        macros        = Map.empty
        rules         = Map.empty
        invariants    = Map.empty
        fctIdxTable   = new Dictionary<string, int>(HashIdentity.Structural)
        fctTable      = new ResizeArray<FUNCTION'>()
        termIdxTable  = new Dictionary<TERM', TERM>(HashIdentity.Structural)
        termTable     = new ResizeArray<TERM' * TERM_ATTRS>()
        TRUE_         = ref None
        FALSE_        = ref None
        AND_          = ref None
        OR_           = ref None
        NOT_          = ref None
    }
    global_ctxs.Add new_ctx
    let extract_fct_interpretation_if_possible f_name =
        let f_kind = Signature.fct_kind f_name sign
        match Signature.fct_kind f_name sign with
        |   Signature.Constructor ->
                Some (Constructor (fun xs -> CELL (f_name, xs)))
        |   Signature.Static ->
                match initial_state._static |> Map.tryFind f_name with
                |   None -> fprintf stderr "Warning: static function '%s' is in signature, but is not defined - ignored\n" f_name; None
                |   Some fct_interp ->
                        if Set.contains f_name (Signature.fct_names Background.signature)   // background functions
                        then Some (StaticBackground fct_interp)
                        else Some (StaticUserDefined (fct_interp, None))   // second component is the AsmetaL definition to be filled in later
        |   Signature.Controlled ->
                match initial_state._dynamic_initial |> fst |> Map.tryFind f_name with
                |   Some fct_def -> Some (ControlledInitial (fct_def, None))
                |   None -> Some ControlledUninitialized
        |   Signature.Derived ->
                match macros |> Map.tryFind f_name with
                |   Some (args, body) -> Some (Derived (args, convert_term (GlobalCtx ctx_id) body))
                |   None -> failwith (sprintf "Warning: derived function '%s' is in signature, but is not defined - ignored\n" f_name)
        |   Signature.Monitored -> failwith (sprintf "DAG.new_global_ctx: monitored function '%s' - not implemented" f_name)
        |   Signature.Shared -> failwith (sprintf "DAG.new_global_ctx: shared function '%s' - not implemented" f_name)
        |   Signature.Out -> failwith (sprintf "DAG.new_global_ctx: out function '%s' - not implemented" f_name)
    sign |> Map.toList
        |> List.filter (fun (fct_name, _) -> Signature.is_function_name fct_name sign)
        |> List.map (fun (name, _) -> (name, extract_fct_interpretation_if_possible name))
        |> List.filter (function (_, None) -> false | _ -> true)
        |> Seq.iteri (fun i (name, opt_fct_interpretation) ->
            match opt_fct_interpretation with
            |   None -> ()
            |   Some fct_interpretation ->
                    let fct' : FUNCTION' = {
                        fct_id   = i;
                        fct_name = name;
                        fct_kind = Signature.fct_kind name sign;
                        // fct_type = Signature.fct_types name sign;   // !!! to be implemented together with monomorphization
                        fct_interpretation = fct_interpretation;
                    }
                    new_ctx.fctIdxTable.[name] <- i
                    new_ctx.fctTable.Add fct'
        )
    for i in 0..new_ctx.fctTable.Count - 1 do
        let fctInfo = new_ctx.fctTable.[i]
        match fctInfo.fct_interpretation with
        |   StaticUserDefined (fct_interp, None) ->
                match macros |> Map.tryFind fctInfo.fct_name with
                |   Some (args, body) ->
                        new_ctx.fctTable.[i] <- { fctInfo with fct_interpretation = StaticUserDefined (fct_interp, Some (args, convert_term (GlobalCtx ctx_id) body)) }
                |   None -> failwith (sprintf "cannot find definition of static function '%s'\n" fctInfo.fct_name)
        |   ControlledInitial (fct_interp, None) ->
                match macros |> Map.tryFind fctInfo.fct_name with
                |   Some (args, body) ->
                        new_ctx.fctTable.[i] <- { fctInfo with fct_interpretation = ControlledInitial (fct_interp, Some (args, convert_term (GlobalCtx ctx_id) body)) }
                |   None -> failwith (sprintf "cannot find initial definition of controlled function '%s'\n" fctInfo.fct_name)
        |   _ -> ()     // if not any of the above cases, do nothing (the entry of fctTable was already completely initialized)
    let new_ctx = {
        new_ctx with
            macros = convert_macros (GlobalCtx ctx_id) macros
            rules  = convert_rules (GlobalCtx ctx_id) rules
            invariants = Map.map (fun _ t -> convert_term (GlobalCtx ctx_id) t) invariants
        }
    global_ctxs.[ctx_id] <- new_ctx
    global_ctxs.[ctx_id].TRUE_  := Some (Value (GlobalCtx ctx_id) (BOOL true))
    global_ctxs.[ctx_id].FALSE_ := Some (Value (GlobalCtx ctx_id) (BOOL false))
    global_ctxs.[ctx_id].AND_   := Some (get_fct_id (GlobalCtx ctx_id) "and")
    global_ctxs.[ctx_id].OR_    := Some (get_fct_id (GlobalCtx ctx_id) "or")
    global_ctxs.[ctx_id].NOT_   := Some (get_fct_id (GlobalCtx ctx_id) "not")
    GlobalCtx ctx_id

and get_global_ctx' (GlobalCtx gctx_id : GLOBAL_CTX) : GLOBAL_CTX' =
    if gctx_id < global_ctxs.Count then
        global_ctxs.[gctx_id]
    else
        failwith (sprintf "get_global_ctx': context %d not found" gctx_id)

// and signature_of (GlobalCtx gctx_id) =
//     global_ctxs.[gctx_id].signature

and initial_state_of (GlobalCtx gctx_id) =
    global_ctxs.[gctx_id].initial_state

and macros_of (GlobalCtx gctx_id) =
    global_ctxs.[gctx_id].macros

and rules_of (GlobalCtx gctx_id) =
    global_ctxs.[gctx_id].rules

and invariants_of (GlobalCtx gctx_id) =
    global_ctxs.[gctx_id].invariants

//--------------------------------------------------------------------

type TERM_INDUCTION<'fct_id, 'term> = {
    Value      : (VALUE) -> 'term;
    Initial    : ('fct_id * VALUE list) -> 'term;
    AppTerm    : ('fct_id * 'term list) -> 'term;
    CondTerm   : ('term * 'term * 'term) -> 'term;
    VarTerm    : (string) -> 'term;
    QuantTerm  : (AST.QUANT_KIND * string * 'term * 'term) -> 'term;
    LetTerm    : (string * 'term * 'term) -> 'term;
    DomainTerm : (Signature.TYPE) -> 'term;
}
let rec term_induction (gctx: GLOBAL_CTX) (fct_id : FCT_ID -> 'fct_id) (F : TERM_INDUCTION<'fct_id, 'term>) (t : TERM) :'term =
    let term_ind = term_induction gctx fct_id F
    match get_term' gctx t with
    |   Value' x              -> F.Value x
    |   Initial' (f, xs)      -> F.Initial (fct_id f, xs)
    |   AppTerm' (f, ts)      -> F.AppTerm (fct_id f, List.map (fun t -> term_ind t) ts)
    |   CondTerm' (G, t1, t2) -> F.CondTerm (term_ind G, term_ind t1, term_ind t2)
    |   VarTerm' v            -> F.VarTerm v
    |   QuantTerm' (q_kind, v, t_set, t_cond) -> F.QuantTerm (q_kind, v, term_ind t_set, term_ind t_cond)
    |   LetTerm' (x, t1, t2)  -> F.LetTerm (x, term_ind t1, term_ind t2)
    |   DomainTerm' tyname    -> F.DomainTerm tyname

//--------------------------------------------------------------------

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
        AppTerm  = fun (f, ts) -> pp_app_term (Signature.FctName (get_function' gctx f).fct_name, ts);
        CondTerm = fun (G, t1, t2) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun x -> str (value_to_string x);
        Initial  = fun (f, xs) -> pp_location_term "initial" ((get_function' gctx f).fct_name, xs);
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
//
//  function tables
//
//--------------------------------------------------------------------

let show_fct_tables (C : GLOBAL_CTX) =
    let ctx = get_global_ctx' C
    let fct_idx_table = ctx.fctIdxTable
    let show_fct_idx_table =
        fct_idx_table
        |> Seq.toList
        |> List.map (fun key_value -> sprintf "%s -> %d" key_value.Key key_value.Value)
        |> String.concat "\n"
    let fct_table = ctx.fctTable
    let fct_lines =
        fct_table
        |> Seq.toList
        |> List.map (fun fct' ->
            sprintf "%d: %s (%s) = [%s]"
                fct'.fct_id
                fct'.fct_name
                (Signature.fct_kind_to_string fct'.fct_kind)
                (match fct'.fct_interpretation with
                 | Constructor _ -> "constructor"
                 | StaticSymbolic _ -> "static (symbolic)"
                 | StaticBackground _ -> "static (background)"
                 | StaticUserDefined _ -> "static (user-defined)"
                 | ControlledInitial _ -> "controlled (initial)"
                 | ControlledUninitialized -> "controlled (uninitialized)"
                 | Derived (args, body) -> sprintf "derived (%s) = %s" (String.concat ", " args) (term_to_string C body) )
        )
    let show_fct_table = String.concat "\n" fct_lines
    show_fct_idx_table + "\n" + show_fct_table + "\n"

//--------------------------------------------------------------------
//
//  locations, symbolic updates, symbolic update sets
//
//--------------------------------------------------------------------

let location_to_string : LOCATION -> string = Updates.location_to_string

let show_s_update gctx ((f, xs), t) =
    sprintf "%s := %s"
        (if List.isEmpty xs then f else sprintf "%s (%s)" f (String.concat ", " (List.map value_to_string xs)))
        (PrettyPrinting.toString 80 (pp_term gctx t))

let show_s_update_set sign (U :S_UPDATE_SET) =
    "{ " +
    ( Set.toList U >>| show_s_update sign
        |> String.concat ", "   ) +
    " }"

let show_s_update_map sign (U :S_UPDATE_MAP) =
    let s_update_set = Set.ofSeq (Map.toSeq U |> Seq.collect (fun (f, table) -> table |> Map.toSeq |> Seq.map (fun (args, value) -> (f, args), value)))
    show_s_update_set sign s_update_set

//--------------------------------------------------------------------
    
type ErrorDetails =
|   InconsistentUpdates of GLOBAL_CTX * TERM list option * S_UPDATE * S_UPDATE * S_UPDATE_SET option

exception Error of GLOBAL_CTX * string * string * ErrorDetails

let error_msg (gctx : GLOBAL_CTX, modul : string, fct : string, err : ErrorDetails) = 
    sprintf "error - function %s.%s:\n" modul fct +
    match err with
    |   InconsistentUpdates (gctx, opt_conditions, u1, u2, opt_u_set) ->
            (   sprintf "\n--- inconsistent updates:\n%s\n%s\n" (show_s_update gctx u1) (show_s_update gctx u2) ) +
            (   match opt_conditions with    
                |   None -> ""
                |   Some ts ->
                        sprintf "\n--- initial state conditions leading to the inconsistent updates:\n%s\n"
                            (String.concat "\n" (ts >>| term_to_string gctx)) ) +
            (   match opt_u_set with
                |   None -> ""
                |   Some U ->
                        sprintf "\n--- updates collected on this path so far:\n%s\n" (String.concat "\n" (List.map (show_s_update gctx) (List.ofSeq U))) )

let add_s_update gctx (U : S_UPDATE_MAP) (u as (loc as (f, args), value): S_UPDATE) =
    if !trace > 0 then fprintf stderr "add_s_update: %s\n" (show_s_update gctx u)
    Map.change f
        ( function None -> Some (Map.add args value Map.empty)
                 | Some table ->
                        Some (  if Map.containsKey args table
                                then if value <> Map.find args table  // deal with conflicting updates
                                     then raise (Error (gctx, module_name, "add_s_update", InconsistentUpdates (gctx, None, (loc, Map.find args table), (loc, value), None)))
                                     else table
                                else Map.add args value table ) )
        U

let s_update_set_to_s_update_map gctx (U : S_UPDATE_SET) =
    Set.fold (add_s_update gctx) Map.empty U

let consistent gctx (U : S_UPDATE_SET) =
    try let x = s_update_set_to_s_update_map gctx U
        in true
    with Failure _ -> false
    
let locations (U : S_UPDATE_SET) : Set<LOCATION> =
    Set.map (fun (loc, value) -> loc) U

let seq_merge_2 gctx (U : S_UPDATE_SET) (V : S_UPDATE_SET) =
    if not (consistent gctx U)
    then U
    else let U_reduced = Set.filter (fun (loc, _) -> not (Set.contains loc (locations V))) U
         in Set.union U_reduced V

let seq_merge_n gctx (Us : S_UPDATE_SET list) : S_UPDATE_SET =
    List.fold (seq_merge_2 gctx) Set.empty Us

let apply_s_update_map (UM0 : S_UPDATE_MAP) (UM' : S_UPDATE_MAP) =
    let update_dynamic_function_table (f_table : Map<VALUE list, TERM>) (updates_of_f : Map<VALUE list, TERM>) =
            Map.fold (fun table args value -> Map.add args value table) f_table updates_of_f
    let apply_to_s_update_map (UM0 : S_UPDATE_MAP) (UM' : S_UPDATE_MAP) =
            Map.fold
                ( fun UM f updates_of_f ->
                    Map.change f
                        (function None -> Some (update_dynamic_function_table Map.empty updates_of_f) 
                                | Some f_table -> Some (update_dynamic_function_table f_table updates_of_f)) UM )
                UM0 UM'
    in  apply_to_s_update_map UM0 UM'

let apply_s_update_set gctx S U =
    apply_s_update_map S (s_update_set_to_s_update_map gctx U)

let sequel_s_state : GLOBAL_CTX -> S_UPDATE_MAP -> S_UPDATE_SET -> S_UPDATE_MAP = apply_s_update_set

//--------------------------------------------------------------------

type ENV = Map<string, TERM * Signature.TYPE>

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

type PATH_COND = Set<TERM> // * S_UPDATE_MAP

//let empty_context : CONTEXT = (Set.empty, Map.empty)
//let add_cond (G : TERM) (C : CONTEXT as (C1, C2)) = (Set.add G C1, C2)
let add_cond (G : TERM) (C : PATH_COND) = (Set.add G C)
//let add_intp (f : string, xs : VALUE list, t : TERM) (C : CONTEXT as (C1, C2)) = (C1, SymbUpdates.add_s_update C2 ((f, xs), t))


//--------------------------------------------------------------------
//
//  SMT solver interface
//  
//--------------------------------------------------------------------

// let smt_map_app_ctr = ref 0

let rec smt_map_term_background_function gctx (C : SmtInterface.SMT_CONTEXT) (f : FCT_ID, ts : TERM list) : SmtInterface.SMT_EXPR =
    let ctx = !C.ctx
    let es = ts >>| smt_map_term gctx C
    let f' = get_function' gctx f
    match (f'.fct_name, es) with
    |   ("=",       [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("=",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("=",       [ SmtInterface.SMT_Expr e1;     SmtInterface.SMT_Expr e2 ])     -> SmtInterface.SMT_BoolExpr (ctx.MkEq (e1, e2))
    |   ("!=",      [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
    |   ("!=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
    |   ("!=",      [ SmtInterface.SMT_Expr e1;     SmtInterface.SMT_Expr e2 ])     -> SmtInterface.SMT_BoolExpr (ctx.MkNot (ctx.MkEq (e1, e2)))
    |   ("not",     [ SmtInterface.SMT_BoolExpr e ])                                -> SmtInterface.SMT_BoolExpr (ctx.MkNot e)
    |   ("and",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkAnd (e1, e2))
    |   ("or",      [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkOr (e1, e2))
    |   ("xor",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkXor (e1, e2))
    |   ("implies", [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkImplies (e1, e2))
    |   ("iff",     [ SmtInterface.SMT_BoolExpr e1; SmtInterface.SMT_BoolExpr e2 ]) -> SmtInterface.SMT_BoolExpr (ctx.MkIff (e1, e2))
    |   (">",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkGt (e1, e2))
    |   (">=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkGe (e1, e2))
    |   ("<",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkLt (e1, e2))
    |   ("<=",      [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_BoolExpr (ctx.MkLe (e1, e2))
    |   ("+",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkAdd (e1, e2) :?> Microsoft.Z3.IntExpr)
    |   ("-",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkSub (e1, e2) :?> Microsoft.Z3.IntExpr)
    |   ("*",       [ SmtInterface.SMT_IntExpr e1;  SmtInterface.SMT_IntExpr e2 ])  -> SmtInterface.SMT_IntExpr (ctx.MkMul (e1, e2) :?> Microsoft.Z3.IntExpr)
    |   _ -> failwith (sprintf "smt_map_term_background_function: error (t = %s)" (term_to_string gctx (AppTerm gctx (f, ts))))

and smt_map_term_user_defined_function (gctx as GlobalCtx gctx_id) (C : SmtInterface.SMT_CONTEXT) (f_id : FCT_ID, ts : TERM list) : SmtInterface.SMT_EXPR =
    let sign = global_ctxs.[gctx_id].signature
    let { fct_kind = f_kind } = get_function' gctx f_id
    let (ctx, fct) = (!C.ctx, !C.fct)
    let fail (f, dom, ran) =
        failwith (sprintf "smt_map_term_user_defined_function: function '%s : %s -> %s' not found" f (Signature.type_list_to_string dom) (Signature.type_to_string ran))
    let f = (get_function' gctx f_id).fct_name     // !!!! change to new architecture
    if f_kind = Signature.Controlled
    then
        match (f, Signature.fct_type f sign, ts >>| fun t -> smt_map_term gctx C t) with
        |   (f, (dom, Signature.Boolean), es) ->
                try SmtInterface.SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.BoolExpr) with _ -> fail (f, dom, Signature.Boolean)
        |   (f, (dom, Signature.Subset (_, Signature.Boolean)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                try SmtInterface.SMT_BoolExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.BoolExpr) with _ -> fail (f, dom, Signature.Boolean)
        |   (f, (dom, Signature.Integer), es) ->
                try SmtInterface.SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.IntExpr) with _ -> fail (f, dom, Signature.Integer)
        |   (f, (dom, Signature.Subset (_, Signature.Integer)), es) ->       // !!! is it allowed in AsmetaL to have nested subset types? in that case this would fail
                try SmtInterface.SMT_IntExpr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr)) :?> Microsoft.Z3.IntExpr) with _ -> fail (f, dom, Signature.Integer)
        |   (f, (dom, (ran as Signature.TypeCons (tyname, []))), es) ->
                let (kind, ar) = (Signature.type_kind tyname sign, Signature.type_arity tyname sign)
                if kind <> Signature.EnumType || ar <> 0 then failwith (sprintf "smt_map_term_user_defined_function: types in function '%s : %s -> %s' not supported" f (Signature.type_list_to_string dom) (Signature.type_to_string ran))
                try SmtInterface.SMT_Expr (ctx.MkApp (Map.find f fct, Array.ofList (es >>| SmtInterface.convert_to_expr))) with _ -> fail (f, dom, ran)
        |   (f, (_, ran), _) -> failwith (sprintf "smt_map_term_user_defined_function : error (t = %s)" (term_to_string gctx (AppTerm gctx (f_id, ts))))
    else failwith (sprintf "smt_map_term_user_defined_function: unsupported function kind '%s' of function '%s'" (f_kind |> Signature.fct_kind_to_string) f)

and smt_map_ITE gctx (C : SmtInterface.SMT_CONTEXT) (G_, t1_, t2_) : SmtInterface.SMT_EXPR =
    let ctx = !C.ctx
    let err_msg (G, T_G, t1, T_t1, t2, T_t2) =
        failwith (sprintf "smt_map_ITE: type error: for term %s the expected type is (Boolean, T, T), where T is Boolean, Integer or a user-defined type; type (%s, %s, %s) found instead"
            (term_to_string gctx (CondTerm gctx (G, t1, t2))) (Signature.type_to_string T_G) (Signature.type_to_string T_t1) (Signature.type_to_string T_t2) )
    match (smt_map_term gctx C G_, get_type gctx G_, smt_map_term gctx C t1_, get_type gctx t1_, smt_map_term gctx C t2_, get_type gctx t2_) with
    |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_BoolExpr t1, Signature.Boolean, SmtInterface.SMT_BoolExpr t2, Boolean) ->
            SmtInterface.SMT_BoolExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.BoolExpr)
    |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_IntExpr t1, Signature.Integer, SmtInterface.SMT_IntExpr t2, Integer) ->
            SmtInterface.SMT_IntExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.IntExpr)
    |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_Expr t1, Signature.TypeCons (tyname1, []), SmtInterface.SMT_Expr t2, Signature.TypeCons (tyname2, [])) ->
            if tyname1 = tyname2
            then SmtInterface.SMT_Expr (ctx.MkITE (G, (t1 : Microsoft.Z3.Expr), (t2 : Microsoft.Z3.Expr)) : Microsoft.Z3.Expr)
            else err_msg (G_, Signature.Boolean, t1_, Signature.TypeCons (tyname1, []), t2_, Signature.TypeCons (tyname2, []))
    |   (_, T_G, _, T_t1, _, T_t2) -> err_msg (G_, T_G, t1_, T_t1, t2_, T_t2)

and smt_map_app_term gctx (C : SmtInterface.SMT_CONTEXT) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
    let { fct_name = f; fct_kind = f_kind } = get_function' gctx f_id
    if Set.contains f (Signature.fct_names Background.signature)
    then smt_map_term_background_function gctx C (f_id, ts)
    else if f_kind = Signature.Static
         then smt_map_term_user_defined_function gctx C (f_id, ts)
         else failwith (sprintf "smt_map_app_term: '%s' is not a static function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_initial gctx (C : SmtInterface.SMT_CONTEXT) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
    let { fct_name = f; fct_kind = f_kind } = get_function' gctx f_id
    let f = (get_function' gctx f_id).fct_name     // !!!! change to new architecture
    if f_kind = Signature.Controlled
    then smt_map_term_user_defined_function gctx C (f_id, ts)
    else failwith (sprintf "smt_map_initial: '%s' is not a controlled function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

and smt_map_term (gctx as GlobalCtx ctx_id : GLOBAL_CTX) (C : SmtInterface.SMT_CONTEXT) (t : TERM) : SmtInterface.SMT_EXPR =
    //if !trace > 0 then fprintf stderr "smt_map_term: %s -> " (term_to_string sign t)
    let ctx = !C.ctx
    //let gctx' = get_global_ctx' gctx
    match get_smt_expr gctx t with
    |   Some e -> e
    |   None ->
            let result = 
                match get_term' gctx t with
                |   Value' (INT i)               -> SmtInterface.SMT_IntExpr (ctx.MkInt i)
                |   Value' (BOOL b)              -> SmtInterface.SMT_BoolExpr (ctx.MkBool b)
                |   Value' (CELL (cons, []))     -> SmtInterface.SMT_Expr (Map.find cons (!C.con))
                |   Initial' (f, xs)             -> smt_map_initial gctx C (f, xs >>| Value gctx)
                |   CondTerm' (G, t1, t2)        -> smt_map_ITE gctx C (G, t1, t2)
                |   AppTerm' (f, ts) ->
                        // smt_map_app_ctr := !smt_map_app_ctr + 1;
                        // fprintf stderr "%d: %A: %A\n" (!smt_map_app_ctr) t (term_to_string gctx t);
                        smt_map_app_term gctx C (f, ts)
                |   _ -> failwith (sprintf "smt_map_term: not supported (t = %s)" (term_to_string gctx t))
            set_smt_expr gctx t result
            result

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
    |   _ -> AppTerm S (NOT S, [t])

let s_equals S (t1, t2) =
    match (get_term' S t1, get_term' S t2) with
    |   (Value' x1, Value' x2) -> Value S (BOOL (x1 = x2))
    |   (_, _) -> AppTerm S (get_fct_id S "=", [t1; t2])

let s_and S (phi1, phi2)=
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> FALSE S
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> FALSE S
    |   (_, Value' (BOOL true)) -> phi1
    |   (phi1', phi2') -> if phi1 = phi2 then phi1 else AppTerm S (AND S, [phi1; phi2])

let s_or S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> TRUE S
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> TRUE S
    |   (_, _) -> if phi1 = phi2 then phi1 else AppTerm S (OR S, [phi1; phi2])

let s_xor S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> phi2
    |   (Value' (BOOL true), _) -> s_not S phi2
    |   (_, Value' (BOOL false)) -> phi1
    |   (_, Value' (BOOL true)) -> s_not S phi1
    |   (_, _) -> if phi1 = phi2 then FALSE S else AppTerm S (get_fct_id S "xor", [phi1; phi2])

let s_implies S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL b1), _) -> s_or S (Value S (BOOL (not b1)), phi2)
    |   (_, Value' (BOOL b2)) -> s_or S (s_not S phi1, Value S (BOOL b2))
    |   (_, _) -> if phi1 = phi2 then TRUE S else AppTerm S (get_fct_id S "implies", [phi1; phi2])

let s_iff S (phi1, phi2) =
    match (get_term' S phi1, get_term' S phi2) with
    |   (Value' (BOOL false), _) -> s_not S phi2
    |   (Value' (BOOL true), _) -> phi2
    |   (_, Value' (BOOL false)) -> s_not S phi1
    |   (_, Value' (BOOL true)) -> phi1
    |   (_, _) -> if phi1 = phi2 then TRUE S else AppTerm S (get_fct_id S  "iff", [phi1; phi2])


let ctx_condition S C =
    List.fold (fun a -> fun b -> s_and S (a, b)) (TRUE S) (Set.toList C)

let smt_assert (S : GLOBAL_CTX) C (phi : TERM) =
    if get_type S phi = Signature.Boolean
    then match smt_map_term S C phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; (!C.slv).Assert be
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string S phi))
    else failwith (sprintf "'smt_assert' expects a Boolean term, %s found instead " (term_to_string S phi))

let with_extended_path_cond (gctx : GLOBAL_CTX) (G : TERM) eval_fct (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) =
    SmtInterface.smt_solver_push TopLevel.smt_ctx
    smt_assert gctx TopLevel.smt_ctx G
    let result = eval_fct () gctx (UM, env, add_cond G pc)
    SmtInterface.smt_solver_pop TopLevel.smt_ctx
    result

//--------------------------------------------------------------------

let smt_formula_is_true (S : GLOBAL_CTX) (C : SmtInterface.SMT_CONTEXT) (phi : TERM) =
    let get_type = get_type S
    if get_type phi = Signature.Boolean
    then match smt_map_term S C phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check ((!C.ctx).MkNot be) = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_true: error converting Boolean term (term = %s)" (term_to_string S phi))
    else failwith (sprintf "'smt_formula_is_true' expects a Boolean term, %s found instead " (term_to_string S phi))

let smt_formula_is_false (S : GLOBAL_CTX) (C : SmtInterface.SMT_CONTEXT) (phi : TERM) =
    let get_type = get_type S
    if get_type phi = Signature.Boolean
    then match smt_map_term S C phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check be = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_false: error converting Boolean term (term = %s)" (term_to_string S phi))
    else failwith (sprintf "'smt_formula_is_false' expects a Boolean term, %s found instead " (term_to_string S phi))

let rec interpretation (S as GlobalCtx gctx_id : GLOBAL_CTX) (UM : S_UPDATE_MAP) (pc : PATH_COND) (f as FctId f_id) (xs : VALUE list) =
    let Value = Value S
    let f' = get_function' S f
    let eval_fct_definition (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> add_binding env' (arg, Value x, type_of_value global_ctxs.[gctx_id].signature x)) Map.empty args xs
        s_eval_term body S (UM, env, pc)
    let eval_fct_definition_in_initial_state (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> add_binding env' (arg, Value x, type_of_value global_ctxs.[gctx_id].signature x)) Map.empty args xs
        s_eval_term body S (Map.empty, env, Set.empty)   //!!!! to be modified if at some point initial state constraints are implemented => path condition may then be non-empty
    match f'.fct_interpretation with
    |   Constructor (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticBackground (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticUserDefined (fct_interpretation : VALUE list -> VALUE, Some (fct_definition : string list * TERM)) ->
            eval_fct_definition fct_definition xs
            // !! alternative implementation !! Value (fct_interpretation xs)
    |   ControlledInitial (fct_interpretation : VALUE list -> VALUE, Some (fct_definition : string list * TERM)) -> 
            try Map.find xs (Map.find (get_function' S f).fct_name UM)
            with _ -> eval_fct_definition_in_initial_state fct_definition xs        // if no updates found, take value of f(xs) in initial state
            // !! alternative implementation !! Value (fct_interpretation xs)
    |   ControlledUninitialized ->
            try Map.find xs (Map.find (get_function' S f).fct_name UM)
            with _ -> Initial S (f, xs)
    |   Derived (macro_interpretation : string list * TERM) ->
            failwith (sprintf "DAG.interpretation: derived function '%s' - not implemented" f'.fct_name)
    |   StaticSymbolic (s_fct_interpretation: TERM list -> TERM) ->
            failwith (sprintf "DAG.interpretation: static symbolic function '%s' - not implemented" f'.fct_name)
    |   StaticUserDefined (_, None) ->
            failwith (sprintf "definition of static function '%s' missing" f'.fct_name)
    |   ControlledInitial (_, None) -> 
            failwith (sprintf "initial state definition of controlled function '%s' missing" f'.fct_name)

and smt_eval_formula (phi : TERM) (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env, pc : PATH_COND) =
    // precondition: term_type sign phi = Boolean
    if !trace > 0 then fprintf stderr "smt_eval_formula(%s) -> " (term_to_string C phi)
    let phi = expand_term phi C (UM, env, pc)
    let result =
        if (!SymbEval.use_smt_solver && smt_formula_is_true C TopLevel.smt_ctx phi)
        then TRUE C
        else if (!SymbEval.use_smt_solver && smt_formula_is_true C TopLevel.smt_ctx (s_not C phi))
        then FALSE C
        else phi
    if !trace > 0 then fprintf stderr "%s\n" (term_to_string C result)
    result

and expand_term t (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let get_type = get_type C
    term_induction C (fun x -> x) {
        Value   = fun x (UM, env, pc) -> Value C x;
        Initial = fun (f, xs) (UM, env, pc) -> Initial C (f, xs)
        AppTerm = fun (f, ts) (UM : S_UPDATE_MAP, env, pc) ->
            let { fct_name = f_name; fct_kind = f_kind; fct_interpretation = f_intp } = get_function' C f
            match f_intp with
            |   StaticUserDefined (_, Some (args, body)) ->
                    let ts = ts >>| fun t -> t (UM, env, pc)
                    let env = List.fold2 (fun env' arg t -> add_binding env' (arg, s_eval_term t C (UM, env, pc), get_type t)) Map.empty args ts
                    s_eval_term body C (UM, env, pc)
            | _ -> AppTerm C (f, ts >>| fun t -> t (UM, env, pc))
        CondTerm  = fun (G, t1, t2) (UM : S_UPDATE_MAP, env, pc) -> CondTerm C (G (UM, env, pc), t1 (UM, env, pc), t2 (UM, env, pc));
        VarTerm   = fun v           (UM : S_UPDATE_MAP, env, pc) -> fst (get_env env v);
        QuantTerm = fun (q_kind, v, t_set, t_cond) (UM : S_UPDATE_MAP, env, pc) -> expand_quantifier (q_kind, v, t_set, t_cond) C (UM, env, pc);
        LetTerm   = fun (v, t1, t2) (UM : S_UPDATE_MAP, env, pc) ->
                        let t1_val = t1 (UM, env, pc)
                        t2 (UM, add_binding env (v, t1_val, get_type t1_val), pc);
        DomainTerm = fun dom (UM : S_UPDATE_MAP, env, pc) -> match State.enum_finite_type dom (initial_state_of C) with Some xs -> Value C (SET xs) | _ -> failwith (sprintf "DAG.expand_term: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))
    } t ((UM : S_UPDATE_MAP), (env : ENV), (pc : PATH_COND))

and expand_quantifier (q_kind, v, t_set : S_UPDATE_MAP * ENV * PATH_COND -> TERM, t_cond : S_UPDATE_MAP * ENV * PATH_COND -> TERM)
                        (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let t_set = t_set (UM, env, pc)
    let t_set_type = get_type C t_set
    let elem_type =
        match t_set_type with
        |   Signature.Powerset tyname -> tyname
        |   _ -> failwith (sprintf "DAG.expand_quantifier: expected a set or domain type, %s found instead" (Signature.type_to_string t_set_type))
    match get_term' C t_set with
    |   Value' (Background.SET xs) ->
            let eval_instance x = t_cond (UM, add_binding env (v, Value C x, elem_type), pc)
            let t_conds = List.map eval_instance (Set.toList xs)
            match q_kind with
            |   AST.Forall -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_and C (t_accum, t1)) (TRUE C)  t_conds
            |   AST.Exist  -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_or  C (t_accum, t1)) (FALSE C) t_conds
            |   AST.ExistUnique -> failwith "DAG.expand_quantifier: 'ExistUnique' not implemented"
    |   x -> failwith (sprintf "DAG.expand_quantifier: not a set (%A): %A v" t_set x)

and try_case_distinction_for_term_with_finite_range (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env, pc : PATH_COND) (f : FCT_ID) (ts0 : TERM list) : TERM =
    let generate_cond_term (t, cases : (VALUE * TERM) list) =
        let mkCondTerm (G, t1, t2) = CondTerm C (G, t1, t2)
        let mkEq t1 t2 = s_equals C (t1, t2)
        let rec mk_cond_term (cases : (VALUE * TERM) list) =
            match cases with
            |   [] -> failwith "mk_cond_term: empty list of cases"
            |   [(t1, t2)] -> t2
            |   (t1, t2) :: cases' ->
                    let eq_term  = s_eval_term (mkEq t (Value C t1)) C (UM, env, pc)
                    match get_term' C eq_term with
                    |   Value' (BOOL true) -> t2
                    |   Value' (BOOL false) -> mk_cond_term cases'
                    |   _ -> mkCondTerm (eq_term, t2, mk_cond_term cases')
        mk_cond_term cases
    let make_case_distinction (t : TERM) (elem_term_pairs : (VALUE * TERM) list) =
        if List.isEmpty elem_term_pairs
        then failwith (sprintf "DAG.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string C t))
        generate_cond_term (t, elem_term_pairs)
    let rec F past_args = function
    |   [] -> AppTerm C (f, List.rev past_args)
    |   t1 :: ts' ->
            let t1 = s_eval_term t1 C (UM, env, pc)
            match get_term' C t1 with
            |   Value' x1 -> F (Value C x1 :: past_args) ts'
            |   _ ->
                    match (try State.enum_finite_type (get_type C t1) (initial_state_of C) with _ -> None) with
                    |   None ->
                            let f_name = (get_function' C f).fct_name
                            failwith (sprintf "arguments of dynamic function '%s' must be fully evaluable for unambiguous determination of a location\n('%s' found instead)"
                                        f_name (term_to_string C (AppTerm C (f, ts0))))
                    |   Some elems ->
                            make_case_distinction t1 (List.map (fun elem -> (elem, F (Value C elem :: past_args) ts')) (Set.toList elems))
    let result = F [] ts0
    result

and eval_app_term (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) (fct_id : FCT_ID, ts : (GLOBAL_CTX -> S_UPDATE_MAP * ENV * PATH_COND -> TERM) list) : TERM = 
//  let with_extended_path_cond = with_extended_path_cond C
    //if !trace > 0 then fprintfn stderr "|signature|=%d | eval_app_term %s%s\n" (Map.count sign) (spaces !level) (term_to_string sign (AppTerm (fct_name, [])))
    let rec F (ts_past : TERM list) ts =
        match ts with
        |   t :: ts_fut ->
                let t = t C (UM, env, pc)
                match get_term' C t with
                |   Value' x1             -> F (t :: ts_past) ts_fut
                |   Initial'  (f, xs)     -> F (t :: ts_past) ts_fut
                |   CondTerm' (G1, t11, t12) -> s_eval_term_ (CondTerm C (G1, F ts_past ((fun _ _ -> t11) :: ts_fut), F ts_past ((fun _ _ -> t12) :: ts_fut))) C (UM, env, pc)
                |   LetTerm'  (v, t1, t2) -> F (t :: ts_past) ts_fut
                |   VarTerm'  v           -> F (t :: ts_past) ts_fut
                |   AppTerm'  _           -> F (t :: ts_past) ts_fut
                |   QuantTerm' _          -> failwith "DAG.eval_app_term: QuantTerm not implemented"
                |   DomainTerm' _         -> failwith "DAG.eval_app_term: DomainTerm not implemented"
        |   [] ->
                let { fct_name = f_name; fct_kind = f_kind }  = get_function' C fct_id
                match (f_name, List.rev ts_past) with
                |   "and", [ t1; t2 ] -> s_and C (t1, t2)
                |   "or", [ t1; t2 ]  -> s_or C (t1, t2)
                |   "xor", [ t1; t2 ] -> s_xor C (t1, t2)
                |   "implies", [ t1; t2 ] -> s_implies C (t1, t2)
                |   "iff", [ t1; t2 ] -> s_iff C (t1, t2)
                |   "=", [ t1; t2 ]   -> s_equals C (t1, t2)
                |   f, ts ->
                    match get_values C ts with
                    |   Some xs -> interpretation C UM pc fct_id xs
                    |   None ->
                        match f_kind with
                        |   Signature.Static ->
                                let t = AppTerm C (fct_id, ts)
                                match get_type C t with
                                |   Signature.Boolean ->
                                        if Set.contains t pc                  then TRUE C
                                        else if Set.contains (s_not C t) pc   then FALSE C
                                        else smt_eval_formula t C (UM, env, pc)
                                | _ -> AppTerm C (fct_id, ts)
                        |   Signature.Controlled ->  s_eval_term (try_case_distinction_for_term_with_finite_range C (UM, env, pc) fct_id ts) C (UM, env, pc)
                        |   other_kind -> failwith (sprintf "DAG.eval_app_term: kind '%s' of function '%s' not implemented" (Signature.fct_kind_to_string other_kind) f)
    let f_name = (get_function' C fct_id).fct_name
    match (f_name, ts) with
    |   "and", [ t1; t2 ] ->
            let t1 = t1 C (UM, env, pc)
            match get_term' C t1 with
            |   Value' (BOOL false) -> FALSE C
            |   Value' (BOOL true)  -> t2 C (UM, env, pc)        // alternative: with_extended_path_cond t1' (fun _ -> t2) (S, env, C)
            |   t1' ->
                let t2 = t2 C (UM, env, pc)
                match get_term' C t2 with
                |   Value' (BOOL false) -> FALSE C
                |   Value' (BOOL true) -> t1    // with_extended_path_cond t2' (fun _ -> t1) (S, env, C)
                |   t2' -> if t1' = t2' then t1 else F [] [(fun _ _ -> t1); (fun _ _ -> t2)]
    |   "or", [ t1; t2 ] ->
            match get_term' C (t1 C (UM, env, pc)) with
            |   Value' (BOOL true) -> TRUE C
            |   Value' (BOOL false) -> t2 C (UM, env, pc)
            |   t1' ->
                match get_term' C (t2 C (UM, env, pc)) with
                |   Value' (BOOL true) -> TRUE C
                |   Value' (BOOL false) -> make_term C t1'
                |   t2' -> if t1' = t2' then make_term C t1' else F [] [( fun _ _ -> make_term C t1'); ( fun _ _ -> make_term C t2')]
    |   "implies", [ t1; t2 ] ->
            match get_term' C (t1 C (UM, env, pc)) with
            |   Value' (BOOL false) -> TRUE C
            |   t1' as Value' (BOOL true)  -> t2 C (UM, env, pc)       // with_extended_path_cond t1' ( fun _ _ -> t2) (S, env, C)
            |   t1' ->
                match get_term' C (t2 C (UM, env, pc)) with
                |   Value' (BOOL false) -> s_not C (make_term C t1')
                |   Value' (BOOL true)  -> TRUE C
                |   t2' -> if t1' = t2' then TRUE C else F [] [( fun _ _ -> make_term C t1'); ( fun _ _ -> make_term C t2')]
    |   "iff", [ t1; t2 ] ->
        match get_term' C (t1 C (UM, env, pc)) with
        |   Value' (BOOL false) -> s_not C (t2 C (UM, env, pc))
        |   Value' (BOOL true)  -> t2 C (UM, env, pc)
        |   t1' ->
            match get_term' C (t2 C (UM, env, pc)) with
            |   Value' (BOOL false) -> s_not C (make_term C t1')
            |   Value' (BOOL true)  -> make_term C t1'
            |   t2' -> if t1' = t2' then TRUE C else F [] [( fun _ _ -> make_term C t1'); ( fun _ _ -> make_term C t2')]
    |   "=", [ t1; t2 ] ->
        match get_term' C (t1 C (UM, env, pc)) with
        |   t1' as Value' x1 ->
            match get_term' C (t2 C (UM, env, pc)) with
            |   Value' x2 -> Value C (BOOL (x1 = x2))
            |   t2' -> F [] [( fun _ _ -> make_term C t1');  fun _ _ -> make_term C t2']
        |   t1' -> F [] [( fun _ _ -> make_term C t1');  fun _ _ -> t2 C (UM, env, pc)]
    |   _ ->
    F [] ts

and eval_cond_term (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) (G, t1 : GLOBAL_CTX -> S_UPDATE_MAP * ENV * PATH_COND -> TERM, t2) : TERM = 
    let get_type = get_type C
    let with_extended_path_cond = with_extended_path_cond C
    let term_to_string = term_to_string C
    let G = G C (UM, env, pc)
    match get_term' C G with
    |   Value' (BOOL true)  -> t1 C (UM, env, pc)
    |   Value' (BOOL false) -> t2 C (UM, env, pc)
    |   CondTerm' (G', G1, G2) ->
            if get_type G1 <> Signature.Boolean || get_type G2 <> Signature.Boolean
            then failwith (sprintf "eval_cond_term: '%s' and '%s' must be boolean terms" (term_to_string G1) (term_to_string G2))
            else let t1_G'     = t1 C (UM, env, add_cond G' (add_cond G1 pc))
                 let t1_not_G' = t1 C (UM, env, add_cond (s_not C G') (add_cond G1 pc))
                 let t2_G'     = t2 C (UM, env, add_cond G' (add_cond G2 pc))
                 let t2_not_G' = t2 C (UM, env, add_cond (s_not C G') (add_cond G2 pc))
                 s_eval_term (CondTerm C (G', CondTerm C (G1, t1_G', t2_G'), CondTerm C (G2, t1_not_G', t2_not_G'))) C (UM, env, pc)
    |   G ->    let G = make_term C G
                if (!trace > 1)
                then fprintfn stderr "\n%sctx_condition: %s" (spaces !level) (term_to_string (ctx_condition C pc))
                if not SymbEval.simplify_cond then
                    // version 1: no simplification whatsoever (inefficient, but useful for debugging)
                    CondTerm C (G, t1 C (UM, env, add_cond G pc), t2 C (UM, env, add_cond (s_not C G) pc))
                else 
                    // version 2: with simplification
                    if Set.contains G pc
                    then t1 C (UM, env, pc)
                    else if Set.contains (s_not C G) pc
                    then t2 C (UM, env, pc)
                    else let (t1', t2') = (t1 C (UM, env, add_cond G pc), t2 C (UM, env, add_cond (s_not C G) pc))
                         if t1' = t2' then t1'
                         else if not !SymbEval.use_smt_solver
                              then  let t1' = s_eval_term t1' C (UM, env, add_cond G pc)
                                    let t2' = s_eval_term t2' C (UM, env, add_cond (s_not C G) pc)
                                    if t1' = t2' then t1' else CondTerm C (G, t1', t2')
                              else  let t1' = with_extended_path_cond G           ( fun _ -> s_eval_term t1') (UM, env, pc)  
                                    let t2' = with_extended_path_cond (s_not C G) ( fun _ -> s_eval_term t2') (UM, env, pc)  
                                    if t1' = t2' then t1' else CondTerm C (G, t1', t2')
and eval_let_term (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) (v, t1, t2) : TERM =
    let t1 = t1 C (UM, env, pc)
    t2 C (UM, add_binding env (v, t1, get_type C t1), pc)

and s_eval_term_ (t : TERM) (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    term_induction C (fun x -> x) {
        Value      = fun x C _ -> Value C x;
        Initial    = fun (f, xs) C _ -> Initial C (f, xs);
        AppTerm    = fun (f, ts) C (UM, env, pc) -> eval_app_term C (UM, env, pc) (f, ts)
        CondTerm   = fun (G, t1, t2) C (UM, env, pc) -> eval_cond_term C (UM, env, pc) (G, t1, t2);
        VarTerm    = fun v -> fun C (_, env, _) -> fst (get_env env v);
        QuantTerm  = fun (q_kind, v, t_set, t_cond) C (UM, env, pc) -> expand_quantifier (q_kind, v, t_set C, t_cond C) C (UM, env, pc);
        LetTerm    = fun (v, t1, t2) C (_, env, _) -> eval_let_term C (UM, env, pc) (v, t1, t2) 
        DomainTerm = fun dom C (_, _, _) -> match State.enum_finite_type dom (initial_state_of C) with Some xs -> Value C (SET xs) | None -> failwith (sprintf "DAG.s_eval_term_: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))
    } t C (UM, env, pc)

and s_eval_term (t : TERM) (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let t = s_eval_term_ t C (UM, env, pc)
    if get_type C t = Signature.Boolean
    then    match get_term' C t with
            |   Value' (BOOL _)  -> t
            |   _ -> smt_eval_formula t C (UM, env, pc)
    else    t

//--------------------------------------------------------------------

let rec try_case_distinction_for_update_with_finite_domain
        (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND)
        (f : Signature.FCT_NAME) (ts0 : TERM list) (t_rhs : TERM): RULE =
    let mkEq (t1 : TERM) t2 = s_equals C (t1, t2)  // AppTerm' (Boolean, (FctName "=", [t1; t2]))
    let generate_cond_rule (t, cases : (VALUE * RULE) list) =
        let t = s_eval_term t C (UM, env, pc)
        let ty = get_type C t
        let rec mk_cond_rule cases =
            match cases with
            |   [] -> failwith "mk_cond_rule: empty list of cases"
            |   [(t1, R)] -> s_eval_rule R C (UM, env, pc)
            |   (t1, R) :: cases' ->
                    let eq_term0 = mkEq t (Value C t1)
                    let eq_term  = s_eval_term eq_term0 C (UM, env, pc)
                    match get_term' C eq_term with
                    |   Value' (BOOL true) -> s_eval_rule R C (UM, env, pc)
                    |   Value' (BOOL false) -> mk_cond_rule cases'
                    |   _ -> CondRule (eq_term, s_eval_rule R C (UM, env, pc), mk_cond_rule cases')
        mk_cond_rule cases
    let make_case_distinction (t : TERM) (elem_rule_pairs : (VALUE * RULE) list) =
        if List.isEmpty elem_rule_pairs
        then failwith (sprintf "SymbEval.try_case_distinction_for_term_with_finite_domain: empty range for term %s" (term_to_string C t))
        generate_cond_rule (t, elem_rule_pairs)
    let rec F past_args = function
        |   [] -> UpdateRule ((f, List.rev past_args), t_rhs)
        |   t1 :: ts' ->
            let t1 = s_eval_term t1 C (UM, env, pc)
            match get_term' C t1 with
            |   Value' x1 -> F (Value C x1 :: past_args) ts'
            |   _ ->
                    match (try State.enum_finite_type (get_type C t1) (initial_state_of C) with _ -> None) with
                    |   None ->
                            failwith (sprintf "location (%s, (%s)) on the lhs of update cannot be fully evaluated"
                                        f (String.concat ", " (ts0 >>| term_to_string C)))
                    |   Some elems ->
                            make_case_distinction t1 (List.map (fun elem -> (elem, F (Value C elem :: past_args) ts')) (Set.toList elems))
    F [] ts0

and s_eval_rule (R : RULE) (C : GLOBAL_CTX) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
    let s_eval_term t = s_eval_term t C
    let s_eval_rule R = s_eval_rule R C
    let get_type, with_extended_path_cond = get_type C, with_extended_path_cond C
    let rule_to_string, term_to_string, pp_rule = rule_to_string C, term_to_string C, pp_rule C

    if (!trace > 1)
    then fprintf stderr "%s----------------------\n%ss_eval_rule %s\n%s\n\n"
            (spaces !level) (spaces !level) (show_s_update_map C UM) (toString 80 (indent (!level) (pp_rule R)))
    level := !level + 1

    let eval_update ((f, ts), t_rhs) (UM : S_UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
        if !trace > 0 then fprintf stderr "eval_update: %s\n" (rule_to_string (UpdateRule ((f, ts), t_rhs)))
        match get_term' C (s_eval_term t_rhs (UM, env, pc)) with
        |   CondTerm' (G, t1, t2) ->
                s_eval_rule (CondRule (G, UpdateRule ((f, ts), t1), UpdateRule ((f, ts), t2))) (UM, env, pc)
        |   _ ->
            let rec F (ts_past : TERM list) : TERM list -> RULE = function
                |   (t1 :: ts_fut) ->
                    match get_term' C t1 with
                    |   Value' _        -> F (t1 :: ts_past) ts_fut
                    |   Initial' _      -> F (t1 :: ts_past) ts_fut
                    |   CondTerm' (G1, t11, t12) ->
                           s_eval_rule (CondRule (G1, F ts_past (t11 :: ts_fut), F ts_past (t12 :: ts_fut))) (UM, env, pc)
                    |   QuantTerm' _          -> failwith "SymbEval.eval_app_term: QuantTerm not implemented"
                    |   LetTerm' _            -> failwith "SymbEval.eval_app_term: LetTerm not implemented"
                    |   VarTerm' _      -> F (s_eval_term_ t1 C (UM, env, pc) :: ts_past) ts_fut
                    |   AppTerm' _      -> F (s_eval_term_ t1 C (UM, env, pc) :: ts_past) ts_fut
                    |   DomainTerm' _   -> failwith "SymbEval.eval_app_term: DomainTerm not implemented"
                |   [] ->
                    match get_values C (ts_past >>| fun t -> s_eval_term t (UM, env, pc)) with
                    |   Some xs -> S_Updates (Set.singleton ((f, List.rev xs), s_eval_term t_rhs (UM, env, pc)));
                    |   None -> try_case_distinction_for_update_with_finite_domain C (UM, env, pc) f ts t_rhs
            F [] ts

    let eval_cond (G, R1, R2) (UM, env, pc) = 
        let G = s_eval_term G (UM, env, pc)
        match get_term' C G with
        |   Value' (BOOL true)  -> s_eval_rule R1 (UM, env, pc)
        |   Value' (BOOL false) -> s_eval_rule R2 (UM, env, pc)
        |   CondTerm' (G', G1, G2) ->
                if get_type G1 <> Signature.Boolean || get_type G2 <> Signature.Boolean
                then failwith (sprintf "s_eval_rule.eval_cond: '%s' and '%s' must be boolean terms" (term_to_string G1) (term_to_string G2))
                else s_eval_rule (CondRule (G', CondRule (G1, R1, R2), CondRule (G2, R1, R2))) (UM, env, pc)
        |   _ ->    //let (R1', R2') = (s_eval_rule R1 (S, env, add_cond G C), s_eval_rule R2 (S, env, add_cond (s_not G) C)_
                    if not !SymbEval.use_smt_solver
                    then    let R1' = s_eval_rule R1 (UM, env, (add_cond G pc))
                            let R2' = s_eval_rule R2 (UM, env, (add_cond (s_not C G) pc))
                            if R1' = R2' then R1' else CondRule (G, R1', R2')
                    else    let R1' = with_extended_path_cond G           (fun _ _ -> s_eval_rule R1) (UM, env, pc)
                            let R2' = with_extended_path_cond (s_not C G) (fun _ _ -> s_eval_rule R2) (UM, env, pc)  
                            if R1' = R2' then R1' else CondRule (G, R1', R2')

    let rec eval_par Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> s_eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_par R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_par R1 R2 (UM, env, pc) : RULE =
        match s_eval_rule R1 (UM, env, pc) with
        |   S_Updates U1 ->
                match s_eval_rule R2 (UM, env, pc) with
                |   S_Updates U2 ->
                        S_Updates (Set.union U1 U2)
                |   CondRule (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, ParRule [ S_Updates U1; R21 ], ParRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R2))
        |   CondRule (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, ParRule [ R11; R2 ], ParRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R1))

    and eval_seq Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> s_eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_seq R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_seq R1 R2 (UM, env, pc): RULE = 
        match s_eval_rule R1 (UM, env, pc) with
        |   S_Updates U1 ->
                let S' =
                    try sequel_s_state C UM U1
                    with Error (_, _, _, InconsistentUpdates (C, _, u1, u2, _)) ->
                            raise (Error (C, module_name, "s_eval_rule.eval_binary_seq",
                                InconsistentUpdates (C, Some (List.ofSeq pc), u1, u2, Some U1)))
                match s_eval_rule R2 (S', env, pc) with
                |   S_Updates U2 ->
                        S_Updates (seq_merge_2 C U1 U2)
                |   CondRule (G2, R21, R22) ->
                        s_eval_rule (CondRule (G2, SeqRule [ S_Updates U1; R21 ], SeqRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R2))
        |   CondRule (G1, R11, R12) ->
                s_eval_rule (CondRule (G1, SeqRule [ R11; R2 ], SeqRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R1))

    and eval_iter R (UM, env, pc) =
        match s_eval_rule R (UM, env, pc) with
        |   S_Updates U ->
                if Set.isEmpty U
                then S_Updates Set.empty
                else s_eval_rule (SeqRule [ S_Updates U; IterRule R ]) (UM, env, pc)
        |   (CondRule (G, R1, R2)) ->
                //s_eval_rule (SeqRule [ CondRule (G, R1, R2); IterRule R ]) (UM, env, pc)
                s_eval_rule (CondRule (G, SeqRule [R1; IterRule R], SeqRule [R2; IterRule R])) (UM, env, pc)
        |   R' -> failwith (sprintf "SymEvalRules.s_eval_rule: eval_iter_rule - R'' = %s" (rule_to_string R'))
    
    and eval_let (v, t, R) (UM, env, pc) =
        let t' = s_eval_term t (UM, env, pc)
        let R' = s_eval_rule R (UM, add_binding env (v, t', get_type t'), pc)
        R'

    and eval_forall (v, ts, G, R) (UM, env, pc) =
        match get_term' C (s_eval_term ts (UM, env, pc)) with
        |   Value' (SET xs) ->
                let eval_instance x =
                    let env' = let t_x = Value C x in add_binding env (v, t_x, get_type t_x)
                    CondRule (s_eval_term G (UM, env', pc), s_eval_rule R (UM, env', pc), skipRule)
                let Rs = List.map (fun x -> eval_instance x) (Set.toList xs)
                s_eval_rule (ParRule Rs) (UM, env, pc)
        |   x -> failwith (sprintf "SymbEval.forall_rule: not a set (%A): %A v" ts x)

    and eval_macro_rule_call (r, args) (UM, env, pc) =
        let (formals, body) =
            try Map.find r (rules_of C)
            with _ -> failwith (sprintf "SymbEval.s_eval_rule: macro rule %s not found" r)
        let env' =
            List.fold2 (fun env' formal arg -> add_binding env' (formal, s_eval_term arg (UM, env, pc), get_type arg)) env formals args
        s_eval_rule body (UM, env', pc)
 
    let R =
        match R with
        |   UpdateRule ((f, ts), t) -> eval_update ((f, ts), t) (UM, env, pc)
        |   CondRule (G, R1, R2)    -> eval_cond (G, R1, R2) (UM, env, pc)
        |   ParRule Rs              -> eval_par Rs (UM, env, pc)
        |   SeqRule Rs              -> eval_seq Rs (UM, env, pc)
        |   IterRule R              -> eval_iter R (UM, env, pc)
        |   LetRule (v, t, R)       -> eval_let (v, t, R) (UM, env, pc) 
        |   ForallRule (v, t, G, R) -> eval_forall (v, t, G, R) (UM, env, pc) 
        |   MacroRuleCall (r, args) -> eval_macro_rule_call (r, args) (UM, env, pc)
        |   S_Updates S             -> S_Updates S

    level := !level - 1
    if (!trace > 1)
    then fprintf stderr "%ss_eval_rule result = \n%s\n%s----------------------\n" (spaces !level) (toString 120 (indent (!level) (pp_rule R))) (spaces !level)

    R


//--------------------------------------------------------------------
// convert partially evaluated terms and rules to regular ones

let rec reconvert_value (C : GLOBAL_CTX) x =
    match x with
    |   UNDEF    -> Value C x
    |   BOOL b   -> Value C x
    |   INT i    -> Value C x
    |   STRING s -> Value C x
    |   SET fs   -> //AppTerm (FctName "asSet", ?????)
                    failwith "reconvert_value: SET not implemented yet"
    |   CELL (tag, args) -> AppTerm C (get_fct_id C tag, args >>| reconvert_value C)

let reconvert_term (C : GLOBAL_CTX) t =
    term_induction C (fun x -> x) {
        Value      = fun x -> reconvert_value C x;
        Initial    = fun (f, xs) -> AppTerm C (f, xs >>| Value C);
        AppTerm    = AppTerm C;
        CondTerm   = CondTerm C;
        VarTerm    = VarTerm C;
        QuantTerm  = QuantTerm C;
        LetTerm    = LetTerm C;
        DomainTerm = DomainTerm C;
    } t

let reconvert_rule (C : GLOBAL_CTX) R = 
    rule_induction (reconvert_term C) {
        UpdateRule = UpdateRule;
        CondRule   = CondRule;
        ParRule    = ParRule;
        SeqRule    = SeqRule;
        IterRule   = IterRule;
        LetRule    = LetRule;
        MacroRuleCall = MacroRuleCall;
        ForallRule = ForallRule;
        S_Updates  = fun upds -> ParRule (List.map (fun ((f, xs), t_rhs) -> UpdateRule ((f, xs >>| Value C), reconvert_term C t_rhs)) (Set.toList upds))
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

let name_size name = 1

let term_size C =
    term_induction C name_size {
        Value = fun _ -> 1;
        AppTerm = fun (f, ts : int list) -> 1 + f + List.sum ts;
        CondTerm = fun (G, t1, t2) -> 1 + G + t1 + t2;
        Initial = fun _ -> 1;
        VarTerm = fun _ -> 1;
        QuantTerm = fun (q_kind, v, t_set, t_cond) -> 1 + t_set + t_cond;
        LetTerm = fun (v, t1, t2) -> 1 + t1 + t2;
        DomainTerm = fun _ -> 1;
    }

let rule_size C =
    rule_induction (term_size C) {
        S_Updates = fun U -> Set.count U;   // not relevant, but define somehow to allow printing for debugging
        UpdateRule = fun ((f, ts), t) -> 1 + 1 + List.sum ts + t;
        CondRule = fun (G, R1, R2) -> 1 + G + R1 + R2;
        ParRule = fun Rs -> 1 + List.sum Rs;
        SeqRule = fun Rs -> 1 + List.sum Rs;
        IterRule = fun R' -> 1 + R';
        LetRule = fun (_, t, R) -> 1 + t + R;
        ForallRule = fun (_, t_set, t_filter, R) -> 1 + t_set + t_filter + R;
        MacroRuleCall = fun (r, ts) -> 1 + 1 + List.sum ts;
    }

//--------------------------------------------------------------------
// first element of pair returned is the number of S_Updates rules, i.e. paths in the decision tree
let symbolic_execution (C : GLOBAL_CTX) (R_in : RULE) (steps : int) : int * RULE =
    if (!trace > 2) then fprintf stderr "symbolic_execution\n"
    if (steps <= 0) then failwith "SymbEval.symbolic_execution: number of steps must be >= 1"
    let S0 = TopLevel.initial_state ()
    //  if (!trace > 2) then fprintf stderr "---\n%s\n---\n" (Signature.signature_to_string (signature_of C))
    let R_in_n_times = [ for _ in 1..steps -> R_in ]
    let R_in' = SeqRule (R_in_n_times @ [ skipRule ])      // this is to force the application of the symbolic update sets of R_in, thus identifying any inconsistent update sets
    let R_out = s_eval_rule R_in' C (Map.empty, Map.empty, Set.empty)
    (count_s_updates R_out, reconvert_rule C R_out)

let symbolic_execution_for_invariant_checking (C : GLOBAL_CTX) (opt_steps : int option) (R_in : RULE) : unit =
    let proc = Process.GetCurrentProcess()
    let capture_cpu_time (proc : Process) =
        (proc.TotalProcessorTime, proc.UserProcessorTime, proc.PrivilegedProcessorTime)
    let measure_cpu_time (proc : Process) (cpu0, usr0, sys0) =
        let (cpu1, usr1, sys1) = capture_cpu_time proc
        ( (cpu1 - cpu0).TotalMilliseconds, (usr1 - usr0).TotalMilliseconds, (sys1 - sys0).TotalMilliseconds )
    let (cpu0, usr0, sys0) = capture_cpu_time proc
    if (!trace > 2) then fprintf stderr "symbolic_execution_for_invariant_checking\n"
    let with_extended_path_cond = with_extended_path_cond C
    match opt_steps with
    |   Some n -> if n < 0 then failwith "SymbEval.symbolic_execution_for_invariant_checking: number of steps must be >= 0"
    |   None -> ()
    let UM0 = Map.empty
    let invs = Map.toList (invariants_of C)
    let counters = ref Map.empty
    let reset_counters () = counters := Map.empty
    let update_counters f inv_id = counters := Map.change inv_id (function Some (m, v, u) -> Some (f (m, v, u)) | None -> Some (f (0, 0, 0))) (!counters)
    let print_counters i () =
        printf "\n--- S_%d summary:\n\n" i
        Map.map (fun inv_id (m, v, u) -> printf "'%s': met on %d paths / definitely violated on %d paths / possibly violated on %d paths\n" inv_id m v u) !counters |> ignore
        let (cpu, usr, sys) = measure_cpu_time proc (cpu0, usr0, sys0)
        print_time (cpu, usr, sys)
        |> ignore
    let rec traverse i conditions R (UM, env, pc) =
        let initial_state_conditions_to_reach_this_state ts =
            sprintf "- this path is taken when the following conditions hold in the initial state:\n%s"
                (String.concat "\n" (List.rev ts >>| fun t -> term_to_string C (reconvert_term C t)))
        let show_cumulative_updates sign updates =
            "- cumulative update set for this path:\n" ^
            String.concat "\n"
                (Set.toList updates >>| fun ((f, xs), t) ->
                    sprintf "%s%s := %s"
                        f (if List.isEmpty xs then "" else "("^(String.concat ", " (xs >>| value_to_string))^")")
                        (term_to_string sign t))
        let met inv_id =
            update_counters (function (m, v, u) -> (m + 1, v, u)) inv_id
            ""
        let possibly_violated inv_id conditions (updates : S_UPDATE_SET) t t' = 
            update_counters (function (m, v, u) -> (m, v, u + 1)) inv_id
            sprintf "\n!!! invariant '%s' possibly violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string C t) (term_to_string C t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates C updates)
        let definitely_violated inv_id conditions updates t t' =
            update_counters (function (m, v, u) -> (m, v + 1, u)) inv_id
            sprintf "\n!!! invariant '%s' definitely violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string C t) (term_to_string C t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates C updates)
        let check_invariants invs S0 conditions updates =
            let check_one (inv_id, t) =
                let t' = s_eval_term t C (apply_s_update_set C S0 updates, Map.empty, Set.empty)
                if smt_formula_is_true C TopLevel.smt_ctx t'
                then met inv_id
                else if smt_formula_is_false C TopLevel.smt_ctx t' then definitely_violated inv_id conditions updates t t'
                else possibly_violated inv_id conditions updates t t'
            printf "%s" (String.concat "" (List.filter (fun s -> s <> "") (List.map check_one invs)))
        match R with      // check invariants on all paths of state S' = S0 + R by traversing tree of R
        |   CondRule (G, R1, R2) ->
                with_extended_path_cond G           (fun _ _ -> traverse i (G::conditions) R1) (UM, env, pc)
                with_extended_path_cond (s_not C G) (fun _ _ -> traverse i ((s_not C G)::conditions) R2) (UM, env, pc)
        |   S_Updates updates    ->
                check_invariants invs UM0 conditions updates
        |   R -> failwith (sprintf "symbolic_execution_for_invariant_checking: there should be no such rule here: %s\n" (rule_to_string C R))
    let state_header i = printf "\n=== state S_%d =====================================\n" i
    let rec F R_acc R_in i =
        reset_counters ()
        state_header i
        traverse i [] R_acc  (UM0, Map.empty, Set.empty)
        print_counters i ()
        if (match opt_steps with Some n -> i < n | None -> true)
        then let R_acc = s_eval_rule (SeqRule ([ R_acc; R_in; skipRule ])) C (UM0, Map.empty, Set.empty)
             F R_acc R_in (i+1)
    F (S_Updates Set.empty) (SeqRule ([ R_in; skipRule ])) 0
    printf "\n=================================================\n"

