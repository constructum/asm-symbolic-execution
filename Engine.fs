module Engine

//--------------------------------------------------------------------

open System.Diagnostics
open System.Collections.Generic

open Common
open IndMap
open PrettyPrinting
open Background

//--------------------------------------------------------------------

let trace = ref 0
let level = ref 0
let module_name = "Engine"

let spaces () =
    let rec F level = if level = 0 then "" else "  " + F (level-1)
    F !level
    
let indent ppt = 
    let rec F level ppt = if level = 0 then ppt else blo2 [ F (level-1) ppt ]
    toString 120 (F !level ppt)

let prepend x = fun xs -> x :: xs
let K x = fun _ -> x

//--------------------------------------------------------------------

type FUNCTION_INTERPRETATION =
|   Constructor of (VALUE list -> VALUE)
|   StaticSymbolic of (TERM list -> TERM)       // rewriting rules for term simplification, e.g. for boolean functions 
|   StaticBackground of (VALUE list -> VALUE)
|   StaticUserDefined of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledInitial of (VALUE list -> VALUE) * (string list * TERM) option
|   ControlledUninitialized
|   Derived of (string list * TERM)             // string list is the list of arguments, TERM is the body of the derived function

and FUNCTION' =
    FctName of string

and FUNCTION_ATTRS = {
    fct_id   : int;
    fct_kind : Signature.FCT_KIND;
    // fct_type : (Signature.TYPE list * Signature.TYPE);   // !!! to be implemented together with monomorphization
    fct_interpretation : FUNCTION_INTERPRETATION
}

and FCT_ID =
|   FctId of int

and RULE_DEF' =
    RuleName of string

and RULE_DEF_ATTRS = {
    rule_id   : int;
    // rule_type : (Signature.TYPE list * Signature.TYPE);   // !!! to be implemented together with monomorphization
    rule_def  : (string list * RULE) option
}
and RULE_DEF_ID =
|   RuleDefId of int

and ENGINE' = {
    signature       : Signature.SIGNATURE
    initial_state   : State.STATE         // use only for initial state in this module, never use '_dynamic' field - also the second elem. of _dynamic_initial seems not to be used !
    invariants      : Map<string, TERM>   // Added invariants field

    functions       : IndMap<FUNCTION', FUNCTION_ATTRS>
    rule_defs       : IndMap<RULE_DEF', RULE_DEF_ATTRS>
    terms           : IndMap<TERM', TERM_ATTRS>
    rules           : IndMap<RULE', RULE_ATTRS>

    TRUE_           : TERM option ref
    FALSE_          : TERM option ref
    AND_            : FCT_ID option ref
    OR_             : FCT_ID option ref
    NOT_            : FCT_ID option ref
    EQUALS_         : FCT_ID option ref

    smt_ctx         : SmtInterface.SMT_CONTEXT
}

and ENGINE = Engine of int

and ENGINES = ResizeArray<ENGINE'>

and TERM' =
|   Value'      of (VALUE)                  // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   Initial'    of (FCT_ID * VALUE list)    // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   AppTerm'    of (FCT_ID * TERM list)
|   CondTerm'   of (TERM * TERM * TERM)
|   VarTerm'    of (string * Signature.TYPE)  // variable name and optional type (to be filled in during type checking)
|   QuantTerm'  of (AST.QUANT_KIND * string * TERM * TERM)
|   LetTerm'    of (string * TERM * TERM)
|   DomainTerm' of Signature.TYPE                  // AsmetaL construct: finite type (e.g. enum, abstract, subsetof) used as finite set
//  | TupleTerm   of 'annotation * ('annotation ANN_TERM list)

and TERM = Term of int

and TERM_ATTRS = {
    term_id       : int
    term_type     : Signature.TYPE
    smt_expr      : SmtInterface.SMT_EXPR option ref
    initial_state_eval_res : TERM option ref     // (symbolic) value of the term in the initial state, used also for static functions
}

and TERM_INDUCTION<'fct_id, 'term> = {
    Value      : (VALUE) -> 'term;
    Initial    : ('fct_id * VALUE list) -> 'term;
    AppTerm    : ('fct_id * 'term list) -> 'term;
    CondTerm   : ('term * 'term * 'term) -> 'term;
    VarTerm    : (string * Signature.TYPE) -> 'term;
    QuantTerm  : (AST.QUANT_KIND * string * 'term * 'term) -> 'term;
    LetTerm    : (string * 'term * 'term) -> 'term;
    DomainTerm : (Signature.TYPE) -> 'term;
}

and RULE' =
|   S_Updates' of Set<(FCT_ID * VALUE list) * TERM>  //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
|   UpdateRule' of (FCT_ID * TERM list) * TERM
|   CondRule' of TERM * RULE * RULE
|   ParRule' of RULE list
|   SeqRule' of RULE list
|   IterRule' of RULE
|   LetRule' of string * TERM * RULE
|   ForallRule' of string * TERM * TERM * RULE
|   MacroRuleCall' of RULE_DEF_ID * TERM list

and RULE = Rule of int

and RULE_ATTRS = unit

and RULE_INDUCTION<'term, 'rule> = {
    S_Updates : Set<(FCT_ID * VALUE list) * TERM> -> 'rule;     // what not ""... * 'term>" ?
    UpdateRule : (FCT_ID * 'term list) * 'term -> 'rule;
    CondRule : 'term * 'rule * 'rule -> 'rule;
    ParRule : 'rule list -> 'rule;
    SeqRule : 'rule list -> 'rule;
    IterRule : 'rule -> 'rule;
    LetRule : string * 'term * 'rule -> 'rule;
    ForallRule : string * 'term * 'term * 'rule -> 'rule;
    MacroRuleCall : RULE_DEF_ID * 'term list -> 'rule;     // Map<FCT_NAME * VALUE list, 'term> -> 'rule;
}

and FCT_DEF_DB = Map<Signature.FCT_NAME, string list * TERM>    // for function definitions
and RULE_DEF_DB = Map<Signature.RULE_NAME, string list * RULE>     // for rule macros

and LOCATION = FCT_ID * VALUE list

and UPDATE = LOCATION * TERM
and UPDATE_SET = Set<UPDATE>
and UPDATE_MAP = Map<FCT_ID, Map<VALUE list, TERM>>

and ENV = Map<string, TERM * Signature.TYPE>

and PATH_COND = Set<TERM> // * S_UPDATE_MAP

let engines = new ENGINES()

let rec env_to_string = fun (eng as Engine eid : ENGINE) (env : ENV) ->
    env
    |> Map.toList
    |> List.map (fun (v, (t, ty)) -> sprintf "%s : %s = %s" v (Signature.type_to_string ty) (term_to_string eng t))
    |> String.concat "; "

and inline get_fct_id (Engine eid) (name : string) : FCT_ID =
    match engines.[eid].functions |> try_get_index (FctName name) with
    | Some fct_id -> FctId fct_id
    | None -> failwith (sprintf "Engine.get_fct_id: function '%s' not found in global context #%d" name eid)

and inline get_function' (Engine eid) (FctId id) : FUNCTION' * FUNCTION_ATTRS =
    engines.[eid].functions |> get id

and inline fct_name eng fct_id = let (FctName name) = fst (get_function' eng fct_id) in name
and inline fct_kind eng fct_id = (snd (get_function' eng fct_id)).fct_kind
and inline fct_interpretation eng fct_id = (snd (get_function' eng fct_id)).fct_interpretation
and inline get_term (eng as Engine eid : ENGINE) (t' : TERM') : TERM =
    match IndMap.try_get_index t' engines.[eid].terms with
    |   Some tid ->
            Term tid
    |   None ->
            let e = engines.[eid]
            let tid = e.terms |> count
            let attrs = {
                term_id    = tid;
                term_type  = compute_type eng t';
                smt_expr   = ref None;
                initial_state_eval_res = ref None
            }
            e.terms |> add (t', attrs) |> Term
and inline get_term'_attrs (Engine eid) (Term tid) = engines.[eid].terms |> get tid
and inline get_term' (Engine eid) (Term tid) :TERM' = engines.[eid].terms |> get_obj tid
and inline get_term_attrs (Engine eid) (Term tid) = engines.[eid].terms |> get_attrs tid

and compute_type (eng as Engine eid) (t' : TERM') : Signature.TYPE =
    let (sign, get_type) = (engines.[eid].signature, get_type eng)
    match t' with
    |   Value' x -> type_of_value sign x
    |   Initial' (f, xs) -> let f_name = fct_name eng f in Signature.match_fct_type f_name (xs >>| type_of_value sign) (Signature.fct_types f_name sign)
    |   AppTerm' (f, ts) -> let f_name = fct_name eng f in Signature.match_fct_type f_name (ts >>| get_type) (Signature.fct_types f_name sign)
    |   CondTerm' (G, t1, t2) ->
            if get_type t1 = get_type t2
            then get_type t1
            else failwith (sprintf "compute_type: types of branches of conditional term do not match:\nguard:%s\nbranch 1:\n%s : %s\nbranch 2:\n%s : %s"
                                (term_to_string eng G)
                                (term_to_string eng t1) (Signature.type_to_string (get_type t1))
                                (term_to_string eng t2) (Signature.type_to_string (get_type t2)))
    |   VarTerm' (v, ty) -> ty
    |   QuantTerm' (_, _, t_set, _) -> Signature.Boolean
    |   LetTerm' (_, t1, t2) -> get_type t2
    |   DomainTerm' tyname -> Signature.Powerset tyname

and get_type (Engine eid) (t as Term tid : TERM) : Signature.TYPE =
    (engines.[eid].terms |> get_attrs tid).term_type

and inline get_smt_expr (Engine eid) (t as Term tid : TERM) : SmtInterface.SMT_EXPR option =
    !(engines.[eid].terms |> get_attrs tid).smt_expr

and inline set_smt_expr (Engine eid) (t as Term tid : TERM) (smt_expr : SmtInterface.SMT_EXPR) =
    (engines.[eid].terms |> get_attrs tid).smt_expr := Some smt_expr

and inline initial_state_eval_res (Engine eid) (t as Term tid : TERM) : TERM option ref =
    (engines.[eid].terms |> get_attrs tid).initial_state_eval_res

and inline Value eng x = get_term eng (Value' x)
and inline Initial eng (f, xs) = get_term eng (Initial' (f, xs))
and inline AppTerm eng (f, ts) = get_term eng (AppTerm' (f, ts))
and inline CondTerm eng (G, t1, t2) = get_term eng (CondTerm' (G, t1, t2))
and inline VarTerm eng v = get_term eng (VarTerm' v)
and inline QuantTerm eng (q_kind, v, t_set, t_cond) = get_term eng (QuantTerm' (q_kind, v, t_set, t_cond))
and inline LetTerm eng (x, t1, t2) = get_term eng (LetTerm' (x, t1, t2))
and inline DomainTerm eng tyname = get_term eng (DomainTerm' tyname)
and inline TRUE (Engine eid) = !engines.[eid].TRUE_ |> Option.get
and inline FALSE (Engine eid) = !engines.[eid].FALSE_ |> Option.get
and inline AND (Engine eid) = !engines.[eid].AND_ |> Option.get
and inline OR (Engine eid) = !engines.[eid].OR_ |> Option.get
and inline NOT (Engine eid) = !engines.[eid].NOT_ |> Option.get
and inline EQUALS (Engine eid) = !engines.[eid].EQUALS_ |> Option.get

and convert_term (eng : ENGINE) (t : AST.TYPED_TERM) : TERM =
    AST.ann_term_induction (fun x -> x) {
        Value      = fun (_, x) -> Value eng x;
        Initial    = fun (_, (f, xs)) -> Initial eng (get_fct_id eng f, xs);
        AppTerm    = fun (ty, (f, ts)) ->
                        match f with
                        |   Signature.UndefConst    -> Value eng UNDEF
                        |   Signature.BoolConst b   -> Value eng (BOOL b)
                        |   Signature.IntConst i    -> Value eng (INT i)
                        |   Signature.StringConst s -> Value eng (STRING s)
                        |   Signature.FctName f ->
                                let f_id = get_fct_id eng f
                                try
                                    AppTerm eng (f_id, ts)
                                with ex as Signature.Error (Signature.NoMatchingFunctionType (f, tys)) ->
                                    fprintf stderr "convert_term: in term %A\n" (AppTerm eng (f_id, ts))
                                    raise ex
        CondTerm   = fun (_, (G, t1, t2)) -> CondTerm eng (G, t1, t2);
        VarTerm    = fun (ty, v) -> VarTerm eng (v, ty)
        QuantTerm  = fun (ty, (q_kind, v, t_set, t_cond)) -> QuantTerm eng (q_kind, v, t_set, t_cond);
        LetTerm    = fun (_, (v, t1, t2)) -> LetTerm eng (v, t1, t2);
        DomainTerm = fun (_, D) -> DomainTerm eng D;
    } t

and inline get_rule_def_id (Engine eid) (name : string) : RULE_DEF_ID =
    match engines.[eid].rule_defs |> try_get_index (RuleName name) with
    | Some rule_def_id -> RuleDefId rule_def_id
    | None -> failwith (sprintf "Engine.get_named_rule_id: function '%s' not found in global context #%d" name eid)

and inline get_rule_def' (Engine eid) (RuleDefId id : RULE_DEF_ID) : RULE_DEF' * RULE_DEF_ATTRS =
    engines.[eid].rule_defs |> get id

and inline get_rule_name (Engine eid) (RuleDefId id : RULE_DEF_ID) = let RuleName r_name, _ =engines.[eid].rule_defs |> get id in r_name
and inline get_rule_id (eng : ENGINE) (id : RULE_DEF_ID) = (snd (get_rule_def' eng id)).rule_id
and inline get_rule_def (eng as Engine eid) (id : RULE_DEF_ID) = (snd (get_rule_def' eng id)).rule_def

and inline make_rule (Engine eid) (R' : RULE') : RULE =
    let e = engines.[eid]
    e.rules |> add (R', ()) |> Rule

and inline get_rule' (Engine eid) (Rule rid) = engines.[eid].rules |> get rid |> fst

and inline UpdateRule eng ((f, ts), t_rhs) = make_rule eng (UpdateRule' ((f, ts), t_rhs))
and inline CondRule eng (G, R1, R2) = make_rule eng (CondRule' (G, R1, R2))
and inline ParRule eng Rs = make_rule eng (ParRule' Rs)
and inline SeqRule eng Rs = make_rule eng (SeqRule' Rs)
and inline IterRule eng R' = make_rule eng (IterRule' R')
and inline LetRule eng (v, t1, R') = make_rule eng (LetRule' (v, t1, R'))
and inline MacroRuleCall eng (r, args) = make_rule eng (MacroRuleCall' (r, args))
and inline ForallRule eng (v, t_set, G, R') = make_rule eng (ForallRule' (v, t_set, G, R'))
and inline S_Updates eng upds = make_rule eng (S_Updates' upds)   // Map.map (fun ((f, xs), t_rhs) -> ((get_fct_id eng f, xs), convert_term eng t_rhs)) upds

and convert_rule (eng : ENGINE) (R : AST.RULE) : RULE =
    AST.rule_induction (convert_term eng) {
        UpdateRule = fun ((f, ts), t_rhs) -> UpdateRule eng ((get_fct_id eng f, ts), t_rhs);
        CondRule   = fun (G, R1, R2) -> CondRule eng (G, R1, R2);
        ParRule    = fun Rs -> ParRule eng Rs;
        SeqRule    = fun Rs -> SeqRule eng Rs;
        IterRule   = fun R' -> IterRule eng R';
        LetRule    = fun (v, t1, R') -> LetRule eng (v, t1, R');
        MacroRuleCall = fun (r_name, args) -> MacroRuleCall eng (get_rule_def_id eng r_name, args);
        ForallRule = fun (v, t_set, G, R') -> ForallRule eng (v, t_set, G, R');
        S_Updates  = fun upds -> S_Updates eng (Set.map (fun ((f, xs), t_rhs) -> (get_fct_id eng f, xs), convert_term eng t_rhs) upds)
    } R

and new_engine (sign : Signature.SIGNATURE, initial_state : State.STATE, fct_def_db : AST.MACRO_DB, rule_def_db : AST.RULES_DB, invariants : Map<string, AST.TYPED_TERM>, smt_ctx : SmtInterface.SMT_CONTEXT) : ENGINE =
    let eid = engines.Count
    let new_engine = {
        signature       = sign
        initial_state   = initial_state
        invariants      = Map.empty
        functions       = newIndMap<FUNCTION', FUNCTION_ATTRS>()
        rule_defs       = newIndMap<RULE_DEF', RULE_DEF_ATTRS>()
        terms           = newIndMap<TERM', TERM_ATTRS>()
        rules           = newIndMap<RULE', RULE_ATTRS>()
        TRUE_           = ref None
        FALSE_          = ref None
        AND_            = ref None
        OR_             = ref None
        NOT_            = ref None
        EQUALS_         = ref None
        smt_ctx         = smt_ctx
    }
    engines.Add new_engine
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
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) -> Some (Derived (args, convert_term (Engine eid) body))   // !!! convert_term here is problematic, because functions are not yet in fctTable, see how it is done for the other kinds of functions
                |   None -> failwith (sprintf "Engine.new_engine: derived function '%s' is in signature, but is not defined\n" f_name)
        |   Signature.Monitored -> failwith (sprintf "Engine.new_engine: monitored function '%s' - not implemented" f_name)
        |   Signature.Shared -> failwith (sprintf "Engine.new_engine: shared function '%s' - not implemented" f_name)
        |   Signature.Out -> failwith (sprintf "Engine.new_engine: out function '%s' - not implemented" f_name)
    let extract_rule_def_rhs r_name =
        match rule_def_db |> Map.tryFind r_name with
        |   Some (args, R) -> (args, R)
        |   None -> failwith (sprintf "Engine.new_engine: no definition found for rule macro '%s'\n" r_name)
    let add_functions fct_list =
        fct_list
            |> List.map (fun (name, _) -> (name, extract_fct_interpretation_if_possible name))
            |> List.filter (function (_, None) -> false | _ -> true)
            |> Seq.iteri ( fun i (name, opt_fct_interpretation) ->
                match opt_fct_interpretation with
                |   None -> ()
                |   Some fct_interpretation ->
                        new_engine.functions |> add (
                            FctName name, {
                                fct_id   = i;
                                fct_kind = Signature.fct_kind name sign;
                                // fct_type = Signature.fct_types name sign;   // !!! to be implemented together with monomorphization
                                fct_interpretation = fct_interpretation
                            }) |> ignore )
    let functions = sign |> Map.toList |> List.filter (fun (name, _) -> Signature.is_function_name name sign)
    // add to engine non-derived functions first, then derived functions
    functions |> List.filter (fun (name, _) -> not (Signature.fct_kind name sign = Signature.Derived)) |> add_functions
    functions |> List.filter (fun (name, _) -> Signature.fct_kind name sign = Signature.Derived) |> add_functions
    // add rules
    rule_def_db |> Map.toList
        |> List.map (fun (name, _) -> (name, extract_rule_def_rhs name))
        |> Seq.iteri (fun i (name, rule_def) ->
            new_engine.rule_defs |> add (
                RuleName name, {
                    rule_id   = i;
                    // rule_type = Signature.rule_types name sign;   // !!! to be implemented together with monomorphization
                    rule_def  = None
                }) |> ignore )
    for i in 0..(new_engine.functions |> count) - 1 do
        let FctName f_name, (f_attrs as { fct_interpretation = fct_intp }) = new_engine.functions |> get i
        match fct_intp with
        |   StaticUserDefined (fct_interp, None) ->
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) ->
                        new_engine.functions |> set i (FctName f_name, { f_attrs with fct_interpretation = StaticUserDefined (fct_interp, Some (args, convert_term (Engine eid) body)) })
                |   None -> failwith (sprintf "cannot find definition of static function '%s'\n" f_name)
        |   ControlledInitial (fct_interp, None) ->
                match fct_def_db |> Map.tryFind f_name with
                |   Some (args, body) ->
                        new_engine.functions |> set i (FctName f_name, { f_attrs with fct_interpretation = ControlledInitial (fct_interp, Some (args, convert_term (Engine eid) body)) })
                |   None -> failwith (sprintf "cannot find initial definition of controlled function '%s'\n" f_name)
        |   _ -> ()     // if not any of the above cases, do nothing (the entry of fctTable was already completely initialized)
    for i in 0..(new_engine.rule_defs |> count) - 1 do
        let RuleName rd_name, (rd_attrs as { rule_id = id; rule_def = _ }) = new_engine.rule_defs |> get i
        let (args, body) = extract_rule_def_rhs rd_name
        new_engine.rule_defs |> set i (RuleName rd_name, { rd_attrs with rule_def = Some (args, convert_rule (Engine eid) body) })
    let new_ctx = {
        new_engine with
            invariants = Map.map (fun _ t -> convert_term (Engine eid) t) invariants
        }
    engines.[eid] <- new_ctx
    engines.[eid].TRUE_   := Some (Value (Engine eid) (BOOL true))
    engines.[eid].FALSE_  := Some (Value (Engine eid) (BOOL false))
    engines.[eid].AND_    := Some (get_fct_id (Engine eid) "and")
    engines.[eid].OR_     := Some (get_fct_id (Engine eid) "or")
    engines.[eid].NOT_    := Some (get_fct_id (Engine eid) "not")
    engines.[eid].EQUALS_ := Some (get_fct_id (Engine eid) "=")
    Engine eid

and get_engine' (Engine eid : ENGINE) : ENGINE' =
    if eid < engines.Count then
        engines.[eid]
    else
        failwith (sprintf "get_engine': engine %d not found" eid)

and initial_state_of (Engine eid) =
    engines.[eid].initial_state

and invariants_of (Engine eid) =
    engines.[eid].invariants

and smt_solver_push (Engine eid) =
    SmtInterface.smt_solver_push engines.[eid].smt_ctx

and smt_solver_pop (Engine eid) =
    SmtInterface.smt_solver_pop engines.[eid].smt_ctx

//--------------------------------------------------------------------
and term_induction (eng: ENGINE) (fct_id : FCT_ID -> 'fct_id) (F : TERM_INDUCTION<'fct_id, 'term>) (t : TERM) :'term =
    let term_ind = term_induction eng fct_id F
    match get_term' eng t with
    |   Value' x              -> F.Value x
    |   Initial' (f, xs)      -> F.Initial (fct_id f, xs)
    |   AppTerm' (f, ts)      -> F.AppTerm (fct_id f, List.map (fun t -> term_ind t) ts)
    |   CondTerm' (G, t1, t2) -> F.CondTerm (term_ind G, term_ind t1, term_ind t2)
    |   VarTerm' (v, ty)      -> F.VarTerm (v, ty)
    |   QuantTerm' (q_kind, v, t_set, t_cond) -> F.QuantTerm (q_kind, v, term_ind t_set, term_ind t_cond)
    |   LetTerm' (x, t1, t2)  -> F.LetTerm (x, term_ind t1, term_ind t2)
    |   DomainTerm' tyname    -> F.DomainTerm tyname

//--------------------------------------------------------------------

and skipRule eng = ParRule eng []

//--------------------------------------------------------------------

and rule_induction (eng: ENGINE) (term : TERM -> 'term) (F : RULE_INDUCTION<'term, 'rule>) (R : RULE) : 'rule =
    let rule_ind = rule_induction eng term
    match get_rule' eng R with
    |   S_Updates' U -> F.S_Updates U   // F.S_Updates (Map.map (fun loc -> fun t_rhs -> term t_rhs) U)
    |   UpdateRule' ((f, ts), t) -> F.UpdateRule ((f, List.map term ts), term t)
    |   CondRule' (G, R1, R2: RULE) -> F.CondRule (term G, rule_ind F R1, rule_ind F R2)
    |   ParRule' Rs -> F.ParRule (List.map (rule_ind F) Rs)
    |   SeqRule' Rs -> F.SeqRule (List.map (rule_ind F) Rs)
    |   IterRule' R -> F.IterRule (rule_ind F R)
    |   LetRule' (v, t, R) -> F.LetRule (v, term t, (rule_ind F) R)
    |   ForallRule' (v, t_set, t_filter, R) -> F.ForallRule (v, term t_set, term t_filter, (rule_ind F) R)
    |   MacroRuleCall' (r, ts) -> F.MacroRuleCall (r, List.map term ts)

//--------------------------------------------------------------------
//
//  pretty printing
//
//--------------------------------------------------------------------

and pp_list sep = function
|   []         -> []
|   [x]        -> [ x ]
|   (x :: xs') -> x :: (sep @ (pp_list sep xs'))

and pp_name (name : Signature.NAME) =
    (   match name with
    |   Signature.UndefConst -> "undef"
    |   Signature.BoolConst b -> if b then "true" else "false"
    |   Signature.IntConst i -> i.ToString()
    |   Signature.StringConst s -> "\"" + s + "\""
    |   Signature.FctName f -> f ) |> str

and pp_app_term sign = function
    |   (Signature.FctName f, [t1; t2]) when Signature.infix_status f sign <> Signature.NonInfix ->
            blo0 [ str "("; blo0 [ t1; brk 1; str (sprintf "%s " f); t2 ]; str ")" ]
    |   (Signature.FctName f, ts) when ts <> [] ->
            blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] ts); str ")" ]
    |   (name, _) -> pp_name name

and pp_location_term sign prefix = function
    |   (f : string, xs : VALUE list) when xs <> [] ->
            blo0 [ str (prefix+"["); str f; str "("; blo0 (pp_list [str",";brk 1] (List.map (fun x -> str (value_to_string x)) xs)); str ")]" ]
    |   (f, _) -> blo0 [ str $"{prefix}[{f}]" ]

and pp_term (eng : ENGINE) (t : TERM) =
    let sign = (get_engine' eng).signature
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    term_induction eng (fun x -> x) {
        AppTerm  = fun (f, ts) -> pp_app_term (Signature.FctName (fct_name eng f), ts);
        CondTerm = fun (G, t1, t2) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun x -> str (value_to_string x);
        Initial  = fun (f, xs) -> pp_location_term "initial" (fct_name eng f, xs);
        VarTerm = fun (x, _) -> str x;
        QuantTerm = fun (q_kind, v, t_set, t_cond) ->
            blo0 [ str ("("^(AST.quant_kind_to_str q_kind)^" "); str v; str " in "; t_set; str " with "; t_cond; str ")" ];
        LetTerm = fun (v, t1, t2) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
        DomainTerm = fun tyname -> str (Signature.type_to_string tyname);
    } t

and pp_rule (eng : ENGINE)  (R : RULE) =
    let sign = (get_engine' eng).signature
    let (pp_app_term, pp_term) = (pp_app_term sign, pp_term eng)
    rule_induction eng pp_term {
        S_Updates = fun U ->
                        let pp_elem ((f, xs), t) = blo0 [ str (fct_name eng f); str " "; str "("; blo0 (pp_list [str",";brk 1] (xs >>| fun x -> str (value_to_string x))); str ") := "; (pp_term t) ]
                        let L = Set.toList U >>| pp_elem
                        blo0 [ str "{"; line_brk; blo2 ( pp_list [line_brk] L); line_brk; str "}" ];
        UpdateRule = fun ((f, ts), t) -> blo0 [ pp_app_term (Signature.FctName (fct_name eng f), ts); str " := "; t ];
        CondRule = fun (G, R1, R2) -> blo0 ( str "if " :: G:: str " then " :: line_brk :: blo2 [ R1 ] :: line_brk ::
                                             (if R2 <> str "skip" then [ str "else "; line_brk; blo2 [ R2 ]; line_brk; str "endif" ] else [ str "endif"]) );
        ParRule = fun Rs -> if Rs <> [] then blo0 [ str "par"; line_brk; blo2 ( pp_list [line_brk] Rs); line_brk; str "endpar" ] else str "skip";
        SeqRule = fun Rs -> blo0 [ str "seq"; line_brk; blo2 (pp_list [line_brk] Rs); line_brk; str "endseq" ];
        IterRule = fun R' -> blo0 [ str "iterate "; line_brk; blo2 [ R' ]; line_brk; str "enditerate" ];
        LetRule = fun (v, t, R) -> blo0 [ str "let "; str v; str " = "; t; line_brk; str "in "; R; line_brk; str "endlet" ];
        ForallRule = fun (v, t_set, t_filter, R) -> blo0 [ str "forall "; str v; str " in "; t_set; str " with "; t_filter; str " do"; line_brk; blo2 [ R ]; line_brk; str "endforall" ];
        MacroRuleCall = fun (r, ts) -> blo0 [ str (get_rule_name eng r); str "["; blo0 (pp_list [str",";brk 1] ts); str "]" ];
    } R


and name_to_string t      = t |> pp_name |> PrettyPrinting.toString 80
and term_to_string sign t = t |> pp_term sign |> PrettyPrinting.toString 80
and rule_to_string sign t = t |> pp_rule sign |> PrettyPrinting.toString 80

let term_table_to_string eng =
    let e = get_engine' eng
    // let index_s = e.terms |> show_index (fun t' -> term_to_string eng (get_term eng t'))
    let show_table_entry (i, t', { term_type = ty }) =
        if i <> (get_term_attrs eng (get_term eng t')).term_id then
            failwith (sprintf "term_table_to_string: term id %d does not match index %d" (get_term_attrs eng (get_term eng t')).term_id i)
        else
            sprintf "%d: %s : %s"
                i (term_to_string eng (get_term eng t')) (Signature.type_to_string ty)
    let table_s = e.terms |> show_table show_table_entry
    // index_s + table_s
    table_s

//--------------------------------------------------------------------
//
//  function tables
//
//--------------------------------------------------------------------

let show_fct_tables (eng as Engine eid: ENGINE) =
    let e = get_engine' eng
    let index_s = e.functions |> show_index (fun (FctName f_name) -> f_name)
    let show_table_entry (i, FctName f_name, { fct_kind = f_kind; fct_id = f_id; fct_interpretation = f_intp }) =
        if i <> f_id then
            failwith (sprintf "show_fct_tables: function id %d does not match index %d" f_id i)
        else
            sprintf "%d: %s (%s) = [%s]"
                f_id f_name (Signature.fct_kind_to_string f_kind)
                (match f_intp with
                    | Constructor _ -> "constructor"
                    | StaticSymbolic _ -> "static (symbolic)"
                    | StaticBackground _ -> "static (background)"
                    | StaticUserDefined _ -> "static (user-defined)"
                    | ControlledInitial _ -> "controlled (initial)"
                    | ControlledUninitialized -> "controlled (uninitialized)"
                    | Derived (args, body) -> sprintf "derived (%s) = %s" (String.concat ", " args) (term_to_string eng body) )
    let table_s = e.functions |> show_table show_table_entry
    index_s + table_s

//--------------------------------------------------------------------
//
//  locations, symbolic updates, symbolic update sets
//
//--------------------------------------------------------------------

let location_to_string eng ((f, xs) : LOCATION) : string = Updates.location_to_string (fct_name eng f, xs)

let show_s_update eng ((f, xs), t) =
    let f = fct_name eng f
    sprintf "%s := %s"
        (if List.isEmpty xs then f else sprintf "%s (%s)" f (String.concat ", " (List.map value_to_string xs)))
        (PrettyPrinting.toString 80 (pp_term eng t))

let show_s_update_set eng (U :UPDATE_SET) =
    "{ " +
    ( Set.toList U >>| show_s_update eng
        |> String.concat ", "   ) +
    " }"

let show_s_update_map eng (U :UPDATE_MAP) =
    let s_update_set = Set.ofSeq (Map.toSeq U |> Seq.collect (fun (f : FCT_ID, table) -> table |> Map.toSeq |> Seq.map (fun (args, value) -> (f, args), value)))
    show_s_update_set eng s_update_set

//--------------------------------------------------------------------
    
type ErrorDetails =
|   InconsistentUpdates of ENGINE * TERM list option * UPDATE * UPDATE * UPDATE_SET option

exception Error of ENGINE * string * string * ErrorDetails

let error_msg (eng : ENGINE, modul : string, fct : string, err : ErrorDetails) = 
    sprintf "error - function %s.%s:\n" modul fct +
    match err with
    |   InconsistentUpdates (eng, opt_conditions, u1, u2, opt_u_set) ->
            (   sprintf "\n--- inconsistent updates:\n%s\n%s\n" (show_s_update eng u1) (show_s_update eng u2) ) +
            (   match opt_conditions with    
                |   None -> ""
                |   Some ts ->
                        sprintf "\n--- initial state conditions leading to the inconsistent updates:\n%s\n"
                            (String.concat "\n" (ts >>| term_to_string eng)) ) +
            (   match opt_u_set with
                |   None -> ""
                |   Some U ->
                        sprintf "\n--- updates collected on this path so far:\n%s\n" (String.concat "\n" (List.map (show_s_update eng) (List.ofSeq U))) )

let add_s_update eng (U : UPDATE_MAP) (u as (loc as (f, args), value): UPDATE) =
    if !trace > 0 then fprintf stderr "%sadd_s_update: %s\n" (spaces()) (show_s_update eng u)
    Map.change f
        ( function None -> Some (Map.add args value Map.empty)
                 | Some table ->
                        Some (  if Map.containsKey args table
                                then if value <> Map.find args table  // deal with conflicting updates
                                     then raise (Error (eng, module_name, "add_s_update", InconsistentUpdates (eng, None, (loc, Map.find args table), (loc, value), None)))
                                     else table
                                else Map.add args value table ) )
        U

let s_update_set_to_s_update_map eng (U : UPDATE_SET) =
    Set.fold (add_s_update eng) Map.empty U

let consistent eng (U : UPDATE_SET) =
    try let x = s_update_set_to_s_update_map eng U
        in true
    with Failure _ -> false
    
let locations (U : UPDATE_SET) : Set<LOCATION> =
    Set.map (fun (loc, value) -> loc) U

let seq_merge_2 eng (U : UPDATE_SET) (V : UPDATE_SET) =
    if not (consistent eng U)
    then U
    else let U_reduced = Set.filter (fun (loc, _) -> not (Set.contains loc (locations V))) U
         in Set.union U_reduced V

let seq_merge_n eng (Us : UPDATE_SET list) : UPDATE_SET =
    List.fold (seq_merge_2 eng) Set.empty Us

let apply_s_update_map (UM0 : UPDATE_MAP) (UM' : UPDATE_MAP) =
    let update_dynamic_function_table (f_table : Map<VALUE list, TERM>) (updates_of_f : Map<VALUE list, TERM>) =
            Map.fold (fun table args value -> Map.add args value table) f_table updates_of_f
    let apply_to_s_update_map (UM0 : UPDATE_MAP) (UM' : UPDATE_MAP) =
            Map.fold
                ( fun UM f updates_of_f ->
                    Map.change f
                        (function None -> Some (update_dynamic_function_table Map.empty updates_of_f) 
                                | Some f_table -> Some (update_dynamic_function_table f_table updates_of_f)) UM )
                UM0 UM'
    in  apply_to_s_update_map UM0 UM'

let apply_s_update_set eng S U =
    apply_s_update_map S (s_update_set_to_s_update_map eng U)

let sequel_s_state : ENGINE -> UPDATE_MAP -> UPDATE_SET -> UPDATE_MAP = apply_s_update_set

//--------------------------------------------------------------------

let get_env (env : ENV) (var : string) =
    Map.find var env

let add_binding (env : ENV) (var : string, t : TERM, ty : Signature.TYPE) =
    Map.add var (t, ty) env

(*
let replace_vars (eng : ENGINE) (env : ENV) (t : TERM) : TERM =
    term_induction eng (fun x -> x) {
        Value      = Value eng
        Initial    = Initial eng
        AppTerm    = AppTerm eng
        CondTerm   = CondTerm eng
        VarTerm    = fun (v, _) -> get_env env v |> fst
        QuantTerm  = QuantTerm eng
        LetTerm    = LetTerm eng
        DomainTerm = DomainTerm eng
    } t
*)

//--------------------------------------------------------------------

let get_values eng (ts : TERM list) : VALUE list option =    // only if all arguments are values
    List.fold ( function
                |   Some ts -> (fun t -> match get_term' eng t with Value' v -> Some(v :: ts) | _ -> None)
                |   None -> (fun _ -> None) ) (Some []) (List.rev ts)

//--------------------------------------------------------------------

let add_cond (G : TERM) (C : PATH_COND) = (Set.add G C)

//--------------------------------------------------------------------
//
//  SMT solver interface
//  
//--------------------------------------------------------------------

let rec smt_map_term (eng as Engine eid) (t : TERM) : SmtInterface.SMT_EXPR =
    let C = engines[eid].smt_ctx
    let (ctx, con, fct) = (!C.ctx, !C.con, !C.fct)

    let smt_map_ITE (eng as Engine eid) (G_, t1_, t2_) : SmtInterface.SMT_EXPR =
        let err_msg (G, T_G, t1, T_t1, t2, T_t2) =
            failwith (sprintf "smt_map_ITE: type error: for term %s the expected type is (Boolean, T, T), where T is Boolean, Integer or a user-defined type; type (%s, %s, %s) found instead"
                (term_to_string eng (CondTerm eng (G, t1, t2))) (Signature.type_to_string T_G) (Signature.type_to_string T_t1) (Signature.type_to_string T_t2) )
        match (smt_map_term eng G_, get_type eng G_, smt_map_term eng t1_, get_type eng t1_, smt_map_term eng t2_, get_type eng t2_) with
        |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_BoolExpr t1, Signature.Boolean, SmtInterface.SMT_BoolExpr t2, Boolean) ->
                SmtInterface.SMT_BoolExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.BoolExpr)
        |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_IntExpr t1, Signature.Integer, SmtInterface.SMT_IntExpr t2, Integer) ->
                SmtInterface.SMT_IntExpr (ctx.MkITE (G, t1 :> Microsoft.Z3.Expr, t2 :> Microsoft.Z3.Expr) :?> Microsoft.Z3.IntExpr)
        |   (SmtInterface.SMT_BoolExpr G, Signature.Boolean, SmtInterface.SMT_Expr t1, Signature.TypeCons (tyname1, []), SmtInterface.SMT_Expr t2, Signature.TypeCons (tyname2, [])) ->
                if tyname1 = tyname2
                then SmtInterface.SMT_Expr (ctx.MkITE (G, (t1 : Microsoft.Z3.Expr), (t2 : Microsoft.Z3.Expr)) : Microsoft.Z3.Expr)
                else err_msg (G_, Signature.Boolean, t1_, Signature.TypeCons (tyname1, []), t2_, Signature.TypeCons (tyname2, []))
        |   (_, T_G, _, T_t1, _, T_t2) -> err_msg (G_, T_G, t1_, T_t1, t2_, T_t2)

    let smt_map_app_term (eng : ENGINE) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
        let FctName f, { fct_id = fct_id; fct_kind = f_kind; fct_interpretation = fct_intp } = get_function' eng f_id
        if (match fct_intp with StaticBackground _ -> true | _ -> false) then 
            let es = ts >>| smt_map_term eng
            //let f' = get_function' eng f
            match (f, es) with
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
            |   _ -> failwith (sprintf "smt_map_term_background_function: error (t = %s)" (term_to_string eng (AppTerm eng (FctId fct_id, ts))))
        else failwith (sprintf "smt_map_app_term: '%s' is not a background function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

    let smt_map_initial (eng : ENGINE) (f_id : FCT_ID, ts) : SmtInterface.SMT_EXPR =
        let FctName f, { fct_kind = f_kind } = get_function' eng f_id
        if f_kind = Signature.Controlled then
            let sign = engines.[eid].signature
            let fail (f, dom, ran) =
                failwith (sprintf "smt_map_term_user_defined_function: function '%s : %s -> %s' not found" f (Signature.type_list_to_string dom) (Signature.type_to_string ran))
            match (f, Signature.fct_type f sign, ts >>| fun t -> smt_map_term eng t) with
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
            |   (f, (_, ran), _) -> failwith (sprintf "smt_map_term_user_defined_function : error (t = %s)" (term_to_string eng (AppTerm eng (f_id, ts))))
        else failwith (sprintf "smt_map_initial: '%s' is not a controlled function" f)   // smt_map_term_user_defined_function initial_flag sign C (f, ts)

    match get_smt_expr eng t with
    |   Some e -> e
    |   None ->
            let result = 
                match get_term' eng t with
                |   Value' (INT i)           -> SmtInterface.SMT_IntExpr (ctx.MkInt i)
                |   Value' (BOOL b)          -> SmtInterface.SMT_BoolExpr (ctx.MkBool b)
                |   Value' (CELL (cons, [])) -> SmtInterface.SMT_Expr (Map.find cons (!C.con))
                |   Initial' (f, xs)         -> smt_map_initial eng (f, xs >>| Value eng)
                |   CondTerm' (G, t1, t2)    -> smt_map_ITE eng (G, t1, t2)
                |   AppTerm' (f, ts)         -> smt_map_app_term eng (f, ts)
                |   _ -> failwith (sprintf "smt_map_term: not supported (t = %s)" (term_to_string eng t))
            set_smt_expr eng t result
            result

//--------------------------------------------------------------------
//
//  symbolic evaluator
//  
//  through the symbolic evaluation functions:
//  - S or eng   stands for engine
//  - env        stands for variable environment
//
//--------------------------------------------------------------------

let s_not eng (t : TERM) =
    let t = t
    if      t = TRUE  eng then FALSE eng
    else if t = FALSE eng then TRUE eng
    else AppTerm eng (NOT eng, [t])

let s_equals eng (eval_t1 : unit -> TERM, eval_t2 : unit -> TERM) =
    let t1, t2 = eval_t1 (), eval_t2 ()
    if t1 = t2 then TRUE eng
    else match get_term' eng t1, get_term' eng t2 with
         |   Value' x1, Value' x2 -> if x1 = x2 then TRUE eng else FALSE eng
         |   _, _ -> AppTerm eng (EQUALS eng, [t1; t2])
 
let s_and eng (eval_t1, eval_t2) =
    let TRUE, FALSE = TRUE eng, FALSE eng
    let t1 = eval_t1 ()
    if      t1 = FALSE then FALSE
    else if t1 = TRUE  then eval_t2 ()
    else let t2 = eval_t2 ()
         if      t2 = FALSE then FALSE
         else if t2 = TRUE  then t1
         else if t1 = t2 then t1
         else AppTerm eng (AND eng, [t1; t2])

let s_or eng (eval_t1, eval_t2) =
    let TRUE, FALSE = TRUE eng, FALSE eng
    let t1 = eval_t1 ()
    if      t1 = TRUE  then TRUE
    else if t1 = FALSE then eval_t2 ()
    else let t2 = eval_t2 ()
         if      t2 = TRUE  then TRUE
         else if t2 = FALSE then t1
         else if t1 = t2 then t1
         else AppTerm eng (OR eng, [t1; t2])

let s_xor eng (eval_t1, eval_t2) =
    let TRUE, FALSE = TRUE eng, FALSE eng
    let t1 = eval_t1 ()
    if      t1 = FALSE then eval_t2 ()
    else if t1 = TRUE  then s_not eng (eval_t2 ())
    else let t2 = eval_t2 ()
         if      t2 = FALSE then t1
         else if t2 = TRUE  then s_not eng t1
         else if t1 = t2 then FALSE
         else AppTerm eng (get_fct_id eng "xor", [t1; t2])

let s_implies eng (eval_t1, eval_t2) =
    let TRUE, FALSE = TRUE eng, FALSE eng
    let t1 = eval_t1 ()
    if      t1 = FALSE then TRUE
    else if t1 = TRUE  then eval_t2 ()
    else let t2 = eval_t2 ()
         if      t2 = TRUE  then TRUE
         else if t2 = FALSE then s_not eng t1
         else if t1 = t2 then TRUE
         else AppTerm eng (get_fct_id eng "implies", [t1; t2])

let s_iff eng (eval_t1, eval_t2) =
    let TRUE, FALSE = TRUE eng, FALSE eng
    let t1 = eval_t1 ()
    if      t1 = FALSE then s_not eng (eval_t2 ())
    else if t1 = TRUE  then eval_t2 ()
    else let t2 = eval_t2 ()
         if      t2 = FALSE then s_not eng t1
         else if t2 = TRUE  then t1
         else if t1 = t2 then TRUE
         else AppTerm eng (get_fct_id eng "iff", [t1; t2])

let ctx_condition eng C =
    List.fold (fun a -> fun b -> s_and eng ((fun () -> a), (fun () -> b))) (TRUE eng) (Set.toList C)

let smt_assert (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_type eng phi = Signature.Boolean
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; (!C.slv).Assert be
         | _ -> failwith (sprintf "smt_assert: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_assert' expects a Boolean term, %s found instead " (term_to_string eng phi))

let with_extended_path_cond (eng : ENGINE) (G : TERM) (eval_fct : 'a -> ENGINE -> UPDATE_MAP * ENV * PATH_COND -> 'a) (term_or_rule : 'a) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : 'a =
    smt_solver_push eng
    smt_assert eng G
    let result = eval_fct term_or_rule eng (UM, env, add_cond G pc)
    smt_solver_pop eng
    result

//--------------------------------------------------------------------

let smt_formula_is_true (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_type eng phi = Signature.Boolean
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check ((!C.ctx).MkNot be) = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_true: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_formula_is_true' expects a Boolean term, %s found instead " (term_to_string eng phi))

let smt_formula_is_false (eng as Engine eid) (phi : TERM) =
    let C = engines.[eid].smt_ctx
    if get_type eng phi = Signature.Boolean
    then match smt_map_term eng phi with
         | SmtInterface.SMT_BoolExpr be -> C.ctr := !C.ctr + 1; ((!C.slv).Check be = Microsoft.Z3.Status.UNSATISFIABLE)
         | _ -> failwith (sprintf "smt_formula_is_false: error converting Boolean term (term = %s)" (term_to_string eng phi))
    else failwith (sprintf "'smt_formula_is_false' expects a Boolean term, %s found instead " (term_to_string eng phi))

let rec interpretation (eng : ENGINE) (UM : UPDATE_MAP) (pc : PATH_COND) (f as FctId f_id) (xs : VALUE list) =
    let AppTerm, Value, Initial, get_type = AppTerm eng, Value eng, Initial eng, get_type eng
    let eval_fct_definition_in_curr_state (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> let val_x = Value x in add_binding env' (arg, val_x, get_type val_x)) Map.empty args xs
        // first element of triple = UM  =>  evaluate in current state
        s_eval_term body eng (UM, env, Set.empty)           //!!!! to be modified if at some point initial state constraints are implemented => path condition may then be non-empty
    let eval_fct_definition_in_initial_state (fct_definition as (args, body)) xs =
        let env = List.fold2 (fun env' arg x -> let val_x = Value x in add_binding env' (arg, val_x, get_type val_x)) Map.empty args xs
        let body' = body              // to do actual args replacement: // let body' = replace_vars eng env body
        // first element of triple = Map.empty  =>  evaluate in initial state
        s_eval_term body' eng (Map.empty, env, Set.empty)   //!!!! to be modified if at some point initial state constraints are implemented => path condition may then be non-empty
    let FctName f_name, { fct_interpretation = f_intp; fct_id = f_id } = get_function' eng f
    match f_intp with
    |   Constructor (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticBackground (fct_interpretation : VALUE list -> VALUE) ->
            Value (fct_interpretation xs)
    |   StaticUserDefined (_ : VALUE list -> VALUE, Some (fct_def : string list * TERM)) ->
            // memoization of computed values for static user-defined functions
            let res = initial_state_eval_res eng (AppTerm (f, xs >>| Value))
            match !res with
            |   Some t' -> t'
            |   None -> let t' = eval_fct_definition_in_initial_state fct_def xs in res := Some t'; t'
    |   ControlledInitial (_ : VALUE list -> VALUE, Some (fct_def : string list * TERM)) -> 
            try Map.find xs (Map.find (FctId f_id) UM)
            with _ ->
                let res = initial_state_eval_res eng (AppTerm (f, xs >>| Value))
                match !res with
                |   Some t' -> t'
                |   None -> let t' = eval_fct_definition_in_initial_state fct_def xs in res := Some t'; t'
    |   ControlledUninitialized ->
            try Map.find xs (Map.find (FctId f_id) UM)
            with _ -> Initial (f, xs)
    |   Derived (fct_def : string list * TERM) ->
            eval_fct_definition_in_curr_state fct_def xs
    |   StaticSymbolic (s_fct_interpretation: TERM list -> TERM) ->
            failwith (sprintf "Engine.interpretation: static symbolic function '%s' - not implemented" f_name)
    |   StaticUserDefined (_, None) ->
            failwith (sprintf "definition of static function '%s' missing" f_name)
    |   ControlledInitial (_, None) -> 
            failwith (sprintf "initial state definition of controlled function '%s' missing" f_name)

and smt_eval_formula (eng : ENGINE) (phi : TERM) (UM : UPDATE_MAP, env, pc : PATH_COND) =
    // precondition: term_type sign phi = Boolean
    if !trace > 0 then fprintf stderr "smt_eval_formula(%s) -> " (term_to_string eng phi)
    let phi = expand_term eng phi (UM, env, pc)
    let result =
        if smt_formula_is_true eng phi
        then TRUE eng
        else if smt_formula_is_true eng (s_not eng phi)
        then FALSE eng
        else phi
    if !trace > 0 then fprintf stderr "%s\n" (term_to_string eng result)
    result

and expand_term (eng : ENGINE) t (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let get_type = get_type eng
    term_induction eng (fun x -> x) {
        Value   = fun x (UM, env, pc) -> Value eng x;
        Initial = fun (f, xs) (UM, env, pc) -> Initial eng (f, xs)
        AppTerm = fun (f, ts) (UM : UPDATE_MAP, env, pc) ->
            let FctName name, { fct_kind = f_kind; fct_interpretation = f_intp } = get_function' eng f
            match f_intp with
            |   StaticUserDefined (_, Some (args, body)) ->
                    let ts = ts >>| fun t -> t (UM, env, pc)
                    let env = List.fold2 (fun env' arg t -> add_binding env' (arg, s_eval_term t eng (UM, env, pc), get_type t)) Map.empty args ts
                    s_eval_term body eng (UM, env, pc)
            | _ -> AppTerm eng (f, ts >>| fun t -> t (UM, env, pc))
        CondTerm  = fun (G, t1, t2) (UM : UPDATE_MAP, env, pc) -> CondTerm eng (G (UM, env, pc), t1 (UM, env, pc), t2 (UM, env, pc));
        VarTerm   = fun (v, _) (UM : UPDATE_MAP, env, pc) -> fst (get_env env v);
        QuantTerm = fun (q_kind, v, t_set, t_cond) (UM : UPDATE_MAP, env, pc) -> expand_quantifier eng (q_kind, v, t_set, t_cond) (UM, env, pc);
        LetTerm   = fun (v, t1, t2) (UM : UPDATE_MAP, env, pc) ->
                        let t1_val = t1 (UM, env, pc)
                        t2 (UM, add_binding env (v, t1_val, get_type t1_val), pc);
        DomainTerm = fun dom (UM : UPDATE_MAP, env, pc) ->
            match State.enum_finite_type dom (initial_state_of eng) with
            |   Some xs -> Value eng (SET (Signature.main_type_of dom, xs))
            |   _ -> failwith (sprintf "Engine.expand_term: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))
    } t ((UM : UPDATE_MAP), (env : ENV), (pc : PATH_COND))

and expand_quantifier (eng : ENGINE) (q_kind, v, t_set : UPDATE_MAP * ENV * PATH_COND -> TERM, t_cond : UPDATE_MAP * ENV * PATH_COND -> TERM)
                        (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    // !!! tbd: code duplication, check whether code from s_eval_term can be reused
    let t_set = t_set (UM, env, pc)
    let t_set_type = get_type eng t_set
    let elem_type =
        match t_set_type with
        |   Signature.Powerset tyname -> tyname
        |   _ -> failwith (sprintf "Engine.expand_quantifier: expected a set or domain type, %s found instead" (Signature.type_to_string t_set_type))
    match get_term' eng (s_eval_term t_set eng (UM, env, pc)) with
    |   Value' (SET (_, xs)) ->
            let eval_instance x = t_cond (UM, add_binding env (v, Value eng x, elem_type), pc)
            let t_conds = List.map eval_instance (Set.toList xs)
            match q_kind with
            |   AST.Forall -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_and eng ((fun () -> t_accum), (fun () -> t1))) (TRUE eng)  t_conds
            |   AST.Exist  -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_or  eng ((fun () -> t_accum), (fun () -> t1))) (FALSE eng) t_conds
            |   AST.ExistUnique -> failwith "Engine.expand_quantifier: 'ExistUnique' not implemented"
    |   x -> failwith (sprintf "Engine.expand_quantifier: not a set (%s)" (term_to_string eng t_set))

and cases eng (condConstructor : ENGINE -> TERM * 'a * 'a -> 'a) (t : TERM) (x_t_list : (VALUE * 'a) list) : 'a =
    // the second element of the pairs in x_t_list is typically of type
    //  - TERM (then the parameter 'condConstructor' should be 'CondTerm'), or
    //  - RULE (then the parameter 'condConstructor' should be 'CondRule')
    let eq t1 t2 = s_equals eng (K t1, K t2)
    let rec mk_cond_term = function
    |   [] -> failwith "cases: empty list of cases"
    |   [(x1, t1)] -> t1        // does not use x1, because this is the 'else' case
    |   (x1, t1) :: cases' -> condConstructor eng (eq t (Value eng x1), t1, mk_cond_term cases')
    mk_cond_term x_t_list

and s_eval_term_ expand_initial (t : TERM) (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
    let cases = cases eng CondTerm
    let TRUE, FALSE, get_term', fct_kind = TRUE eng, FALSE eng, get_term' eng, fct_kind eng
    let s_and, s_or, s_not, s_xor, s_implies, s_iff, s_equals = s_and eng, s_or eng, s_not eng, s_xor eng, s_implies eng, s_iff eng, s_equals eng
    let Initial, Value, AppTerm, CondTerm, VarTerm, LetTerm, DomainTerm, QuantTerm = Initial eng, Value eng, AppTerm eng, CondTerm eng, VarTerm eng, LetTerm eng, DomainTerm eng, QuantTerm eng
    let get_type, pp_term, term_to_string = get_type eng, pp_term eng, term_to_string eng

    if !trace > 0 then
        fprintf stderr "%s[[ %s ]]_{%s, {%s}, {%s}}\n" (spaces()) (indent (pp_term t)) (show_s_update_map eng UM) (env_to_string eng env) (pc |> Set.toList >>| term_to_string |> String.concat ", ")
        level := !level + 1

    let rec eval_term_with_ext_path_cond expand_initial (G : TERM) (t : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) =
        with_extended_path_cond eng G (fun t eng -> eval_term expand_initial t) t (UM, env, pc)

    and lazy_eval_term expand_initial t (UM, env, pc) = fun () -> eval_term expand_initial t (UM, env, pc)

    and eval_app_term (expand_initial : bool) (f : FCT_ID, ts : TERM list) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
        if !trace > 0 then
            fprintf stderr "%s[[ %s ]]_{%s, {%s}, {%s}}\n" (spaces()) (indent (pp_term (AppTerm (f, ts)))) (show_s_update_map eng UM) (env_to_string eng env) (pc |> Set.toList >>| term_to_string |> String.concat ", ")
            level := !level + 1
        let t_string = term_to_string (AppTerm (f, ts))
        // Prevent dead code elimination by forcing evaluation
        let _ = if false then fprintf stderr "%s" t_string else ()
        let lazy_eval_term = lazy_eval_term expand_initial
        let FctName f_name, { fct_kind = f_kind }  = get_function' eng f
        let rec F (expand_initial : bool) (ts_past : TERM list, xs_past : VALUE list option) (ts_rest : TERM list) : TERM =
            let F = F expand_initial
            match ts_rest with
            // xs_past = Some values, if all terms in ts_past are fully evaluated; otherwise xs_past = None
            |   t1 :: ts_fut ->
                    let t1_string = term_to_string t1
                    let _ = if false then fprintf stderr "%s" t1_string else ()
                    let t1 = eval_term expand_initial t1 (UM, env, pc)
                    let t1_string_eval = term_to_string t1
                    let _ = if false then fprintf stderr "%s" t1_string_eval else ()
                    match get_term' t1 with
                    |   Value' x              -> F (t1 :: ts_past, Option.map (prepend x) xs_past) ts_fut
                    |   Initial' (f, xs)      -> //F (t :: ts_past, None) ts_fut
                            if not expand_initial then F (t1 :: ts_past, None) ts_fut
                            else
                                match State.enum_finite_type (get_type t1) (initial_state_of eng) with
                                |   None -> F (t1 :: ts_past, None) ts_fut
                                |   Some elems ->
                                        let cases_list = Set.toList elems >>| fun x -> x, F (ts_past, xs_past) (Value x :: ts_fut)
                                        eval_term expand_initial (cases t1 cases_list) (UM, env, pc)
                    |   CondTerm' (G1, t11, t12) -> CondTerm (G1, F (ts_past, xs_past) (t11 :: ts_fut), F (ts_past, xs_past) (t12 :: ts_fut)) // eval_term (CondTerm (G1, F (ts_past, xs_past) (t11 :: ts_fut), F (ts_past, xs_past) (t12 :: ts_fut))) (UM, env, pc)
                    |   AppTerm'  _           -> F (t1 :: ts_past, None) ts_fut
                    |   LetTerm'  (v, t1, t2) -> failwith "Engine.eval_app_term: LetTerm should not occur here"
                    |   VarTerm'  v           -> failwith "Engine.eval_app_term: VarTerm should not occur here"
                    |   QuantTerm' _          -> failwith "Engine.eval_app_term: QuantTerm should not occur here"
                    |   DomainTerm' _         -> failwith "Engine.eval_app_term: DomainTerm should not occur here"
            |   [] ->
                    match f, Option.map List.rev xs_past, List.rev ts_past, f_kind with
                    |   f, Some xs, _,  _ -> interpretation eng UM pc f xs      // fully evaluated case
                    |   f, None,    ts, Signature.Static -> AppTerm (f, ts)
                    |   f, None,    ts, Signature.Controlled -> failwith (sprintf "arguments of controlled function '%s' must be fully evaluable for unambiguous determination of a location\n('%s' found instead)" f_name (term_to_string (AppTerm (f, ts))))
                    |   f, None,    ts, Signature.Derived -> failwith (sprintf "function '%s' in term '%s': %s functions are not implemented" f_name (term_to_string t) (Signature.fct_kind_to_string (fct_kind f)))
                    |   f, None,    ts, _ -> failwith (sprintf "function '%s' in term '%s': %s functions are not supported" f_name (term_to_string t) (Signature.fct_kind_to_string (fct_kind f)))
        let t_result =
            match f_name, ts with
            |   "not", [ t1 ]     -> s_not (eval_term expand_initial t1 (UM, env, pc))
            |   "=",   [ t1; t2 ] -> s_equals (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   "and", [ t1; t2 ] -> s_and (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   "or",  [ t1; t2 ] -> s_or  (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   "xor", [ t1; t2 ] -> s_xor (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   "implies", [ t1; t2 ] -> s_implies (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   "iff", [ t1; t2 ] -> s_iff (lazy_eval_term t1 (UM, env, pc), lazy_eval_term t2 (UM, env, pc))
            |   _ -> match f_kind with
                        |   Signature.Controlled -> F true ([], Some []) ts     // all initial locations in a controlled function application are to be expanded, if possible
                        |   _ -> F expand_initial ([], Some []) ts              // otherwise continue with the inherited 'expand_initial' flag
        if !trace > 0 then 
            level := !level - 1
            fprintf stderr "%s-> %s\n" (spaces()) (indent (pp_term t_result))
        t_result

    and eval_cond_term expand_initial (G : TERM, t1 : TERM, t2 : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
        let eval_term, eval_bool_term = eval_term expand_initial, eval_bool_term expand_initial
        let G_eval = eval_bool_term G (UM, env, pc)
        match get_term' G_eval with
        |   Value' (BOOL true)  -> eval_term t1 (UM, env, pc)
        |   Value' (BOOL false) -> eval_term t2 (UM, env, pc)
        |   CondTerm' (G', G1, G2) ->
                eval_term (CondTerm (G', CondTerm (G1, t1, t2), CondTerm (G2, t2, t2))) (UM, env, pc)
                // let t1_G'_G1_eval         = eval_term t1 (UM, env, pc |> add_cond G'         |> add_cond G1)
                // let t2_G'_not_G1_eval     = eval_term t2 (UM, env, pc |> add_cond G'         |> add_cond (s_not G1))
                // let t1_not_G'_G2_eval     = eval_term t1 (UM, env, pc |> add_cond (s_not G') |> add_cond G2)
                // let t2_not_G'_not_G2_eval = eval_term t2 (UM, env, pc |> add_cond (s_not G') |> add_cond (s_not G2))
                // CondTerm (G', CondTerm (G1, t1_G'_G1_eval, t2_G'_not_G1_eval), CondTerm (G2, t1_not_G'_G2_eval, t2_not_G'_not_G2_eval))
        |   G' ->
                let t1_eval : TERM = eval_term_with_ext_path_cond expand_initial G_eval         t1 (UM, env, pc)
                let t2_eval : TERM = eval_term_with_ext_path_cond expand_initial (s_not G_eval) t2 (UM, env, pc)
                match get_term' t1_eval, get_term' t2_eval with
                |   Value' (BOOL true),  Value' (BOOL true) -> TRUE
                |   Value' (BOOL true),  Value' (BOOL false) -> G_eval
                |   Value' (BOOL false), Value' (BOOL true) -> s_not G_eval
                |   Value' (BOOL false), Value' (BOOL false) -> FALSE
                |   Value' (BOOL true),  _ -> s_or  (K G_eval,         K t2_eval)
                |   Value' (BOOL false), _ -> s_and (K (s_not G_eval), K t2_eval)
                |   _, Value' (BOOL true)  -> s_or  (K (s_not G_eval), K t1_eval)
                |   _, Value' (BOOL false) -> s_and (K G_eval,         K t1_eval)
                |   _, _ -> if t1_eval = t2_eval then t1_eval else CondTerm (G_eval, t1_eval, t2_eval)

    and eval_let_term expand_initial (v : string, t1 : TERM, t2 : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
        let eval_term = eval_term expand_initial
        let t1 = eval_term t1 (UM, env, pc)
        eval_term t2 (UM, add_binding env (v, t1, get_type t1), pc)

    and eval_domain_term (dom : Signature.TYPE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
        match State.enum_finite_type dom (initial_state_of eng) with
        |   Some xs -> Value (SET (Signature.main_type_of dom, xs))
        |   None -> failwith (sprintf "Engine.eval_domain_term: domain of type '%s' is not enumerable" (dom |> Signature.type_to_string))

    and eval_quant_term expand_initial (q_kind : AST.QUANT_KIND, v : string, t_set : TERM, t_cond : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : TERM =
        let t_set = eval_term true t_set (UM, env, pc)    // always unfold the term defining the set
        let t_set_type = get_type t_set
        let elem_type =
            match t_set_type with
            |   Signature.Powerset tyname -> tyname
            |   _ -> failwith (sprintf "Engine.eval_quant_term: expected a set or domain type, %s found instead" (Signature.type_to_string t_set_type))
        match get_term' (s_eval_term t_set eng (UM, env, pc)) with
        |   Value' (Background.SET (_, xs)) ->
                let eval_instance x = eval_term expand_initial t_cond (UM, add_binding env (v, Value x, elem_type), pc)
                let t_conds = List.map eval_instance (Set.toList xs)
                match q_kind with
                |   AST.Forall -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_and ((fun () -> t_accum), (fun () -> t1))) TRUE  t_conds
                |   AST.Exist  -> List.fold (fun (t_accum : TERM) -> fun (t1 : TERM) -> s_or  ((fun () -> t_accum), (fun () -> t1))) FALSE t_conds
                |   AST.ExistUnique -> failwith "Engine.eval_quant_term: 'ExistUnique' not implemented"
        |   x -> failwith (sprintf "Engine.eval_quant_term: not a set (%s)" (term_to_string t_set))

    and eval_term (expand_initial : bool) (t : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) =
        match get_term' t with
        |   Value' _              -> t
        |   Initial' _            -> t
        |   VarTerm' (v, ty)      -> fst (get_env env v);
        |   AppTerm' (f, ts)      -> eval_app_term expand_initial (f, ts) (UM, env, pc)
        |   CondTerm' (G, t1, t2) -> eval_cond_term expand_initial (G, t1, t2) (UM, env, pc)
        |   LetTerm' (v, t1, t2)  -> eval_let_term expand_initial (v, t1, t2) (UM, env, pc)
        |   DomainTerm' dom       -> eval_domain_term dom (UM, env, pc)
        |   QuantTerm' (q_kind, v, t_set, t_cond) -> eval_quant_term expand_initial (q_kind, v, t_set, t_cond) (UM, env, pc)

    and eval_bool_term (expand_initial : bool) (t : TERM) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) =
        // specialized version for boolean terms, possibly calling SMT solver
        // only to be called for terms known to be boolean
        let t_eval = eval_term expand_initial t (UM, env, pc)
        match get_term' t_eval with
        |   Value' (BOOL _) ->
                t_eval
        |   _ -> // (* optionally *) if Set.contains t_eval pc then TRUE else if Set.contains (s_not t_eval) pc then FALSE else
                smt_eval_formula eng t_eval (UM, env, pc)

    let t_result =
        match get_type t with
        |   Signature.Boolean -> eval_bool_term expand_initial t (UM, env, pc)
        |   _ -> eval_term expand_initial t (UM, env, pc)

    if !trace > 0 then 
        level := !level - 1
        fprintf stderr "%s-> %s\n" (spaces()) (indent (pp_term t_result))

    t_result

and s_eval_term = s_eval_term_ false
and s_eval_term_with_unfolding = s_eval_term_ true

//--------------------------------------------------------------------

and s_eval_rule (R : RULE) (eng : ENGINE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
    let cases = cases eng CondRule
    let Value, Initial, AppTerm, CondRule, UpdateRule, S_Updates = Value eng, Initial eng, AppTerm eng, CondRule eng, UpdateRule eng, S_Updates eng
    let ParRule, SeqRule, IterRule, skipRule = ParRule eng, SeqRule eng, IterRule eng, skipRule eng
    let eval_term t = s_eval_term t eng
    let eval_term_with_unfolding t = s_eval_term_with_unfolding t eng
    let get_type, rule_to_string, term_to_string, pp_rule = get_type eng, rule_to_string eng, term_to_string eng, pp_rule eng

    if (!trace > 1) then
        fprintf stderr "%s----------------------\n%ss_eval_rule %s\n%s\n\n" (spaces()) (spaces()) (show_s_update_map eng UM) (indent (pp_rule R))
        level := !level + 1

    let rec eval_rule_with_ext_path_cond (G : TERM) (R : RULE) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) =
        with_extended_path_cond eng G (fun R eng -> eval_rule R) R (UM, env, pc)

    and eval_update ((f, ts), t_rhs) (UM : UPDATE_MAP, env : ENV, pc : PATH_COND) : RULE =
        if !trace > 0 then fprintf stderr "%seval_update: %s\n" (spaces()) (indent (pp_rule (UpdateRule ((f, ts), t_rhs))))
        let t_rhs_eval = eval_term_with_unfolding t_rhs (UM, env, pc)
        let result =
            match get_term' eng t_rhs_eval with
            |   CondTerm' (G, t1, t2) ->
                    eval_rule (CondRule (G, UpdateRule ((f, ts), t1), UpdateRule ((f, ts), t2))) (UM, env, pc)
            |   _ ->
                let rec F (ts_past : TERM list, xs_past : VALUE list option) : TERM list -> RULE = function
                    |   (t1 :: ts_fut) ->
                        let t1 = eval_term_with_unfolding t1 (UM, env, pc)
                        match get_term' eng t1 with
                        |   Value' x1       -> F (t1 :: ts_past, Option.map (prepend x1) xs_past) ts_fut
                        |   Initial' _      -> //F (t1 :: ts_past, None) ts_fut
                                match State.enum_finite_type (get_type t1) (initial_state_of eng) with
                                |   None -> F (t1 :: ts_past, None) ts_fut
                                |   Some elems ->
                                        let cases_list = Set.toList elems >>| fun x -> x, F (ts_past, xs_past) (Value x :: ts_fut)
                                        eval_rule (cases t1 cases_list) (UM, env, pc)
                        |   CondTerm' (G1, t11, t12) -> eval_rule (CondRule (G1, F (ts_past, xs_past) (t11 :: ts_fut), F (ts_past, xs_past) (t12 :: ts_fut))) (UM, env, pc)
                        |   AppTerm' _      -> F (t1 :: ts_past, None) ts_fut
                        |   LetTerm' _      -> failwith "Engine.eval_update_rule: LetTerm should not occur here"
                        |   VarTerm' _      -> failwith "Engine.eval_update_rule: VarTerm should not occur here"
                        |   DomainTerm' _   -> failwith "Engine.eval_update_rule: DomainTerm should not occur here"
                        |   QuantTerm' _    -> failwith "Engine.eval_update_rule: QuantTerm should not occur here"
                    |   [] ->
                        match f, Option.map List.rev xs_past, List.rev ts_past with
                        |   f, Some xs, _  -> S_Updates (Set.singleton ((f, xs), t_rhs_eval))   // fully evaluated case
                        |   f, None,    ts ->
                                failwith (sprintf "Engine.eval_update: unable to fully evaluate lhs of update '%s := %s'"
                                        (term_to_string (AppTerm (f, ts))) (term_to_string t_rhs_eval))
                F ([], Some []) ts
        if !trace > 0 then fprintf stderr "%s-> %s\n" (spaces()) (indent (pp_rule result))
        result
 
    and eval_cond (G, R1, R2) (UM, env, pc) = 
        //let G = eval_term G (UM, env, pc)
        let G = eval_term_with_unfolding G (UM, env, pc)
        match get_term' eng G with
        |   Value' (BOOL true)  -> eval_rule R1 (UM, env, pc)
        |   Value' (BOOL false) -> eval_rule R2 (UM, env, pc)
        |   CondTerm' (G', G1, G2) ->
                eval_rule (CondRule (G', CondRule (G1, R1, R2), CondRule (G2, R1, R2))) (UM, env, pc)
        |   _ ->
                let R1' = eval_rule_with_ext_path_cond G             R1 (UM, env, pc)
                let R2' = eval_rule_with_ext_path_cond (s_not eng G) R2 (UM, env, pc)
                if R1' = R2' then R1' else CondRule (G, R1', R2')

    and eval_par Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_par R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_par R1 R2 (UM, env, pc) : RULE =
        match get_rule' eng (eval_rule R1 (UM, env, pc)) with
        |   S_Updates' U1 ->
                match get_rule' eng (eval_rule R2 (UM, env, pc)) with
                |   S_Updates' U2 ->
                        S_Updates (Set.union U1 U2)
                |   CondRule' (G2, R21, R22) ->
                        eval_rule (CondRule (G2, ParRule [ S_Updates U1; R21 ], ParRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R2))
        |   CondRule' (G1, R11, R12) ->
                eval_rule (CondRule (G1, ParRule [ R11; R2 ], ParRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_par: %s" (rule_to_string R1))

    and eval_seq Rs (UM, env, pc) =
        match Rs with
        |   []          -> S_Updates Set.empty
        |   [R1]        -> eval_rule R1 (UM, env, pc)
        |   R1 :: Rs    -> List.fold (fun R1 R2 -> eval_binary_seq R1 R2 (UM, env, pc)) R1 Rs

    and eval_binary_seq R1 R2 (UM, env, pc): RULE = 
        match get_rule' eng (eval_rule R1 (UM, env, pc)) with
        |   S_Updates' U1 ->
                let S' =
                    try sequel_s_state eng UM U1
                    with Error (_, _, _, InconsistentUpdates (C, _, u1, u2, _)) ->
                            raise (Error (C, module_name, "eval_rule.eval_binary_seq",
                                InconsistentUpdates (C, Some (List.ofSeq pc), u1, u2, Some U1)))
                match get_rule' eng (eval_rule R2 (S', env, pc)) with
                |   S_Updates' U2 ->
                        S_Updates (seq_merge_2 eng U1 U2)
                |   CondRule' (G2, R21, R22) ->
                        eval_rule (CondRule (G2, SeqRule [ S_Updates U1; R21 ], SeqRule [ S_Updates U1; R22 ])) (UM, env, pc)
                |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R2))
        |   CondRule' (G1, R11, R12) ->
                eval_rule (CondRule (G1, SeqRule [ R11; R2 ], SeqRule [ R12; R2 ])) (UM, env, pc)
        |   _ -> failwith (sprintf "eval_binary_seq: %s" (rule_to_string R1))

    and eval_iter R (UM, env, pc) =
        match get_rule' eng (eval_rule R (UM, env, pc)) with
        |   S_Updates' U ->
                if Set.isEmpty U
                then S_Updates Set.empty
                else eval_rule (SeqRule [ S_Updates U; IterRule R ]) (UM, env, pc)
        |   CondRule' (G, R1, R2) ->
                //eval_rule (SeqRule [ CondRule (G, R1, R2); IterRule R ]) (UM, env, pc)
                eval_rule (CondRule (G, SeqRule [R1; IterRule R], SeqRule [R2; IterRule R])) (UM, env, pc)
        |   R' -> failwith (sprintf "SymEvalRules.eval_rule: eval_iter_rule - R'' = %s" (rule_to_string (make_rule eng R')))
    
    and eval_let (v, t, R) (UM, env, pc) =
        let t' = eval_term t (UM, env, pc)
        let R' = eval_rule R (UM, add_binding env (v, t', get_type t'), pc)
        R'

    and eval_forall (v, ts, G, R) (UM, env, pc) =
        match get_term' eng (eval_term ts (UM, env, pc)) with
        |   Value' (SET (_, xs)) ->
                let eval_instance x =
                    let env' = let t_x = Value x in add_binding env (v, t_x, get_type t_x)
                    CondRule (eval_term G (UM, env', pc), eval_rule R (UM, env', pc), skipRule)
                let Rs = List.map (fun x -> eval_instance x) (Set.toList xs)
                eval_rule (ParRule Rs) (UM, env, pc)
        |   x -> failwith (sprintf "Engine.forall_rule: not a set (%A): %A v" ts x)

    and eval_macro_rule_call (r, args) (UM, env, pc) =
        let (formals, body) =
            match get_rule_def eng r with
            |   Some (formals, body) -> (formals, body)
            |   None -> failwith (sprintf "Engine.eval_macro_rule_call: macro rule '%s' not defined" (get_rule_name eng r))
        let env' =
            List.fold2 (fun env' formal arg -> add_binding env' (formal, eval_term arg (UM, env, pc), get_type arg)) env formals args
        eval_rule body (UM, env', pc)

    and eval_rule R (UM, env, pc) =
        match get_rule' eng R with
        |   UpdateRule' ((f, ts), t) -> eval_update ((f, ts), t) (UM, env, pc)
        |   CondRule' (G, R1, R2)    -> eval_cond (G, R1, R2) (UM, env, pc)
        |   ParRule' Rs              -> eval_par Rs (UM, env, pc)
        |   SeqRule' Rs              -> eval_seq Rs (UM, env, pc)
        |   IterRule' R              -> eval_iter R (UM, env, pc)
        |   LetRule' (v, t, R)       -> eval_let (v, t, R) (UM, env, pc) 
        |   ForallRule' (v, t, G, R) -> eval_forall (v, t, G, R) (UM, env, pc) 
        |   MacroRuleCall' (r, args) -> eval_macro_rule_call (r, args) (UM, env, pc)
        |   S_Updates' S             -> S_Updates S

    let R = eval_rule R (UM, env, pc)

    if (!trace > 1) then
        level := !level - 1
        fprintf stderr "%ss_eval_rule result = \n%s\n%s----------------------\n" (spaces()) (indent (pp_rule R)) (spaces())

    R


//--------------------------------------------------------------------
// convert partially evaluated terms and rules to regular ones

let rec reconvert_value (eng : ENGINE) x =
    match x with
    |   UNDEF    -> Value eng x
    |   BOOL b   -> Value eng x
    |   INT i    -> Value eng x
    |   STRING s -> Value eng x
    |   SET (_, fs) -> //AppTerm (FctName "asSet", ?????)
                    failwith "reconvert_value: SET not implemented yet"
    |   CELL (tag, args) -> AppTerm eng (get_fct_id eng tag, args >>| reconvert_value eng)

let reconvert_term (eng : ENGINE) t =
    term_induction eng (fun x -> x) {
        Value      = fun x -> reconvert_value eng x;
        Initial    = fun (f, xs) -> AppTerm eng (f, xs >>| Value eng);
        AppTerm    = AppTerm eng;
        CondTerm   = CondTerm eng;
        VarTerm    = VarTerm eng;
        QuantTerm  = QuantTerm eng;
        LetTerm    = LetTerm eng;
        DomainTerm = DomainTerm eng;
    } t

let reconvert_rule (eng : ENGINE) R = 
    rule_induction eng (reconvert_term eng) {
        UpdateRule = UpdateRule eng;
        CondRule   = CondRule eng;
        ParRule    = ParRule eng;
        SeqRule    = SeqRule eng;
        IterRule   = IterRule eng;
        LetRule    = LetRule eng;
        MacroRuleCall = MacroRuleCall eng;
        ForallRule = ForallRule eng;
        S_Updates  = fun upds -> ParRule eng (List.map (fun ((f, xs), t_rhs) -> UpdateRule eng ((f, xs >>| Value eng), reconvert_term eng t_rhs)) (Set.toList upds))
    } R

//--------------------------------------------------------------------

let count_s_updates eng = rule_induction eng (fun _ -> ()) {
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

let term_size eng =
    term_induction eng name_size {
        Value = fun _ -> 1;
        AppTerm = fun (f, ts : int list) -> 1 + f + List.sum ts;
        CondTerm = fun (G, t1, t2) -> 1 + G + t1 + t2;
        Initial = fun _ -> 1;
        VarTerm = fun _ -> 1;
        QuantTerm = fun (q_kind, v, t_set, t_cond) -> 1 + t_set + t_cond;
        LetTerm = fun (v, t1, t2) -> 1 + t1 + t2;
        DomainTerm = fun _ -> 1;
    }

let rule_size eng =
    rule_induction eng (term_size eng) {
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
let symbolic_execution (eng : ENGINE) (R_in : RULE) (steps : int) : int * RULE =
    if (!trace > 2) then fprintf stderr "symbolic_execution\n"
    if (steps <= 0) then failwith "Engine.symbolic_execution: number of steps must be >= 1"
    //  if (!trace > 2) then fprintf stderr "---\n%s\n---\n" (Signature.signature_to_string (signature_of C))
    let R_in_n_times = [ for _ in 1..steps -> R_in ]
    let R_in' = SeqRule eng (R_in_n_times @ [ skipRule eng ])      // this is to force the application of the symbolic update sets of R_in, thus identifying any inconsistent update sets
    let R_out = s_eval_rule R_in' eng (Map.empty, Map.empty, Set.empty)
    (count_s_updates eng R_out, reconvert_rule eng R_out)

let symbolic_execution_for_invariant_checking (eng : ENGINE) (opt_steps : int option) (R_in : RULE) : unit =
    let s_not = s_not eng
    let CondRule, UpdateRule, S_Updates = CondRule eng, UpdateRule eng, S_Updates eng
    let ParRule, SeqRule, IterRule, skipRule = ParRule eng, SeqRule eng, IterRule eng, skipRule eng

    let proc = Process.GetCurrentProcess()
    let capture_cpu_time (proc : Process) =
        (proc.TotalProcessorTime, proc.UserProcessorTime, proc.PrivilegedProcessorTime)
    let measure_cpu_time (proc : Process) (cpu0, usr0, sys0) =
        let (cpu1, usr1, sys1) = capture_cpu_time proc
        ( (cpu1 - cpu0).TotalMilliseconds, (usr1 - usr0).TotalMilliseconds, (sys1 - sys0).TotalMilliseconds )
    let (cpu0, usr0, sys0) = capture_cpu_time proc
    if (!trace > 2) then fprintf stderr "symbolic_execution_for_invariant_checking\n"
    let with_extended_path_cond = with_extended_path_cond eng
    match opt_steps with
    |   Some n -> if n < 0 then failwith "Engine.symbolic_execution_for_invariant_checking: number of steps must be >= 0"
    |   None -> ()
    let UM0 = Map.empty
    let invs = Map.toList (invariants_of eng)
    let counters = ref Map.empty
    let reset_counters () = counters := Map.empty
    let update_counters f inv_id = counters := Map.change inv_id (function Some (m, v, u) -> Some (f (m, v, u)) | None -> Some (f (0, 0, 0))) (!counters)
    let print_counters i () =
        printf "\n--- S_%d summary:\n\n" i
        Map.map (fun inv_id (m, v, u) -> printf "'%s': met on %d paths / definitely violated on %d paths / possibly violated on %d paths\n" inv_id m v u) !counters |> ignore
        let (cpu, usr, sys) = measure_cpu_time proc (cpu0, usr0, sys0)
        print_time (cpu, usr, sys)
        |> ignore
    let rec traverse i conditions R (UM, env, pc) : unit =
        let initial_state_conditions_to_reach_this_state ts =
            sprintf "- this path is taken when the following conditions hold in the initial state:\n%s"
                (String.concat "\n" (List.rev ts >>| fun t -> term_to_string eng (reconvert_term eng t)))
        let show_cumulative_updates sign updates =
            "- cumulative update set for this path:\n" ^
            String.concat "\n"
                (Set.toList updates >>| fun ((f, xs), t) ->
                    sprintf "%s%s := %s"
                        (fct_name eng f) (if List.isEmpty xs then "" else "("^(String.concat ", " (xs >>| value_to_string))^")")
                        (term_to_string sign t))
        let met inv_id =
            update_counters (function (m, v, u) -> (m + 1, v, u)) inv_id
            ""
        let possibly_violated inv_id conditions (updates : UPDATE_SET) t t' = 
            update_counters (function (m, v, u) -> (m, v, u + 1)) inv_id
            sprintf "\n!!! invariant '%s' possibly violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string eng t) (term_to_string eng t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates eng updates)
        let definitely_violated inv_id conditions updates t t' =
            update_counters (function (m, v, u) -> (m, v + 1, u)) inv_id
            sprintf "\n!!! invariant '%s' definitely violated in S_%d:\n%s\n\n- in this state and path, it symbolically evaluates to:\n%s\n\n%s\n\n%s\n\n---------------\n"
                inv_id i (term_to_string eng t) (term_to_string eng t')
                (initial_state_conditions_to_reach_this_state conditions)
                (show_cumulative_updates eng updates)
        let check_invariants invs S0 conditions updates =
            let check_one (inv_id, t) =
                let t' = s_eval_term t eng (apply_s_update_set eng S0 updates, Map.empty, Set.empty)
                if smt_formula_is_true eng t'
                then met inv_id
                else if smt_formula_is_false eng t' then definitely_violated inv_id conditions updates t t'
                else possibly_violated inv_id conditions updates t t'
            printf "%s" (String.concat "" (List.filter (fun s -> s <> "") (List.map check_one invs)))
        match get_rule' eng R with      // check invariants on all paths of state S' = S0 + R by traversing tree of R
        |   CondRule' (G, R1, R2) ->
                with_extended_path_cond G         (fun () eng (UM, env, pc) -> traverse i (G::conditions) R1 (UM, env, pc))             () (UM, env, pc)
                with_extended_path_cond (s_not G) (fun () eng (UM, env, pc) -> traverse i (s_not G::conditions) R2 (UM, env, pc)) () (UM, env, pc)
        |   S_Updates' updates    ->
                check_invariants invs UM0 conditions updates
        |   R -> failwith (sprintf "symbolic_execution_for_invariant_checking: there should be no such rule here: %s\n" (rule_to_string eng (make_rule eng R)))
    let state_header i = printf "\n=== state S_%d =====================================\n" i
    let rec F R_acc R_in i =
        reset_counters ()
        state_header i
        traverse i [] R_acc  (UM0, Map.empty, Set.empty)
        print_counters i ()
        if match opt_steps with Some n -> i < n | None -> true
        then let R_acc = s_eval_rule (SeqRule ([ R_acc; R_in; skipRule ])) eng (UM0, Map.empty, Set.empty)
             F R_acc R_in (i+1)
    F (S_Updates Set.empty) (SeqRule ([ R_in; skipRule ])) 0
    printf "\n=================================================\n"