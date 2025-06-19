module DAG

//--------------------------------------------------------------------

open System.Collections.Generic

open Common
open PrettyPrinting
open Background
//open Signature
// open AST
open SmtInterface

let trace = ref 0

//--------------------------------------------------------------------

type GLOBAL_CTX' = {
    signature    : Signature.SIGNATURE
    fwdTermTable : Dictionary<TERM', TERM>
    bwdTermTable : Dictionary<TERM, TERM'>
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

type TERM_ATTRS = {   
    term_id   : int
    term_type : Signature.TYPE
}

let global_ctxs : GLOBAL_CTX_TABLE = {
    ctx_table = new Dictionary<int, GLOBAL_CTX'>()
    next_ctx  = ref 0
}


let make_term (GlobalCtx gctx_id) (t' : TERM') : TERM =
    let ctx = global_ctxs.ctx_table.[gctx_id]
    if ctx.fwdTermTable.ContainsKey t' then
        ctx.fwdTermTable.[t']
    else
        let term_id = ctx.fwdTermTable.Count
        ctx.fwdTermTable.[t'] <- Term term_id
        ctx.bwdTermTable.[Term term_id] <- t'
        Term term_id

let get_term' (gctx: GLOBAL_CTX) (Term term_id) =
    let (GlobalCtx gctx_id) = gctx
    let ctx = global_ctxs.ctx_table.[gctx_id]
    if ctx.bwdTermTable.ContainsKey (Term term_id) then
        ctx.bwdTermTable.[Term term_id]
    else
        failwith (sprintf "get_term': term %d not found in context %d" term_id gctx_id)

let Value gctx x = make_term gctx (Value' x)

let Initial gctx (f, xs) = make_term gctx (Initial' (f, xs))

let AppTerm gctx (f, ts) = make_term gctx (AppTerm' (f, ts))

let CondTerm gctx (G, t1, t2) = make_term gctx (CondTerm' (G, t1, t2))

let VarTerm gctx v = make_term gctx (VarTerm' v)

let QuantTerm gctx (q_kind, v, t_set, t_cond) = make_term gctx (QuantTerm' (q_kind, v, t_set, t_cond))

let LetTerm gctx (x, t1, t2) = make_term gctx (LetTerm' (x, t1, t2))

let DomainTerm gctx tyname = make_term gctx (DomainTerm' tyname)    

//--------------------------------------------------------------------

let new_global_ctx (sign : Signature.SIGNATURE) =
    let ctx_id = !global_ctxs.next_ctx
    global_ctxs.next_ctx := ctx_id + 1
    let new_ctx = {
        signature    = sign
        fwdTermTable = new Dictionary<TERM', TERM>(HashIdentity.Structural)
        bwdTermTable = new Dictionary<TERM, TERM'>(HashIdentity.Structural)
    }
    global_ctxs.ctx_table.[ctx_id] <- new_ctx
    GlobalCtx ctx_id

let get_global_ctx' (GlobalCtx gctx_id) =
    if global_ctxs.ctx_table.ContainsKey gctx_id then
        global_ctxs.ctx_table.[gctx_id]
    else
        failwith (sprintf "get_global_ctx': context %d not found" gctx_id)

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
