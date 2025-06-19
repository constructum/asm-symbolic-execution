module DAG

//--------------------------------------------------------------------

open Common
open PrettyPrinting
open Background
//open Signature
// open AST
open SmtInterface

let trace = ref 0

//--------------------------------------------------------------------
(*
type GLOBAL_CTX = GlobalCtx of {
    signature : Signature.SIGNATURE;
    initial_state : State.STATE;
    rules : AST.RULES_DB;
    macros : AST.MACRO_DB;
    invariants : Map<string, AST.TYPED_TERM>;
    initially : Set<AST.TYPED_TERM>;
    smt_ctx : SMT_CONTEXT;
}
*)
//--------------------------------------------------------------------

type TERM' =
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

let rec term_induction (name : Signature.NAME -> 'name) (F : TERM_INDUCTION<'name, 'term>) (t : TERM) :'term =
    let term_ind = term_induction name
    match t with
    |   Value' (ann, x)              -> F.Value   (ann, x)
    |   Initial' (ann, (f, xs))      -> F.Initial (ann, (f, xs))
    |   AppTerm'  (ann, (f, ts))     -> F.AppTerm (ann, (name f, List.map (fun t -> term_ind F t) ts))
    |   CondTerm' (ann, (G, t1, t2)) -> F.CondTerm (ann, (term_ind F G, term_ind F t1, term_ind F t2))
    |   VarTerm' (ann, v)            -> F.VarTerm (ann, v)
    |   QuantTerm' (ann, (q_kind, v, t_set, t_cond)) -> F.QuantTerm (ann, (q_kind, v, term_ind F t_set, term_ind F t_cond))
    |   LetTerm' (ann, (x, t1, t2))  -> F.LetTerm (ann, (x, term_ind F t1, term_ind F t2))
    |   DomainTerm' (ann, tyname)    -> F.DomainTerm (ann, tyname)


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

let rec pp_term (sign : Signature.SIGNATURE) (t : TERM) =
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    ann_term_induction (fun x -> x) {
        AppTerm  = fun (_, (f, ts)) -> pp_app_term (f, ts);
        CondTerm = fun (_, (G, t1, t2)) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun (_, x) -> str (value_to_string x);
        Initial  = fun (_, (f, xs)) -> pp_location_term "initial" (f, xs);
        VarTerm = fun (_, x) -> str x;
        QuantTerm = fun (_, (q_kind, v, t_set, t_cond)) ->
            blo0 [ str ("("^(quant_kind_to_str q_kind)^" "); str v; str " in "; t_set; str " with "; t_cond; str ")" ];
        LetTerm = fun (_, (v, t1, t2)) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
        DomainTerm = fun (_, tyname) -> str (type_to_string tyname);
    } t

let rec pp_rule (sign : Signature.SIGNATURE) (R : RULE) =
    let (pp_app_term, pp_term) = (pp_app_term sign, pp_term sign)
    rule_induction pp_term {
        S_Updates = fun U ->
                        let pp_elem ((f, xs), t) = blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] (xs >>| fun x -> str (value_to_string x))); str ") := "; (pp_term t) ]
                        let L = Set.toList U >>| pp_elem
                        blo0 [ str "{"; line_brk; blo2 ( pp_list [line_brk] L); line_brk; str "}" ];
        UpdateRule = fun ((f, ts), t) -> blo0 [ pp_app_term (FctName f, ts); str " := "; t ];
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
