module AST

open Common
open Background
open Signature
open PrettyPrinting

//--------------------------------------------------------------------

type QUANT_KIND =
|   Forall
|   ExistUnique
|   Exist

type 'annotation ANN_TERM =
|   Value'      of 'annotation * (VALUE)                     // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   Initial'    of 'annotation * (FCT_NAME * VALUE list)   // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
|   AppTerm'    of 'annotation * (NAME * 'annotation ANN_TERM list)
|   CondTerm'   of 'annotation * ('annotation ANN_TERM * 'annotation ANN_TERM * 'annotation ANN_TERM)
|   VarTerm'    of 'annotation * (string)
|   QuantTerm'  of 'annotation * (QUANT_KIND * string * 'annotation ANN_TERM * 'annotation ANN_TERM)
|   LetTerm'    of 'annotation * (string * 'annotation ANN_TERM * 'annotation ANN_TERM)
|   DomainTerm' of 'annotation * TYPE                  // AsmetaL construct: finite type (e.g. enum, abstract, subsetof) used as finite set
//  | TupleTerm   of 'annotation * ('annotation ANN_TERM list)

let get_annotation = function
|   Value' (ann, _) -> ann
|   Initial' (ann, _) -> ann
|   AppTerm' (ann, _) -> ann
|   CondTerm' (ann, _) -> ann
|   VarTerm' (ann, _) -> ann
|   QuantTerm' (ann, _) -> ann
|   LetTerm' (ann, _) -> ann
|   DomainTerm' (ann, _) -> ann
//  |   TupleTerm (ann, _) -> ann

type TYPED_TERM = TYPE ANN_TERM
let get_type : TYPED_TERM -> TYPE = get_annotation

let mkValue sign x = Value' (type_of_value sign x, x)
let mkInitial sign (f, xs) = Initial' (match_fct_type f (xs >>| type_of_value sign) (fct_types f sign), (f, xs))    // !!!!!! very inefficient

//--------------------------------------------------------------------

type RULE =
| S_Updates of Set<(FCT_NAME * VALUE list) * TYPED_TERM>  //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
| UpdateRule of (FCT_NAME * TYPED_TERM list) * TYPED_TERM
| CondRule of TYPED_TERM * RULE * RULE
| ParRule of RULE list
| SeqRule of RULE list
| IterRule of RULE
| LetRule of string * TYPED_TERM * RULE
| ForallRule of string * TYPED_TERM * TYPED_TERM * RULE
| MacroRuleCall of RULE_NAME * TYPED_TERM list

let skipRule = ParRule []

//--------------------------------------------------------------------

type RULES_DB = Map<RULE_NAME, string list * RULE>   // !!! what about types ?

let empty_rules_db : RULES_DB = Map.empty
let rules_db_override (db1 : RULES_DB) (db' : RULES_DB) = Common.map_override db1 db'
let add_rule rule_name ((args, R) : string list * RULE) (db : RULES_DB) = Map.add rule_name (args, R) db
let exists_rule rule_name (db : RULES_DB) = Map.containsKey rule_name db
let get_rule rule_name (db : RULES_DB) = Map.find rule_name db

//--------------------------------------------------------------------

type MACRO_DB = Map<FCT_NAME, string list * TYPED_TERM>   // for derived functions = macros !!! what about types ?

let empty_macro_db : MACRO_DB = Map.empty
let macro_db_override (db1 : MACRO_DB) (db' : MACRO_DB) : MACRO_DB = Common.map_override db1 db'
let add_macro macro_name ((args, t) : string list * TYPED_TERM) (db : MACRO_DB) = Map.add macro_name (args, t) db
let exists_macro macro_name (db : MACRO_DB) = Map.containsKey macro_name db
let get_macro macro_name (db : MACRO_DB) = Map.find macro_name db

//--------------------------------------------------------------------

let int_term n = AppTerm' (Integer, (IntConst n, []))
let str_term s = AppTerm' (Strg, (StringConst s, []))

//--------------------------------------------------------------------

type FUNC_EXPR =
| LambdaTerm of string list * TYPED_TERM

//--------------------------------------------------------------------

type ANN_TERM_INDUCTION<'annotation, 'name, 'term> = {
    Value      : 'annotation * (VALUE) -> 'term;
    Initial    : 'annotation * (string * VALUE list) -> 'term;
    AppTerm    : 'annotation * ('name * 'term list) -> 'term;
    CondTerm   : 'annotation * ('term * 'term * 'term) -> 'term;
    VarTerm    : 'annotation * (string) -> 'term;
    QuantTerm  : 'annotation * (QUANT_KIND * string * 'term * 'term) -> 'term;
    LetTerm    : 'annotation * (string * 'term * 'term) -> 'term;
    DomainTerm : 'annotation * (TYPE) -> 'term;
}

let rec ann_term_induction (name : NAME -> 'name) (F : ANN_TERM_INDUCTION<'annotation, 'name, 'term>) (t : 'annotation ANN_TERM) :'term =
    let term_ind = ann_term_induction name
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

type RULE_INDUCTION<'term, 'rule> = {
    S_Updates : Set<(FCT_NAME * VALUE list) * TYPED_TERM> -> 'rule;     // what not ""... * 'term>" ?
    UpdateRule : (FCT_NAME * 'term list) * 'term -> 'rule;
    CondRule : 'term * 'rule * 'rule -> 'rule;
    ParRule : 'rule list -> 'rule;
    SeqRule : 'rule list -> 'rule;
    IterRule : 'rule -> 'rule;
    LetRule : string * 'term * 'rule -> 'rule;
    ForallRule : string * 'term * 'term * 'rule -> 'rule;
    MacroRuleCall : RULE_NAME * 'term list -> 'rule;     // Map<FCT_NAME * VALUE list, 'term> -> 'rule;
}

let rec rule_induction (term : TYPED_TERM -> 'term) (F : RULE_INDUCTION<'term, 'rule>) (R : RULE) : 'rule =
    let rule_ind = rule_induction term
    match R with
    |   S_Updates U -> F.S_Updates U   // F.S_Updates (Map.map (fun loc -> fun t_rhs -> term t_rhs) U)
    |   UpdateRule ((f: FCT_NAME, ts), t) -> F.UpdateRule ((f, List.map term ts), term t)
    |   CondRule (G, R1, R2: RULE) -> F.CondRule (term G, rule_ind F R1, rule_ind F R2)
    |   ParRule Rs -> F.ParRule (List.map (rule_ind F) Rs)
    |   SeqRule Rs -> F.SeqRule (List.map (rule_ind F) Rs)
    |   IterRule R -> F.IterRule (rule_ind F R)
    |   LetRule (v, t, R) -> F.LetRule (v, term t, (rule_ind F) R)
    |   ForallRule (v, t_set, t_filter, R) -> F.ForallRule (v, term t_set, term t_filter, (rule_ind F) R)
    |   MacroRuleCall (r, ts) -> F.MacroRuleCall (r, List.map term ts)

//--------------------------------------------------------------------
//
//  example of AST induction: size
//
//--------------------------------------------------------------------

let name_size name = 1

let rec term_size t =
    ann_term_induction name_size {
        Value = fun (_, _) -> 1;
        AppTerm = fun (_, (f, ts : int list)) -> 1 + f + List.sum ts;
        CondTerm = fun (_, (G, t1, t2)) -> 1 + G + t1 + t2;
        Initial = fun (_, _) -> 1;
        VarTerm = fun (_, _) -> 1;
        QuantTerm = fun (_, (q_kind, v, t_set, t_cond)) -> 1 + t_set + t_cond;
        LetTerm = fun (_, (v, t1, t2)) -> 1 + t1 + t2;
        DomainTerm = fun (_, _) -> 1;
    } t

let rule_size = rule_induction term_size {
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
//
//  pretty printing
//
//--------------------------------------------------------------------

let rec pp_list sep = function
|   []         -> []
|   [x]        -> [ x ]
|   (x :: xs') -> x :: (sep @ (pp_list sep xs'))

let pp_name (name : NAME) =
    (   match name with
    |   UndefConst -> "undef"
    |   BoolConst b -> if b then "true" else "false"
    |   IntConst i -> i.ToString()
    |   StringConst s -> "\"" + s + "\""
    |   FctName f -> f ) |> str

let pp_app_term sign = function
    |   (FctName f, [t1; t2]) when infix_status f sign <> NonInfix ->
            blo0 [ str "("; blo0 [ t1; brk 1; str (sprintf "%s " f); t2 ]; str ")" ]
    |   (FctName f, ts) when ts <> [] ->
            blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] ts); str ")" ]
    |   (name, _) -> pp_name name

let pp_location_term sign prefix = function
    |   (f : string, xs : VALUE list) when xs <> [] ->
            blo0 [ str (prefix+"["); str f; str ", "; str "("; blo0 (pp_list [str",";brk 1] (List.map (fun x -> str (value_to_string x)) xs)); str ")]" ]
    |   (f, _) -> blo0 [ str $"{prefix}[{f}]" ]

let rec pp_term (sign : SIGNATURE) (t : TYPED_TERM) =
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    ann_term_induction (fun x -> x) {
        AppTerm  = fun (_, (f, ts)) -> pp_app_term (f, ts);
        CondTerm = fun (_, (G, t1, t2)) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun (_, x) -> str (value_to_string x);
        Initial  = fun (_, (f, xs)) -> pp_location_term "initial" (f, xs);
        VarTerm = fun (_, x) -> str x;
        QuantTerm = fun (_, (q_kind, v, t_set, t_cond)) ->
            let q_kind = match q_kind with Forall -> "(forall " | ExistUnique -> "(exist unique " | Exist -> "(exist "
            blo0 [ str q_kind; str v; str " in "; t_set; str " with "; t_cond; str ")" ];
        LetTerm = fun (_, (v, t1, t2)) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
        DomainTerm = fun (_, tyname) -> str (type_to_string tyname);
    } t

let rec pp_rule (sign : SIGNATURE) (R : RULE) =
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
