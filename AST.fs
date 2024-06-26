module AST

open Common
open Background
open Signature
open PrettyPrinting

//--------------------------------------------------------------------

type TERM =
| Value of VALUE                     // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
| Initial of FCT_NAME * VALUE list   // used for special purposes (symbolic evaluation): "partially interpreted term", not an actual term of the language
| AppTerm of NAME * TERM list
| CondTerm of TERM * TERM * TERM
//  | VarTerm of string
//  | LetTerm of string * TERM * TERM
//  | TupleTerm of TERM list

type RULE =
| S_Updates of Set<(FCT_NAME * VALUE list) * TERM>  //Map<FCT_NAME * VALUE list, TERM>   // used for special purposes (symbolic evaluation): "partially interpreted rules", not actual rules of the language
| UpdateRule of (FCT_NAME * TERM list) * TERM
| CondRule of TERM * RULE * RULE
| ParRule of RULE list
| SeqRule of RULE list
| IterRule of RULE

let skipRule = ParRule []

//--------------------------------------------------------------------

type RULES_DB = Map<RULE_NAME, RULE>
let empty_rules_db = Map.empty
let rules_db_override db1 db' = Common.map_override db1 db'
let add_rule R db = Map.add R db
let exists_rule rule_name db = Map.containsKey rule_name db
let get_rule rule_name db = Map.find rule_name db

//--------------------------------------------------------------------

let int_term n = AppTerm (IntConst n, [])
let str_term s = AppTerm (StringConst s, [])

//--------------------------------------------------------------------

type TERM_INDUCTION<'name, 'term> = {
    Value    : VALUE -> 'term;
    Initial  : string * VALUE list -> 'term;
    AppTerm  : 'name * 'term list -> 'term;
    CondTerm : 'term * 'term * 'term -> 'term;
    //  VarTerm  : string -> 'term;
    //  LetTerm  : string * 'term * 'term -> 'term
}

let rec term_induction (name : NAME -> 'name) (F : TERM_INDUCTION<'name, 'term>) (t : TERM) :'term =
    let term_ind = term_induction name
    match t with
    |   Value x -> F.Value x
    |   Initial (f, xs) -> F.Initial (f, xs);
    |   AppTerm (f, ts) -> F.AppTerm (name f, List.map (fun t -> term_ind F t) ts)
    |   CondTerm (G, t1, t2) -> F.CondTerm (term_ind F G, term_ind F t1, term_ind F t2)
    //  |   VarTerm v -> (((F.VarTerm :string -> 'term) (v : string)) :'term)
    //  |   LetTerm (x, t1, t2) -> F.LetTerm (x, term_ind F t1, term_ind F t2)

//--------------------------------------------------------------------

type RULE_INDUCTION<'term, 'rule> = {
    UpdateRule : (FCT_NAME * 'term list) * 'term -> 'rule;
    CondRule : 'term * 'rule * 'rule -> 'rule;
    ParRule : 'rule list -> 'rule;
    SeqRule : 'rule list -> 'rule;
    IterRule : 'rule -> 'rule;
    S_Updates : Set<(FCT_NAME * VALUE list) * TERM> -> 'rule;    // Map<FCT_NAME * VALUE list, 'term> -> 'rule;
}

let rec rule_induction (term : TERM -> 'term) (F : RULE_INDUCTION<'term, 'rule>) (R : RULE) : 'rule =
    let rule_ind = rule_induction term
    match R with
    |   UpdateRule ((f: FCT_NAME, ts), t) -> F.UpdateRule ((f, List.map term ts), term t)
    |   CondRule (G, R1, R2: RULE) -> F.CondRule (term G, rule_ind F R1, rule_ind F R2)
    |   ParRule Rs -> F.ParRule (List.map (rule_ind F) Rs)
    |   SeqRule Rs -> F.SeqRule (List.map (rule_ind F) Rs)
    |   IterRule R -> F.IterRule (rule_ind F R)
    |   S_Updates U -> F.S_Updates U   // F.S_Updates (Map.map (fun loc -> fun t_rhs -> term t_rhs) U)

//--------------------------------------------------------------------
//
//  example of AST induction: size
//
//--------------------------------------------------------------------

let name_size name = 1

let rec term_size t =
    term_induction name_size {
        Value = fun _ -> 1;
        AppTerm = fun (f, ts : int list) -> 1 + f + List.sum ts;
        CondTerm = fun (G, t1, t2) -> 1 + G + t1 + t2;
        Initial = fun _ -> 1;
        //  VarTerm = fun _ -> 1;
        //  LetTerm = fun (x, t1, t2) -> 1 + t1 + t2;
    } t

let rule_size = rule_induction term_size {
    UpdateRule = fun ((f, ts), t) -> 1 + 1 + List.sum ts + t;
    CondRule = fun (G, R1, R2) -> 1 + G + R1 + R2;
    ParRule = fun Rs -> 1 + List.sum Rs;
    SeqRule = fun Rs -> 1 + List.sum Rs;
    IterRule = fun R' -> 1 + R';
    S_Updates = fun U -> Set.count U;   // not relevant, but define somehow to allow printing for debugging
}

//--------------------------------------------------------------------
//
//  lift conditional
//
//--------------------------------------------------------------------

let lift_cond_term t = 
    let rec F_app = function
        |   (f, ts, []) -> AppTerm (f, List.rev ts)
        |   (f, ts, CondTerm (G, t1, t2) :: ts') ->
                let (G, t1, t2) = (lift G, lift t1, lift t2)
                lift (CondTerm (G, F_app (f, t1 :: ts, ts'), F_app (f, t2 :: ts, ts')))
        |   (f, ts, t' :: ts') -> F_app (f, t' :: ts, ts')
    and F_cond = function
    |   CondTerm (CondTerm (phi, phi1, phi2), t1, t2) ->
            let (phi, phi1, phi2, t1, t2) = (lift phi, lift phi2, lift phi2, lift t1, lift t2)
            lift (CondTerm (phi, CondTerm (phi1, t1, t2), CondTerm (phi2, t1, t2)))
    |   t -> t
    and lift t =
        match t with
        |   AppTerm (f, ts) -> F_app (f, [], List.map lift ts)
        |   CondTerm (phi, t1, t2) -> F_cond (CondTerm (lift phi, lift t1, lift t2))
        |   _ -> t
    lift t

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

let rec pp_term (sign : SIGNATURE) (t : TERM) =
    let (pp_app_term, pp_location_term) = (pp_app_term sign, pp_location_term sign)
    term_induction (fun x -> x) {
        AppTerm  = fun (f, ts) -> pp_app_term (f, ts);
        CondTerm = fun (G, t1, t2) -> blo0 [ str "if "; G; line_brk; str "then "; t1; line_brk; str "else "; t2; line_brk; str "endif" ];
        Value    = fun x -> str (value_to_string x);
        Initial  = fun (f, xs) -> pp_location_term "initial" (f, xs);
        //  VarTerm = fun x -> str x;
        //  LetTerm = fun (v, t1, t2) -> blo0 [ str "let "; str v; str " = "; t1; line_brk; str "in "; t2; line_brk; str "endlet" ];
    } t

let rec pp_rule (sign : SIGNATURE) (R : RULE) =
    let (pp_app_term, pp_term) = (pp_app_term sign, pp_term sign)
    rule_induction pp_term {
        UpdateRule = fun ((f, ts), t) -> blo0 [ pp_app_term (FctName f, ts); str " := "; t ];
        CondRule = fun (G, R1, R2) -> blo0 ( str "if " :: G:: str " then " :: line_brk :: blo2 [ R1 ] :: line_brk ::
                                             (if R2 <> str "skip" then [ str "else "; line_brk; blo2 [ R2 ]; line_brk; str "endif" ] else [ str "endif"]) );
        ParRule = fun Rs -> if Rs <> [] then blo0 [ str "par"; line_brk; blo2 ( pp_list [line_brk] Rs); line_brk; str "endpar" ] else str "skip";
        SeqRule = fun Rs -> blo0 [ str "seq"; line_brk; blo2 (pp_list [line_brk] Rs); line_brk; str "endseq" ];
        IterRule = fun R' -> blo0 [ str "iterate "; line_brk; blo2 [ R' ]; line_brk; str "enditerate" ];
        S_Updates = fun U ->
                        let pp_elem ((f, xs), t) = blo0 [ str f; str " "; str "("; blo0 (pp_list [str",";brk 1] (xs >>| fun x -> str (value_to_string x))); str ") := "; (pp_term t) ]
                        let L = Set.toList U >>| pp_elem
                        blo0 [ str "{"; line_brk; blo2 ( pp_list [line_brk] L); line_brk; str "}" ];
    } R

let term_to_string sign t    = t |> pp_term sign |> PrettyPrinting.toString 80
let rule_to_string sign t    = t |> pp_rule sign |> PrettyPrinting.toString 80
