module Parser

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let trace = ref 0

//--------------------------------------------------------------------

let pcharf c = pcharsat c ""

let one_line_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    (   R4  (pstring "//" |>> implode)
            (pmany (pcharf (fun c -> c <> '\r' && c <> '\n')) |>> implode)
            (pmany (pchar '\r') |>> implode)
            (pchar '\n' |>> fun c -> implode [c]) |>> fun (s1, s2, s3, s4) -> s1 + s2 + s3 + s4 ) s

// ML style multiline comments
let rec ML_multiline_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    let open_ = pstring "(*"
    let close_ = pstring "*)"
    let inside = pmany (    ( pcharf (fun c -> c <> '*' && c <> ')') |>> fun c -> [c])
                        <|> ((pchar '(') ++ pcharf (fun c -> c <> '*') |>> fun (c1,c2) -> [c1;c2])
                        <|> ((pchar '*') ++ pcharf (fun c -> c <> ')') |>> fun (c1,c2) -> [c1;c2])
                        <|> (fun input -> (ML_multiline_comment |>> explode) input) )  |>> List.concat
    in ( R3 open_ inside close_ |>> fun (s1, s2, s3) ->  (implode s1 + implode s2 + implode s3) ) s

let rec C_multiline_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    let open_ = pstring "/*"
    let close_ = pstring "*/"
    let inside = pmany (    ( pcharf (fun c -> c <> '*' && c <> '/') |>> fun c -> [c])
                        <|> ((pchar '/') ++ pcharf (fun c -> c <> '*') |>> fun (c1,c2) -> [c1;c2])
                        <|> ((pchar '*') ++ pcharf (fun c -> c <> '/') |>> fun (c1,c2) -> [c1;c2])
                        <|> (fun input -> (C_multiline_comment |>> explode) input) )  |>> List.concat
    in ( R3 open_ inside close_ |>> fun (s1, s2, s3) ->  (implode s1 + implode s2 + implode s3) ) s

let comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    (   ( one_line_comment <|> ML_multiline_comment <|> C_multiline_comment )
    |>> fun s' -> ( (if !trace > 0 then fprintf stderr "comment:\n%s\n" s' else ());
                    s' )   )    s

let ws_or_comment (s : ParserInput<'state>) : ParserResult<char list, 'state> =
    ( pwhitespace() << pmany (comment << pwhitespace()) |>> List.concat ) s

let skip_to_eos (s : ParserInput<'state>) : ParserResult<char list, 'state> =
    ( ws_or_comment >> peos ) s

let lit arg s = (ws_or_comment << pstring arg) s
let int s = (ws_or_comment << pint) s
    
let is_symb_ident_char c =
  match c with
    | '!' -> true | '%' -> true | '&' -> true | '$' -> true
    | '#' -> true | '+' -> true | '-' -> true | '/' -> true
    | ':' -> true | '<' -> true | '=' -> true | '>' -> true
    | '?' -> true | '@' -> true | '\\' -> true | '~' -> true
    | '`' -> true | '^' -> true | '|' -> true | '*' -> true
    | _ -> false

let symb_ident_char s = (pcharsat (fun c -> is_symb_ident_char c) "symbolic identifier character") s

//--------------------------------------------------------------------

/// Parse keywords
let kw kw_name s =
    (   (   (   (ws_or_comment << (pmany1 pletter)))
            <|> (ws_or_comment << (pmany1 symb_ident_char)) )
                    >>= fun s ->
                        let s = implode s
                        if s = kw_name
                        then preturn s
                        else pfail_msg "keyword" ($"keyword '{kw_name}' expected, '{s}' found") ) s

//--------------------------------------------------------------------

type PARSER_STATE = SIGNATURE * STATE

let get_signature (sign : SIGNATURE, state : STATE) = sign
let get_state (sign : SIGNATURE, state : STATE) = state

let get_signature_from_input (s : ParserInput<PARSER_STATE>) = get_parser_state s |> get_signature
let get_state_from_input (s : ParserInput<PARSER_STATE>)     = get_parser_state s |> get_state

//--------------------------------------------------------------------

let alphanumeric_identifier s =
    (   ws_or_comment << (pletter ++ (pmany palphanum_))
            |>> (fun (s, d) -> new System.String(s::d |> List.toArray)) ) s

let symbolic_identifier s =
    (   ws_or_comment << (pmany1 symb_ident_char)
            |>> (fun s -> new System.String(s |> List.toArray)) ) s

// non-infix function name
let fct_name (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    (   (alphanumeric_identifier <|> symbolic_identifier)
            >>= (fun s ->
                if is_function_name s sign && not (is_infix s sign)
                then preturn s
                else pfail_msg "fct_name" ($"function name expected, '{s}' found")) ) s

let variable s =
    let sign = get_signature_from_input s
    (   alphanumeric_identifier
            >>= (fun s ->
                if s = "true" || s = "false" || s = "undef" || is_function_name s sign
                then pfail_msg "variable" ($"variable expected, '{s}' found")
                else preturn s) ) s

// infix operator (function name)
let op_name s =
    let sign = get_signature_from_input s
    (   (alphanumeric_identifier <|> symbolic_identifier)
            >>= (fun s ->
                if is_function_name s sign && is_infix s sign
                then preturn s
                else pfail_msg "op_name" ($"infix operator expected, '{s}' found")) ) s

// 'new_fct_name' is for use in function definitions, differs from 'fct_name' in that it must be not be in the signature
// !!! add syntax for user-defined infix operators at some point
let new_fct_name s =
    let sign = get_signature_from_input s
    (   (alphanumeric_identifier)
            >>= (fun s -> if not (is_name_defined s sign) then preturn s else failwith ($"name '{s}' in function definition is already in use")) ) s

let new_rule_name s =
    let sign = get_signature_from_input s
    (   (alphanumeric_identifier)
            >>= (fun s -> if not (is_name_defined s sign) then preturn s else failwith ($"name '{s}' in rule definition is already in use")) ) s

let name s =
    (       ( kw "true"  |>> (fun _ -> BoolConst true) )
        <|> ( kw "false" |>> (fun _ -> BoolConst false) )
        <|> ( kw "undef" |>> (fun _ -> UndefConst) )
        <|> ( int        |>> (fun i -> IntConst i) )
        <|> ( fct_name   |>> (fun s -> FctName s) ) ) s
    // !!!! StringConst still missing

//--------------------------------------------------------------------

let typecheck_name name (sign : SIGNATURE, _ : Map<string, TYPE>) =
    match name with
    |   UndefConst      -> (UndefConst,    [([], Undef)])
    |   BoolConst b     -> (BoolConst b,   [([], Boolean)])
    |   IntConst i      -> (IntConst i,    [([], Integer)])
    |   StringConst s   -> (StringConst s, [([], String)])
    |   FctName f       -> (FctName f,     fct_types f sign)

let typecheck_app_term sign = function
    |   (fct_name, ts)  -> failwith ""

let rec typecheck_term (t : TERM) (sign : SIGNATURE, tyenv : Map<string, TYPE>) : TYPE =
    term_induction typecheck_name {
        Value    = fun x _ -> type_of_value x;
        AppTerm  = fun (f, ts) (sign, tyenv) ->
                        match f (sign, tyenv) with
                        |   (FctName f, f_sign_types) ->  // fprintf stderr "typecheck_term %A\n" (f, (ts >>| fun t -> t (sign, tyenv)))
                                                            match_fct_type f (ts >>| fun t -> t (sign, tyenv)) f_sign_types
                        |   (_, [(_, f_ran)]) -> f_ran    // special constants UndefConst, BoolConst b, etc.
                        |   _ -> failwith "typecheck_term: AppTerm: this should not happen";
        CondTerm = fun (G, t1, t2) (sign, tyenv) ->
                        if G (sign, tyenv) <> Boolean
                        then failwith "type of guard in conditional term must be Boolean)"
                        else
                        (   let (t1, t2) = (t1 (sign, tyenv), t2 (sign, tyenv))
                            if t1 = t2 then t1
                            else failwith $"branches of conditional term have different types (then-branch: {t1 |> type_to_string}; else-branch: {t2 |> type_to_string})" )                                                  
        Initial  = fun (f, xs) (sign, tyenv) ->
                        match_fct_type f (xs >>| type_of_value) (fct_types f sign)
        // VarTerm  = fun v -> fun (_, tyenv) -> try Map.find v tyenv with _ -> failwith $"variable '{v}' not defined";
        // LetTerm  = fun (x, t1, t2) -> fun (sign, tyenv) ->
        //                 let t1 = t1 (sign, tyenv)
        //                 t2 (sign, Map.add x t1 tyenv)
    } t (sign, tyenv)

let typecheck_rule (R : RULE) (sign : SIGNATURE, tyenv : Map<string, TYPE>) : TYPE =
    rule_induction typecheck_term {
        UpdateRule = fun ((f, ts), t) (sign, tyenv) ->
                        let kind = fct_kind f sign
                        if kind = Controlled || kind = Shared || kind = Out
                        then
                            let ts = ts >>| fun t -> t (sign, tyenv)
                            let t_type  = t (sign, tyenv)
                            let f_res_type = match_fct_type f ts (fct_types f sign)
                            if t_type <> f_res_type
                            then failwith (sprintf "type of right-hand side of update rule (%s) does not match type of function %s : %s -> %s"
                                                (t_type |> type_to_string) f (ts |> type_list_to_string) (f_res_type |> type_to_string))
                            else Rule
                        else
                            failwith (sprintf "error: function %s on the left-hand of update rule is of the wrong kind (it should be 'controlled', 'shared' or 'out')" f);
        CondRule   = fun (G, R1, R2) (sign, tyenv) -> 
                        if G (sign, tyenv) <> Boolean
                        then failwith "type of guard in conditional rule must be Boolean)"
                        else
                        (   let (R1, R2) = (R1 (sign, tyenv), R2 (sign, tyenv))
                            if R1 = R2 then Rule
                            else failwith "typecheck_rule: CondRule: this should not happen" );
        ParRule    = fun Rs (sign, tyenv) -> let _ = Rs >>| fun R -> R (sign, tyenv) in Rule;
        SeqRule    = fun Rs (sign, tyenv) -> let _ = Rs >>| fun R -> R (sign, tyenv) in Rule;
        IterRule   = fun R (sign, tyenv) -> let _ = R (sign, tyenv) in Rule;
        S_Updates  = fun _ -> failwith "not implemented"
    } R (sign, tyenv)

//--------------------------------------------------------------------

type 'a STACK_ELEM =
| Opnd of 'a                        (* operand  *)
| Optr of Signature.INFIX_STATUS * string      (* operator *)

/// Parses terms with infix operators, according to specified associativity and precedence
let rec operator_parser (elem : Parser<'elem, PARSER_STATE>, app_cons : NAME * 'elem list -> 'elem) (sign : SIGNATURE) (s : ParserInput<PARSER_STATE>) : ParserResult<'elem, PARSER_STATE> = 
    let reduce = function 
    |   [Opnd t] -> [Opnd t]
    |   (Opnd tR) :: (Optr (_, oper)) :: (Opnd tL) :: rest ->
            Opnd (app_cons (FctName oper, [ tL; tR ])) :: rest
    |   [] -> failwith "operator parsing: 'reduce' applied to empty stack)"
    |   (_ :: stack) -> failwith "operator parsing: badly formed stack"
    let rec extract = function
    |   [Opnd t] -> t
    |   stack -> extract (reduce stack)
    let rec F (stack : 'elem STACK_ELEM list) (s : ParserInput<PARSER_STATE>) : ParserResult<'elem, PARSER_STATE> = 
      ( match stack with
        |   [Opnd t1] ->
                ( ((op_name : Parser<string, PARSER_STATE>) ++ (elem : Parser<'elem, PARSER_STATE>)) 
                        >>= (fun (op, t2 : 'elem) -> F ([ Opnd t2; Optr (infix_status op sign, op); Opnd t1 ] : 'elem STACK_ELEM list)) )
                <|> (preturn (extract stack)) 
        |   ((Opnd t2) :: (Optr (Infix (assoc1, prec1), op1)) :: stack_rest) ->
                ( (((op_name : Parser<string, PARSER_STATE>) ++ (elem : Parser<'elem, PARSER_STATE>))
                        >>= (fun (op2, t3 : 'elem) ->
                            match infix_status op2 sign with
                            |   NonInfix -> failwith (sprintf "operator parsing: infix operator expected, '%s' " op2)
                            |   Infix (assoc2, prec2) -> 
                                    if (prec1 < prec2) || (prec1 = prec2 && assoc1 = RightAssoc && assoc2 = RightAssoc)
                                    then F ((Opnd t3)::(Optr (Infix (assoc2, prec2), op2))::stack)
                                    else if (prec1 > prec2) || (prec1 = prec2 && assoc1 = LeftAssoc && assoc2 = LeftAssoc)
                                    then F ((Opnd t3)::(Optr (Infix (assoc2, prec2), op2))::(reduce stack))
                                    else failwith (sprintf "operator parsing: infix operators '%s' and '%s' have the same precedence, but different associativity" op1 op2)))
                <|> (preturn (extract stack)) )
        | _ -> failwith "operator parsing: badly formed stack"  (* this should never happen *) ) s
    (elem >>= fun t1 -> F [ (Opnd t1) ]) s

//--------------------------------------------------------------------

let mkAppTerm sign = function
|   (FctName f, ts) -> AppTerm (FctName f, ts)
|   (UndefConst,    []) -> AppTerm (UndefConst, [])
|   (BoolConst b,   []) -> AppTerm (BoolConst b, [])
|   (IntConst i,    []) -> AppTerm (IntConst i, [])
|   (StringConst s, []) -> AppTerm (StringConst s, [])
|   (_, ts) -> failwith $"constant / 0-ary function applied to {List.length ts} arguments"

let rec simple_term (s : ParserInput<PARSER_STATE>) : ParserResult<TERM, PARSER_STATE> = 
    let sign = get_signature_from_input s
    let mkAppTerm_ = mkAppTerm sign
    (       (* ( (kw "let" >>. variable_) .>>. (kw "=" >>. term_) .>> kw "in" .>>. (term_ .>> kw "endlet") |>> fun ((x, t1), t2) -> LetTerm (x, t1, t2) )
        <|>*)
            ( R3 (kw "if" << term) (kw "then" << term) (poption (kw "else" << term)) >> kw "endif"
                |>> function  (G, r_then, opt_R_else) -> CondTerm (G, r_then, match opt_R_else with Some r_else -> r_else | None -> AppTerm (UndefConst, [])) )
        <|>
            ( R3 ( fct_name >> lit "(" )   term   (pmany (lit "," << term) >> lit ")")
                |>> fun (f, t, ts) -> mkAppTerm_ (FctName f, t :: ts) ) 
        <|> ( fct_name >> lit "(" >> lit ")" |>> fun f -> mkAppTerm_ (FctName f, []) )
        <|> ( name                           |>> fun nm -> mkAppTerm_ (nm, []) )  // 0-ary function names and special constants (int, string etc.)
      (*<|> ( variable_                         |>> fun s -> VarTerm s ) *)
        <|> ( lit "(" << term >> lit ")" )
    ) s

and term (s : ParserInput<PARSER_STATE>) : ParserResult<TERM, PARSER_STATE> = 
    let sign = get_signature_from_input s
    operator_parser (simple_term, mkAppTerm sign) sign s

//--------------------------------------------------------------------

let mkUpdateRule sign (t_lhs, t_rhs) =
    let err_msg tag = sprintf "update rule: %s term '%s' not allowed on left-hand side of update rule" tag (AST.term_to_string sign t_lhs)
    match t_lhs with
    |   AppTerm (FctName f, ts) ->
            let k = fct_kind f sign
            if k = Controlled || k = Out
            then UpdateRule ((f, ts), t_rhs)
            else failwith (sprintf "update rule: function to be updated must be of 'controlled' or 'out' kind (function '%s' found instead)" f)
    |   _ -> failwith (err_msg "'mkUpdateRule' is only defined for 'AppTerm's")
    // |   VarTerm _  -> failwith (err_msg "variable")
    // |   LetTerm _  -> failwith (err_msg "'let'-")

let rec rule (s : ParserInput<PARSER_STATE>) : ParserResult<RULE, PARSER_STATE> =
    let sign = get_signature_from_input s
    (       ( (R3 term (kw ":=") term) |>> fun (t1,_,t2) -> mkUpdateRule sign (t1, t2) )
        <|> ( kw "skip" |>> fun _ -> skipRule )
        <|> ( kw "par" << pmany1 rule >> kw "endpar" |>> fun Rs -> ParRule Rs)
        <|> ( ((lit "{" << rule) ++ pmany (lit "," << rule)) >> (lit "}") |>> fun (R1, Rs) -> ParRule (R1::Rs) )
        <|> ( kw "seq" << pmany1 rule >> kw "endseq" |>> fun Rs -> SeqRule Rs)
        <|> ( ((lit "[" << rule) ++ pmany (lit ";" << rule)) >> (lit "]") |>> fun (R1, Rs) -> SeqRule (R1::Rs) )
        <|> ( (R3 (kw "if" << term) (kw "then" << rule) (poption (kw "else" << rule)) >> kw "endif")
                |>> function  (G, r_then, opt_R_else) -> CondRule (G, r_then, match opt_R_else with Some r_else -> r_else | None -> skipRule) )
        <|> ( kw "iterate" << rule >> poption (kw "enditerate") |>> fun R -> IterRule R )
        <|> ( (kw "while" << lit "(" << term >> lit ")") ++ rule >> poption (kw "endwhile") |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule)) )
    ) s

//--------------------------------------------------------------------

let type_ (s : ParserInput<PARSER_STATE>) : ParserResult<TYPE, PARSER_STATE> =
    let sign = get_signature_from_input s
    (       (*( kw "Any"     |>> fun _ -> Any )
        <|>*) ( kw "Undef"   |>> fun _ -> Undef)
        <|> ( kw "Boolean" |>> fun _ -> Boolean)
        <|> ( kw "Integer" |>> fun _ -> Integer)
        <|> ( kw "String " |>> fun _ -> String) ) s

let fct_parameter_types (s : ParserInput<PARSER_STATE>) : ParserResult<TYPE list * TYPE, PARSER_STATE> =
    (       ( R3 (poption (kw ":") << lit "(" << type_) (pmany (lit "," << type_)) (lit ")" << kw "->" << type_)
                |>> fun (ty1, tys, ty_dom) -> (ty1 :: tys, ty_dom) )
        <|> ( R3 (kw ":" << type_) (pmany (lit "," << type_)) (kw "->" << type_)
                |>> fun (ty1, tys, ty_dom) -> (ty1 :: tys, ty_dom) )
        <|> ( ( kw ":" << type_ ++ (kw "->" << type_) )
                |>> fun (ty1, ty_dom) -> ([ty1], ty_dom) )
        <|> ( ( ((kw ":" <|> kw "->") << type_) )
                |>> fun ty_dom -> ([], ty_dom) )
    ) s

let fct_initially (s : ParserInput<PARSER_STATE>) : ParserResult<Map<VALUE list, VALUE>, PARSER_STATE> =
    let (sign, state) = get_parser_state s
    // for the time being, only 0-ary functions can be initialised
    (       ( ((kw "initially") << term)
                |>> fun t -> let _ = typecheck_term t (sign, Map.empty)
                             Map.add [] (Eval.eval_term t (state, Map.empty)) Map.empty )
    ) s

let fct_eqdef (s : ParserInput<PARSER_STATE>) : ParserResult<VALUE list -> VALUE, PARSER_STATE> =
    let sign = get_signature_from_input s
    // for the time being, only 0-ary functions can be initialised
    (       ( ((kw "=") << term)
                |>> fun t -> let _ = typecheck_term t (sign, Map.empty)
                             let t_val = Eval.eval_term t (State.background_state  (* !!! use only background !!! *), Map.empty)
                             (function [] -> t_val | _ -> UNDEF) )
    ) s

let definition (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE * STATE * RULES_DB, PARSER_STATE> =
    let (sign, state) = get_parser_state s
    let opt_state_initialisation (kind : Signature.FCT_KIND) f (tys_ran, ty_dom) (opt_static_def, opt_initially) = 
            match (opt_static_def, opt_initially) with
                |   (Some static_def, _) ->
                        state_override_static empty_state (Map.add f static_def Map.empty)
                |   (_, Some initial_values) ->
                        let _ = Map.map (fun xs y -> 
                                    if (xs >>| type_of_value, type_of_value y) <> (tys_ran, ty_dom)
                                    then failwith (sprintf "type mismatch in initialisation of function '%s'" f)
                                    else ()) initial_values
                        state_override_dynamic empty_state (Map.add f initial_values Map.empty)
                |   _ -> empty_state
    ( ( (   ( ((kw "static" >> poption (kw "function")) << new_fct_name ++ fct_parameter_types) ++ (poption fct_eqdef) )
                |>> fun ((f, (tys_ran, ty_dom)), opt_fct_def) ->
                        (   add_function_name f (Static, NonInfix, (tys_ran, ty_dom)) Map.empty,
                            opt_state_initialisation (Signature.Static) f (tys_ran, ty_dom) (opt_fct_def, None),
                            empty_rules_db ) )
        <|> (   ( ((kw "controlled" <|> kw "function" <|> (kw "controlled" >> kw "function")) << new_fct_name ++ fct_parameter_types) ++ (poption fct_initially) )
                |>> fun ((f, (tys_ran, ty_dom)), opt_initially) ->
                        (   add_function_name f (Controlled, NonInfix, (tys_ran, ty_dom)) Map.empty,
                            opt_state_initialisation (Signature.Controlled) f (tys_ran, ty_dom) (None, opt_initially),
                            empty_rules_db ) )
        <|> ( ((kw "rule" << new_rule_name) ++ (kw "=" << rule))
                |>> fun (rule_name, R) ->
                        let _ = typecheck_rule R (sign, Map.empty)
                        (   add_rule_name rule_name [] Signature.empty_signature,
                            empty_state,
                            add_rule rule_name R empty_rules_db ) )   // parameterless rule: empty type list
        (*<|> ( ws_or_comment >> peos |>> fun _ -> (empty_signature, empty_state, empty_rules_db) ) *)
    ) ||>> fun (sign, state) (sign', state', _) -> (signature_override sign sign', state_override state state' ) ) s

let rec definitions (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE * STATE * RULES_DB, PARSER_STATE>  =
    (   ( definition >> skip_to_eos )
    <|> ( definition ++ definitions
            |>> fun ((sign', state', rules_db'), (sign'', state'', rules_db'')) -> 
                    (signature_override sign' sign'', state_override state' state'', rules_db_override rules_db' rules_db'') )   // !!! inefficient, should be changed
    ) s

//--------------------------------------------------------------------

let make_parser parse_fct parser_state s =
    match (parse_fct >> ws_or_comment) (parser_input_in_state_from_string parser_state s) with
    |   ParserSuccess (result, parser_state) -> (result, parser_state)
    |   ParserFailure errors -> failwith (parser_msg (ParserFailure errors))

//--------------------------------------------------------------------
// parser "API"

let parse_and_typecheck (parsing_fct : Parser<'a, PARSER_STATE>) typechecking_fct parser_state (s : string) =
    let sign = get_signature parser_state
    let (ast, parser_state') = make_parser parsing_fct parser_state s
    let _   = typechecking_fct ast (sign, Map.empty)   // function result is discarded, but exceptions are thrown on typing errors
    ast

let parse_name sign s = parse_and_typecheck (name : Parser<NAME, PARSER_STATE>) typecheck_name (sign, empty_state) s
let parse_term sign s = parse_and_typecheck term typecheck_term (sign, empty_state) s
let parse_rule sign s = parse_and_typecheck rule typecheck_rule (sign, empty_state) s
//let parse_definitions (sign, S) s = get_state_from_input (snd (make_parser definitions (sign, S) s))
let parse_definitions (sign, S) s =
    let defs = fst (make_parser definitions (sign, S) s)
    fprintf stderr "parse_definitions: %A\n" defs
    defs
