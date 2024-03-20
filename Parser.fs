module Parser

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let pcharf c = pcharsat c ""

let one_line_comment :Parser<char list> =
    (pchar '/' << pchar '/' << pmany (pcharf (fun c -> c <> '\r' && c <> '\n')) << pmany (pchar '\r') << pchar '\n' |>> fun _ -> [])

let rec multiline_comment s : ParserResult<char list> =
    let open_ = pstring "(*"
    let rest_ = pmany ( pmany (pcharf (fun c -> c <> '*'))
                       ++ ( pmany1 ( ( pchar '*' << pcharf (fun c -> c <> ')') )
                                <|>   pchar '*') ) ) ++ (pchar ')') |>> fun _ -> []
    in ( open_ << rest_ ) s

let comment =
    one_line_comment <|> multiline_comment

let ws_or_comment =
    pwhitespace << pmany (comment << pwhitespace) |>> List.concat             // for the moment only one-line comments are implemented

let skip_to_eos = ws_or_comment >> peos
let lit arg = ws_or_comment << pstring arg
let int = ws_or_comment << pint
    
let is_symb_ident_char c =
  match c with
    | '!' -> true | '%' -> true | '&' -> true | '$' -> true
    | '#' -> true | '+' -> true | '-' -> true | '/' -> true
    | ':' -> true | '<' -> true | '=' -> true | '>' -> true
    | '?' -> true | '@' -> true | '\\' -> true | '~' -> true
    | '`' -> true | '^' -> true | '|' -> true | '*' -> true
    | _ -> false

let symb_ident_char = (pcharsat (fun c -> is_symb_ident_char c) "symbolic identifier character")

//--------------------------------------------------------------------

/// Parse keywords
let kw kw_name =
    (   (ws_or_comment << (pmany1 pletter))
    <|> (ws_or_comment << (pmany1 symb_ident_char)) ) >>= fun s -> if s = explode kw_name then preturn s else pfail

//--------------------------------------------------------------------

let alphanumeric_identifier =
    ws_or_comment << (pletter ++ (pmany palphanum_))
        |>> (fun (s, d) -> new System.String(s::d |> List.toArray))

let symbolic_identifier =
    ws_or_comment << (pmany1 symb_ident_char)
        |>> (fun s -> new System.String(s |> List.toArray))

// non-infix function name
let fct_name (sign : SIGNATURE) =
    (alphanumeric_identifier <|> symbolic_identifier)
        >>= (fun s -> if is_function_name s sign && not (is_infix s sign) then preturn s else pfail)

let variable (sign : SIGNATURE) =
    alphanumeric_identifier
        >>= (fun s ->
                if s = "true" || s = "false" || s = "undef" || is_function_name s sign
                then failwith (sprintf "'%s' is not a variable (instead, it is a constant or function name)" s)
                else preturn s)

// infix operator (function name)
let op_name (sign : SIGNATURE) =
    (alphanumeric_identifier <|> symbolic_identifier)
        >>= (fun s -> if is_function_name s sign && is_infix s sign then preturn s else pfail)

// 'new_fct_name' is for use in function definitions, differs from 'fct_name' in that it must be not be in the signature
// !!! add syntax for user-defined infix operators at some point
let new_fct_name (sign : SIGNATURE) =
    (alphanumeric_identifier)
        >>= (fun s -> if not (is_name_defined s sign) then preturn s else failwith (sprintf "name '%s' in function definition is already in use" s))

let new_rule_name (sign : SIGNATURE) =
    (alphanumeric_identifier)
        >>= (fun s -> if not (is_name_defined s sign) then preturn s else failwith (sprintf "name '%s' in rule definition is already in use" s))

let name (sign : SIGNATURE) =
        ( kw "true"      |>> (fun _ -> BoolConst true) )
    <|> ( kw "false"     |>> (fun _ -> BoolConst false) )
    <|> ( kw "undef"     |>> (fun _ -> UndefConst) )
    <|> ( int            |>> (fun i -> IntConst i) )
    <|> ( fct_name sign  |>> (fun s -> FctName s) )
    // !!!! StringConst still missing

//--------------------------------------------------------------------

let typecheck_name name (sign : SIGNATURE, _ : Map<string, TYPE>) =
    match name with
    |   UndefConst      -> (UndefConst,    ([], Undef))
    |   BoolConst b     -> (BoolConst b,   ([], Boolean))
    |   IntConst i      -> (IntConst i,    ([], Integer))
    |   StringConst s   -> (StringConst s, ([], String))
    |   FctName f       -> (FctName f,     fct_type f sign)

let typecheck_app_term sign = function
    |   (fct_name, ts)  -> failwith ""

let rec typecheck_term (t : TERM) (sign : SIGNATURE, tyenv : Map<string, TYPE>) : TYPE =
    term_induction typecheck_name {
        Value    = fun x _ -> type_of_value x;
        AppTerm  = fun (f, ts) (sign, tyenv) ->
                        match f (sign, tyenv) with
                        |   (FctName f, (f_dom, f_ran)) ->  // fprintf stderr "typecheck_term %A\n" (f, (ts >>| fun t -> t (sign, tyenv)))
                                                            match_fct_type f (ts >>| fun t -> t (sign, tyenv)) (f_dom, f_ran)
                        |   (_, (_, f_ran)) -> f_ran    // special constants UndefConst, BoolConst b, etc.
        CondTerm = fun (G, t1, t2) (sign, tyenv) ->
                        if G (sign, tyenv) <> Boolean
                        then failwith (sprintf "type of guard in conditional term must be Boolean)")
                        else
                        (   let (t1, t2) = (t1 (sign, tyenv), t2 (sign, tyenv))
                            if t1 = t2 then t1
                            else failwith (sprintf "branches of conditional term have different types (then-branch: %s; else-branch: %s)"
                                                (t1 |> type_to_string) (t2 |> type_to_string))  );
        Initial  = fun (f, xs) (sign, tyenv) ->
                    match fct_type f sign with
                    |   (f_dom, f_ran) ->  match_fct_type f (xs >>| type_of_value) (f_dom, f_ran);
        // VarTerm  = fun v -> fun (_, tyenv) -> try Map.find v tyenv with _ -> failwith (sprintf "variable '%s' not defined" v);
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
                            let (f_dom, f_ran) = fct_type f sign
                            let ts = ts >>| fun t -> t (sign, tyenv)
                            let t_type  = t (sign, tyenv)
                            let f_res_type = match_fct_type f ts (f_dom, f_ran)
                            if t_type <> f_res_type
                            then failwith (sprintf "type of right-hand side of update rule (%s) does not match type of function %s : %s -> %s"
                                                (t_type |> type_to_string) f (ts |> type_list_to_string) (f_res_type |> type_to_string))
                            else Rule
                        else
                            failwith (sprintf "error: function %s on the left-hand of update rule is of the wrong kind (it should be 'controlled', 'shared' or 'out')" f);
        CondRule   = fun (G, R1, R2) (sign, tyenv) -> 
                        if G (sign, tyenv) <> Boolean
                        then failwith (sprintf "type of guard in conditional rule must be Boolean)")
                        else
                        (   let (R1, R2) = (R1 (sign, tyenv), R2 (sign, tyenv))
                            if R1 = R2 then Rule
                            else failwith (sprintf "typecheck_rule: CondRule: this should not happen")  );
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
let rec operator_parser (parse_elem : SIGNATURE -> Parser<'elem>, app_cons : NAME * 'elem list -> 'elem) (sign : SIGNATURE) (s : ParserInput) : ParserResult<'elem> = 
    let elem_ s = parse_elem sign s
    let op_name_ s = op_name sign s
    let op_parse_ s = operator_parser (parse_elem, app_cons) sign s
    let reduce = function 
    |   [Opnd t] -> [Opnd t]
    |   (Opnd tR) :: (Optr (_, oper)) :: (Opnd tL) :: rest ->
            Opnd (app_cons (FctName oper, [ tL; tR ])) :: rest
    |   [] -> failwith "operator parsing: 'reduce' applied to empty stack)"
    |   (_ :: stack) -> failwith "operator parsing: badly formed stack"
    let rec extract = function
    |   [Opnd t] -> t
    |   stack -> extract (reduce stack)
    let rec F (stack : 'elem STACK_ELEM list) (s : ParserInput) : ParserResult<'elem> = 
      ( (* printf "F %A %A\n" stack s *)
        match stack with
        |   [Opnd t1] ->
                ( ((op_name_ : Parser<string>) ++ (elem_ : Parser<'elem>)) 
                        >>= (fun (op, t2 : 'elem) -> F ([ Opnd t2; Optr (infix_status op sign, op); Opnd t1 ] : 'elem STACK_ELEM list)) )
                <|> (preturn (extract stack)) 
        |   ((Opnd t2) :: (Optr (Infix (assoc1, prec1), op1)) :: stack_rest) ->
                ( (((op_name_ : Parser<string>) ++ (elem_ : Parser<'elem>))
                        >>= (fun (op2, t3 : 'elem) ->
                            match infix_status op2 sign with
                            |   NonInfix -> failwith (sprintf "operator parsing: infix operator expected, '%s' found instead" op2)
                            |   Infix (assoc2, prec2) -> 
                                    if (prec1 < prec2) || (prec1 = prec2 && assoc1 = RightAssoc && assoc2 = RightAssoc)
                                    then F ((Opnd t3)::(Optr (Infix (assoc2, prec2), op2))::stack)
                                    else if (prec1 > prec2) || (prec1 = prec2 && assoc1 = LeftAssoc && assoc2 = LeftAssoc)
                                    then F ((Opnd t3)::(Optr (Infix (assoc2, prec2), op2))::(reduce stack))
                                    else failwith (sprintf "operator parsing: infix operators '%s' and '%s' have the same precedence, but different associativity" op1 op2)))
                <|> (preturn (extract stack)) )
        | _ -> failwith "operator parsing: badly formed stack"  (* this should never happen *) ) s
    (elem_ >>= fun t1 -> F [ (Opnd t1) ]) s

//--------------------------------------------------------------------

let mkAppTerm sign = function
|   (FctName f, ts) ->
        if arity f sign = List.length ts
        then AppTerm (FctName f, ts)
        else failwith (sprintf "function '%s' with arity %d applied to %d arguments" f (arity f sign) (List.length ts))
|   (UndefConst,    []) -> AppTerm (UndefConst, [])
|   (BoolConst b,   []) -> AppTerm (BoolConst b, [])
|   (IntConst i,    []) -> AppTerm (IntConst i, [])
|   (StringConst s, []) -> AppTerm (StringConst s, [])
|   (_, ts) -> failwith (sprintf "constant / 0-ary function applied to %d arguments" (List.length ts))


let rec simple_term (sign : SIGNATURE) (s : ParserInput) : ParserResult<TERM> = 
    let (fct_name_, name_, variable_, mkAppTerm_) = (fct_name sign, name sign, variable sign, mkAppTerm sign)
    let term_ s = term sign s
    (       (* ( (kw "let" >>. variable_) .>>. (kw "=" >>. term_) .>> kw "in" .>>. (term_ .>> kw "endlet") |>> fun ((x, t1), t2) -> LetTerm (x, t1, t2) )
        <|>*)
            ( R3 (kw "if" << term_) (kw "then" << term_) (poption (kw "else" << term_)) >> kw "endif"
                |>> function  (G, r_then, opt_R_else) -> CondTerm (G, r_then, match opt_R_else with Some r_else -> r_else | None -> AppTerm (UndefConst, [])) )
        <|>
            ( R3 ( fct_name_ >> lit "(" )   term_   (pmany (lit "," << term_) >> lit ")")
                |>> fun (f, t, ts) -> mkAppTerm_ (FctName f, t :: ts) ) 
        <|> ( fct_name_ >> lit "(" >> lit ")" |>> fun f -> mkAppTerm_ (FctName f, []) )
        <|> ( name_                             |>> fun nm -> mkAppTerm_ (nm, []) )  // 0-ary function names and special constants (int, string etc.)
      (*<|> ( variable_                         |>> fun s -> VarTerm s ) *)
        <|> ( lit "(" << term_ >> lit ")" )
    ) s

and term (sign : SIGNATURE) (s : ParserInput) : ParserResult<TERM> = 
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

let rec rule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE> =
    let (fct_name_, name_, term_) = (fct_name sign, name sign, term sign)
    let rule_ s = rule sign s
    (       ( (R3 term_ (kw ":=") term_) |>> fun (t1,_,t2) -> mkUpdateRule sign (t1, t2) )
        <|> ( kw "skip" |>> fun _ -> skipRule )
        <|> ( kw "par" << pmany1 rule_ >> kw "endpar" |>> fun Rs -> ParRule Rs)
        <|> ( ((lit "{" << rule_) ++ pmany (lit "," << rule_)) >> (lit "}") |>> fun (R1, Rs) -> ParRule (R1::Rs) )
        <|> ( kw "seq" << pmany1 rule_ >> kw "endseq" |>> fun Rs -> SeqRule Rs)
        <|> ( ((lit "[" << rule_) ++ pmany (lit ";" << rule_)) >> (lit "]") |>> fun (R1, Rs) -> SeqRule (R1::Rs) )
        <|> ( (R3 (kw "if" << term_) (kw "then" << rule_) (poption (kw "else" << rule_)) >> kw "endif")
                |>> function  (G, r_then, opt_R_else) -> CondRule (G, r_then, match opt_R_else with Some r_else -> r_else | None -> skipRule) )
        <|> ( kw "iterate" << rule_ >> poption (kw "enditerate") |>> fun R -> IterRule R )
        <|> ( (kw "while" << lit "(" << term_ >> lit ")") ++ rule_ >> poption (kw "endwhile") |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule)) )
        <|> ( pfail_msg "rule" "rule expected" )
    ) s

//--------------------------------------------------------------------

let type_ (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE> =
    (       (*( kw "Any"     |>> fun _ -> Any )
        <|>*) ( kw "Undef"   |>> fun _ -> Undef)
        <|> ( kw "Boolean" |>> fun _ -> Boolean)
        <|> ( kw "Integer" |>> fun _ -> Integer)
        <|> ( kw "String " |>> fun _ -> String) ) s

let fct_parameter_types (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE list * TYPE> =
    let type_ = type_ sign
    (       ( R3 (poption (kw ":") << lit "(" << type_) (pmany (lit "," << type_)) (lit ")" << kw "->" << type_)
                |>> fun (ty1, tys, ty_dom) -> (ty1 :: tys, ty_dom) )
        <|> ( R3 (kw ":" << type_) (pmany (lit "," << type_)) (kw "->" << type_)
                |>> fun (ty1, tys, ty_dom) -> (ty1 :: tys, ty_dom) )
        <|> ( ( kw ":" << type_ ++ (kw "->" << type_) )
                |>> fun (ty1, ty_dom) -> ([ty1], ty_dom) )
        <|> ( ( ((kw ":" <|> kw "->") << type_) )
                |>> fun ty_dom -> ([], ty_dom) )
    ) s

let fct_initially (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<Map<VALUE list, VALUE>> =
    // for the time being, only 0-ary functions can be initialised
    let term = term sign
    (       ( ((kw "initially") << term)
                |>> fun t -> let _ = typecheck_term t (sign, Map.empty)
                             Map.add [] (Eval.eval_term t (state, Map.empty)) Map.empty )
    ) s

let definition (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB> =
    let (new_fct_name, fct_parameter_types, fct_initially, new_rule_name, rule) =
            (new_fct_name sign, fct_parameter_types sign, fct_initially (sign, state), new_rule_name sign, rule sign)
    let opt_state_initialisation f (tys_ran, ty_dom) opt_initially = 
            match opt_initially with
                |   None -> empty_state
                |   Some initial_values ->
                        let _ = Map.map (fun xs y -> 
                                    if (xs >>| type_of_value, type_of_value y) <> (tys_ran, ty_dom)
                                    then failwith (sprintf "type mismatch in initialisation of function '%s'" f)
                                    else ()) initial_values
                        state_override_dynamic empty_state (Map.add f initial_values Map.empty)
    (   (   ( ((kw "controlled" <|> kw "function" <|> (kw "controlled" >> kw "function")) << new_fct_name ++ fct_parameter_types) ++ (poption fct_initially) )
                |>> fun ((f, (tys_ran, ty_dom)), opt_initially) ->
                        (   add_function_name f (Controlled, (tys_ran, ty_dom), NonInfix) Map.empty,
                            opt_state_initialisation f (tys_ran, ty_dom) opt_initially,
                            empty_rules_db ) )
        <|> ( ((kw "rule" << new_rule_name) ++ (kw "=" << rule))
                |>> fun (rule_name, R) ->
                        let _ = typecheck_rule R (sign, Map.empty)
                        (   add_rule_name rule_name [] Signature.empty_signature,
                            empty_state,
                            add_rule rule_name R empty_rules_db ) )   // parameterless rule: empty type list
    ) s

let rec definitions (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =
    match definition (sign, state) s with 
    |   ParserSuccess ((sign', state', rules_db'), s') ->
        (   match definitions (signature_override sign sign', state_override state state') s' with
            |   ParserSuccess ((sign'', state'', rules_db''), s'') ->
                    ParserSuccess ((signature_override sign' sign'', state_override state' state'', rules_db_override rules_db' rules_db''), s'')
            |   ParserFailure ("rule", s'', msg) ->
                    ParserFailure ("rule", s'', msg)
            |   ParserFailure (name, s'', msg) ->
                    ParserSuccess ((sign', state', rules_db'), s') )
    | ParserFailure (name, s', msg) -> ParserFailure (name, s', msg)

//--------------------------------------------------------------------

let make_parser parse_fct sign s =
    match (parse_fct sign >> ws_or_comment) (parser_input_from_string s) with
    |   ParserSuccess (r, _) -> r
    |   ParserFailure (name, s', msg) -> failwith (parser_msg (ParserFailure (name, s', msg)))

//--------------------------------------------------------------------
// parser "API"

let parse_and_typecheck parsing_fct typechecking_fct sign s =
    let ast = (make_parser parsing_fct) sign s
    let _   = typechecking_fct ast (sign, Map.empty)   // function result is discarded, but exceptions are thrown on typing errors
    ast

let parse_name sign s = parse_and_typecheck name typecheck_name sign s
let parse_term sign s = parse_and_typecheck term typecheck_term sign s
let parse_rule sign s = parse_and_typecheck rule typecheck_rule sign s
let parse_definitions (sign, S) s = make_parser definitions (sign, S) s
