module Parser

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let trace = ref 0

let module_name = "Parser"

type ErrorDetails =
|   SyntaxError of string * Set<ParserCombinators.FailedAt>
|   SignatureError of Signature.ErrorDetails
|   StaticFunctionExpected of string * FCT_KIND
|   InfixOperatorExpected of string
|   InfixOperatorsSamePrecedenceDifferentAssociativity of string * string
|   CondTermGuardNotBoolean
|   CondTermBranchesWithDifferentTypes of TYPE * TYPE
|   UndefinedVariable of string
|   UpdateRuleNotControlledOrOut of string
|   UpdateRuleTypesOfLhsAndRhsDoNotMatch of TYPE * TYPE
|   UpdateRuleLhsNotInAppTermForm
|   FunctionNameAlreadyDeclared of string
|   RuleAlreadyDefined of string

exception Error of string * SrcReg option * ErrorDetails

let error_msg (fct : string, reg : SrcReg option, err : ErrorDetails) = 
    sprintf "error - function %s.%s:\n%s" module_name fct (ParserCombinators.opt_src_reg_to_string reg) +
    match err with
    |   SyntaxError (where, failures) ->
            sprintf "syntax error in %s:\n%s" where (ParserCombinators.failure_msg failures)
    |   SignatureError details ->
            sprintf "type error:\n%s\n" (Signature.error_msg details)
    |   StaticFunctionExpected (f, kind) ->
            sprintf "static function expected (%s function '%s' found instead)" (kind |> fct_kind_to_string) f
    |   InfixOperatorExpected op ->
            sprintf "operator parsing: infix operator expected, '%s' " op
    |   InfixOperatorsSamePrecedenceDifferentAssociativity (op1, op2) ->
            sprintf "operator parsing: infix operators '%s' and '%s' have the same precedence, but different associativity" op1 op2
    |   CondTermGuardNotBoolean ->
            "type error: guard of conditional term is not of type Boolean"
    |   CondTermBranchesWithDifferentTypes (t1, t2) ->
            sprintf "branches of conditional term have different types (then-branch: %s; else-branch: %s)" (t1 |> type_to_string) (t2 |> type_to_string)
    |   UndefinedVariable v ->
            sprintf "variable '%s' is not defined" v
    |   UpdateRuleNotControlledOrOut f ->
            sprintf "update rule: function to be updated must be of 'controlled' or 'out' kind (function '%s' found instead)" f
    |   UpdateRuleLhsNotInAppTermForm ->
            "update rule: left-hand side must be in the form of an application term, i.e.: f(t_1, ..., t_n) := ..."
    |   UpdateRuleTypesOfLhsAndRhsDoNotMatch (t_lhs, t_rhs) ->
            sprintf "update rule: types of left-hand side and right-hand side do not match\n  left-hand side:  %s\n  right-hand side: %s" (t_lhs |> type_to_string) (t_rhs |> type_to_string)
    |   FunctionNameAlreadyDeclared f ->
            sprintf "function name '%s' already declared" f
    |   RuleAlreadyDefined r ->
            sprintf "rule '%s' already defined" r

//--------------------------------------------------------------------

let add_var_distinct reg (v, ty) env =
    try TypeEnv.add_distinct v ty env
    with Signature.Error details-> raise (Error ("add_var_distinct", Some reg, SignatureError details))

//--------------------------------------------------------------------

let pcharf c = pcharsat c ""

let one_line_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    (   R4  (pstring "//")
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
    in ( R3 open_ inside close_ |>> fun (s1, s2, s3) ->  (s1 + implode s2 + s3) ) s

let rec C_multiline_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    let open_ = pstring "/*"
    let close_ = pstring "*/"
    let inside = pmany (    ( pcharf (fun c -> c <> '*' && c <> '/') |>> fun c -> [c])
                        <|> ((pchar '/') ++ pcharf (fun c -> c <> '*') |>> fun (c1,c2) -> [c1;c2])
                        <|> ((pchar '*') ++ pcharf (fun c -> c <> '/') |>> fun (c1,c2) -> [c1;c2])
                        <|> (fun input -> (C_multiline_comment |>> explode) input) )  |>> List.concat
    in ( R3 open_ inside close_ |>> fun (s1, s2, s3) ->  (s1 + implode s2 + s3) ) s

let comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    (   ( one_line_comment <|> ML_multiline_comment <|> C_multiline_comment )
    |>> fun s' -> ( (if !trace > 0 then fprintf stderr "comment:\n%s\n" s' else ());
                    s' )   )    s

let ws_or_comment (s : ParserInput<'state>) : ParserResult<string, 'state> =
    ( pwhitespace ++ (pmany (comment ++ pwhitespace))
        |>> fun (strg, strg_list : (string*string) list) -> strg + String.concat "" (List.map (fun (s1, s2) -> s1+s2) strg_list) ) s

let skip_to_eos (s : ParserInput<'state>) : ParserResult<string, 'state> =
    ( ws_or_comment >> peos ) s

let lit arg s = (ws_or_comment << pstring arg >> pwhitespace) s
let int s = (ws_or_comment << pint >> pwhitespace) s
    
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

let popt_bool p =
    poption p |>> function None -> false | Some _ -> true

let psep0 p sep =
    poption (p ++ pmany (sep << p)) |>> function Some (x, xs) -> x::xs | None -> []

let psep1 p sep =
    p ++ pmany (sep << p) |>> fun (x, xs) -> x::xs

let psep1_lit p sep =
    p ++ pmany ((lit sep) << p) |>> fun (x, xs) -> x::xs

let psep2_lit p sep =
    p ++ pmany1 ((lit sep) << p) |>> fun (x, xs) -> x::xs

let opt_psep1 encl_begin p sep encl_end =
    poption (lit encl_begin << (psep1_lit p sep) >> lit encl_end) |>> function None -> [] | Some xs -> xs

let opt_psep2 encl_begin p sep encl_end =
    poption (lit encl_begin << psep2_lit p sep >> lit encl_end) |>> function None -> [] | Some xs -> xs

//--------------------------------------------------------------------

/// Parse keywords
let kw kw_name s =
    (   (   (   (ws_or_comment << (pletter ++ (pmany palphanum_) |>> fun (c, cs) -> c :: cs) >> pwhitespace))
            <|> (ws_or_comment << (pmany1 symb_ident_char) >> pwhitespace) )
                    >>= fun s -> let s = implode s in if s = kw_name then preturn s else pfail_msg s ) s

//--------------------------------------------------------------------

type PARSER_STATE = SIGNATURE * STATE

let get_signature (sign : SIGNATURE,state : STATE) = sign
let get_state (sign : SIGNATURE, state : STATE) = state

let get_signature_from_input (s : ParserInput<PARSER_STATE>) = get_parser_state s |> get_signature
let get_state_from_input (s : ParserInput<PARSER_STATE>)     = get_parser_state s |> get_state

let change_sign f (sign, state) = (f sign, state)

//--------------------------------------------------------------------

let alphanumeric_identifier s =
    (   ws_or_comment << (pletter ++ (pmany palphanum_))
            |>> (fun (s, d) -> new System.String(s::d |> List.toArray)) ) s

let symbolic_identifier s =
    (   ws_or_comment << (pmany1 symb_ident_char)
            |>> (fun s -> new System.String(s |> List.toArray)) ) s

let variable_identifier s =
    // starting with '$', AsmetaL-style
    ((ws_or_comment << pchar '$' << (pletter ++ (pmany palphanum_)) |>> fun (id_1, id_rest) -> implode ('$' :: id_1 :: id_rest))) s

// non-infix function name
let fct_name (s : ParserInput<PARSER_STATE>) =
    (   (alphanumeric_identifier <|> symbolic_identifier)
            >>== (fun _ (sign, _) s ->
                if is_function_name s sign && not (is_infix s sign)
                then preturn s
                else pfail_msg s) ) s

let variable s =
    (   alphanumeric_identifier
            >>== (fun _ (sign, _) s ->
                if s = "true" || s = "false" || s = "undef" || is_function_name s sign
                then pfail_msg s
                else preturn s) ) s

// infix operator (function name)
let op_name s =
    (   (alphanumeric_identifier <|> symbolic_identifier)
            >>== (fun _ (sign, _) s ->
                if is_function_name s sign && is_infix s sign
                then preturn s
                else pfail_msg s) ) s

// 'new_fct_name' is for use in function definitions, differs from 'fct_name' in that it must be not be in the signature
// !!! add syntax for user-defined infix operators at some point
let new_fct_name s =
    (   alphanumeric_identifier
            >>== (fun reg (sign, _) s -> if not (is_name_defined s sign) then preturn s else raise (Error ("new_fct_name", Some reg, FunctionNameAlreadyDeclared s))) ) s

let new_rule_name s =
    (   (alphanumeric_identifier)
            >>== (fun reg (sign, _) s -> if not (is_name_defined s sign) then preturn s else raise (Error ("new_rule_name", Some reg, RuleAlreadyDefined s))) ) s

let name s =
    (       ( kw "true"  |>> (fun _ -> BoolConst true) )
        <|> ( kw "false" |>> (fun _ -> BoolConst false) )
        <|> ( kw "undef" |>> (fun _ -> UndefConst) )
        <|> ( int        |>> (fun i -> IntConst i) )
        <|> ( fct_name   |>> (fun s -> FctName s) ) ) s
    // !!!! StringConst still missing

//--------------------------------------------------------------------

type 'a STACK_ELEM =
| Opnd of SrcReg * 'a                       (* operand  *)
| Optr of Signature.INFIX_STATUS * string   (* operator *)

/// Parses terms with infix operators, according to specified associativity and precedence
let rec operator_parser (static_term, env) (elem : bool * TypeEnv.TYPE_ENV -> Parser<'elem, PARSER_STATE>, app_cons : SrcReg option -> NAME * 'elem list -> 'elem) (sign : SIGNATURE) (s : ParserInput<PARSER_STATE>) : ParserResult<'elem, PARSER_STATE> = 
    //let show_stack stack = (stack |> List.map (function Opnd (reg, t) -> sprintf "[%s]" (t |> term_to_string sign) | Optr (_, oper) -> sprintf "%s" oper) |> String.concat " ")
    let elem = elem (static_term, env)
    let reduce stack =
        let result =
            match stack with
            |   [Opnd (reg, t)] -> [Opnd (reg, t)]
            |   (Opnd (regR as (loc, pos_begR, pos_endR), tR)) :: (Optr (_, oper)) :: (Opnd (regL as (_, pos_begL, pos_endL), tL)) :: rest ->
                    let reg = (loc, pos_begL, pos_endR)
                    Opnd (reg, app_cons (Some reg) (FctName oper, [ tL; tR ])) :: rest
            |   [] -> failwith "operator parsing: 'reduce' applied to empty stack)"
            |   (_ :: stack) -> failwith "operator parsing: badly formed stack"
        result
    let rec extract = function
    |   [Opnd (reg, t)] -> t
    |   stack -> extract (reduce stack)
    let rec F (stack : 'elem STACK_ELEM list) (s : ParserInput<PARSER_STATE>) : ParserResult<'elem, PARSER_STATE> = 
        match stack with
        |   [Opnd (reg1, t1)] ->
                match (op_name s) with
                |   ParserSuccess (op1, (s' as (_, loc', pos', _, _))) ->
                        match (elem s') with
                        |   ParserSuccess (t2, (s'' as (_, _, pos'', _, _))) ->
                                F ([ Opnd ((loc', pos', pos''), t2); Optr (infix_status op1 sign, op1); Opnd (reg1, t1) ]) s''
                        |   ParserFailure failures -> ParserFailure failures
                |   ParserFailure failures -> ParserSuccess (extract stack, s)
        |   ((Opnd (reg2, t2)) :: (Optr (Infix (assoc1, prec1), op1)) :: (stack_rest as (Opnd (reg1, t1) :: _))) ->
                match (op_name s) with
                |   ParserSuccess (op2, (s' as (_, loc', pos', _, _))) ->
                        match (elem s') with
                        |   ParserSuccess (t3, (s'' as (_, loc'', pos'', _, _))) ->
                                match infix_status op2 sign with
                                |   NonInfix -> raise (Error ("operator_parser", Some reg2, InfixOperatorExpected op2))
                                |   Infix (assoc2, prec2) -> 
                                        if (prec1 < prec2) || (prec1 = prec2 && assoc1 = RightAssoc && assoc2 = RightAssoc)
                                        then F ((Opnd ((loc', pos', pos''), t3))::(Optr (Infix (assoc2, prec2), op2))::stack) s''
                                        else if (prec1 > prec2) || (prec1 = prec2 && assoc1 = LeftAssoc && assoc2 = LeftAssoc)
                                        then F ((Opnd ((loc', pos', pos''), t3))::(Optr (Infix (assoc2, prec2), op2))::(reduce stack)) s''
                                        else raise (Error ("operator_parser", Some (merge_src_reg reg1 reg2), InfixOperatorsSamePrecedenceDifferentAssociativity (op1, op2)))
                        |   ParserFailure failures -> ParserFailure failures
                |   ParserFailure failures -> ParserSuccess (extract stack, s)
        | _ -> failwith "operator parsing: badly formed stack"  (* this should never happen *)
    (elem >>== fun reg1 _ t1 s -> F [ (Opnd (reg1, t1)) ] s) s

// --- syntactic sugar for terms -------------------------------------

let mkAppTerm (static_term : bool) (reg : SrcReg option) sign args =
    match args with
    |   (UndefConst, _)    -> AppTerm' (Undef, args)
    |   (BoolConst _, _)   -> AppTerm' (Boolean, args)
    |   (IntConst _, _)    -> AppTerm' (Integer, args)
    |   (StringConst _, _) -> AppTerm' (String, args)
    |   (FctName f, ts)    ->
            try let kind = fct_kind f sign
                if static_term && kind <> Static
                then raise (Error ("mkAppTerm", reg, StaticFunctionExpected (f, kind)))
                else AppTerm' (match_fct_type f (ts >>| get_type) (fct_types f sign), args)       // !!!! no overloading yet
            with Signature.Error details -> raise (Error ("mkAppTerm", reg, SignatureError details))
let mkVarTerm reg env v =
    try VarTerm' (TypeEnv.get v env, v)
    with _ -> raise (Error ("mkVarTerm", Some reg, UndefinedVariable v))

let mkCondTerm (reg : SrcReg option) (G, t1, t2) =
    if get_type G <> Boolean
    then raise (Error ("mkCondTerm", reg, CondTermGuardNotBoolean))
    else let (t1_type, t2_type) = (get_type t1, get_type t2)
         if t1_type = t2_type
         then CondTerm' (t1_type, (G, t1, t2))
         else raise (Error ("mkCondTerm", reg, CondTermBranchesWithDifferentTypes (t1_type, t2_type)))

let mkQuantTerm reg =
    failwith "mkQuantTerm: not implemented"

let mkDomainTerm ty =
    DomainTerm' (Powerset ty, ty)

(*
let let_term_with_multiple_bindings (v_ti_list : (string * TYPED_TERM list)) (t : TYPED_TERM) =
    let t_type = get_type t
    let rec mk_let_term = function
    |   [] -> failwith "let_term_with_multiple_bindings: empty list of bindings"
    |   [(v, t_i)] -> LetTerm' (t_type, (v, t_i, t))
    |   (v, t_i) :: v_t_list -> LetTerm' ((t_type, v, t_i, mk_let_term v_t_list))
    in mk_let_term v_ti_list
*)

let switch_to_cond_term static_term reg sign (t, cases : (TYPED_TERM * TYPED_TERM) list, otherwise : TYPED_TERM) =
    let mkCondTerm = mkCondTerm reg
    let mkAppTerm = mkAppTerm static_term reg sign
    let rec mk_cond_term = function
    |   [] -> failwith "switch_to_cond_term: empty list of cases"
    |   [(t1, t2)] -> mkCondTerm (mkAppTerm (FctName "=", [t; t1]), t2, otherwise)
    |   (t1, t2) :: cases -> mkCondTerm (mkAppTerm (FctName "=", [t; t1]), t2, mk_cond_term cases)
    mk_cond_term cases

let switch_to_cond_rule reg sign (t, cases : (TYPED_TERM * RULE) list, otherwise : RULE) =
    let mkAppTerm = mkAppTerm false reg sign
    let rec mk_cond_term = function
    |   [] -> failwith "switch_to_cond_rule: empty list of cases"
    |   [(t1, t2)] -> CondRule (mkAppTerm (FctName "=", [t; t1]), t2, otherwise)
    |   (t1, t2) :: cases -> CondRule (mkAppTerm (FctName "=", [t; t1]), t2, mk_cond_term cases)
    in mk_cond_term cases

//--------------------------------------------------------------------

let rec simple_term (static_term, env0 : TypeEnv.TYPE_ENV) (s : ParserInput<PARSER_STATE>) : ParserResult<TYPED_TERM, PARSER_STATE> = 
    // FiniteQuantificationTerm 	::= 	( ForallTerm | ExistUniqueTerm | ExistTerm )
    // ExistTerm 	                ::= 	"(" <EXIST> VariableTerm <IN> Term ( "," VariableTerm <IN> Term )* ( <WITH> Term )? ")"
    // ExistUniqueTerm 	            ::= 	"(" <EXIST> <UNIQUE> VariableTerm <IN> Term ( "," VariableTerm <IN> Term )* ( <WITH> Term )? ")"
    // ForallTerm 	                ::= 	"(" <FORALL> VariableTerm <IN> Term ( "," VariableTerm <IN> Term )* ( <WITH> Term )? ")" 
    let term_in_env = term
    let term = term (static_term, env0)
    let mkAppTerm = mkAppTerm static_term
    let quantificationTerm =
        let quantContent = R2 (psep1_lit ((variable_identifier >> (kw "in")) ++ ((term |>> fun _ -> "") <|> alphanumeric_identifier (*!!!temporary: should be domain name*) )) ",")
                                (poption (kw "with" >> term))
        (   ( kw "forall" << quantContent )
        <|> ( kw "exist" << kw "unique" << quantContent )
        <|> ( kw "exist" << quantContent ) )
    (       ( (kw "not" << term)
                |||>> fun reg (sign, _) t -> mkAppTerm (Some reg) sign (FctName "not", [t]) )
        <|> ( R3 (kw "if" << term) (kw "then" << term) (poption (kw "else" << term)) >> kw "endif"
                |||>> fun reg (sign, _) (G, r_then, opt_R_else) -> mkCondTerm (Some reg) (G, r_then, match opt_R_else with Some r_else -> r_else | None -> mkAppTerm (Some reg) sign (UndefConst, [])) )
        <|>
            ( R3 ( fct_name >> lit "(" )   term   (pmany (lit "," << term) >> lit ")")  //!!!! is this production rule wrong ?
                |||>> fun reg (sign, _) (f, t, ts) -> mkAppTerm (Some reg) sign (FctName f, t :: ts) ) 
        <|> ( fct_name >> lit "(" >> lit ")"
                |||>> fun reg (sign, _) f -> mkAppTerm (Some reg) sign (FctName f, []) )
        <|> ( name
                |||>> fun reg (sign, _) nm -> mkAppTerm (Some reg) sign (nm, []) )  // 0-ary function names and special constants (int, string etc.)
        <|> ( variable_identifier
                |||>> fun reg (sign, _) id -> mkVarTerm reg env0 id )
        <|> ( lit "{" >> lit "}"
                |||>> fun reg (sign, _) _ -> mkAppTerm (Some reg) sign (FctName "emptyset", []) )
        <|> ( (lit "{" << term >> lit ":") ++ (term >> lit "}")
                |||>> fun reg (sign, _) (t1, t2) -> mkAppTerm (Some reg) sign (FctName "set_interval", [ t1; t2; mkAppTerm (Some reg) sign (IntConst 1, []) ]) )
        <|> ( R3 (lit "{" << term >> lit ":") (term >> lit ",") (term >> lit "}")
                |||>> fun reg (sign, _) (t1, t2, t3) -> mkAppTerm (Some reg) sign (FctName "set_interval", [ t1; t2; t3 ]) )
        <|> ( R3 (kw "switch" << term) (pmany1 ((kw "case" << term >> lit ":") ++ term)) (kw "otherwise" << term >> kw "endswitch")
                        (*                    // !!! note: 'otherwise' not optional to avoid 'undef' as default case *)
                |||>> fun reg (sign, _) (t, cases, otherwise) -> switch_to_cond_term static_term (Some reg) sign (t, cases, otherwise) )
        <|> ( lit "(" << quantificationTerm >> lit ")"
                |||>> fun reg (sign, _) -> mkQuantTerm reg sign (* !!! temporary !!! *) )
        <|> (   let p1 = (kw "let" << lit "(" << variable_identifier) ++ (kw "=" << term >> lit ")")
                let p2 reg env (v, t1) = kw "in" << term_in_env (static_term, add_var_distinct reg (v, get_type t1) env) >> kw "endlet"
                (p1 >>== fun reg _ (v, t1) -> p2 reg env0 (v, t1) >>= fun t2 -> preturn (LetTerm' (get_type t2, (v, t1, t2))) ) )
        <|> ( lit "(" << term >> lit ")" )
    ) s

and term (static_term : bool, env : TypeEnv.TYPE_ENV) (s : ParserInput<PARSER_STATE>) : ParserResult<TYPED_TERM, PARSER_STATE> = 
    let sign = get_signature_from_input s
    operator_parser (static_term, env) (simple_term, fun reg (f, ts) -> mkAppTerm static_term reg sign (f, ts)) sign s

//--------------------------------------------------------------------

let mkUpdateRule reg sign (t_lhs, t_rhs) =
    let err_msg tag = sprintf "update rule: %s term '%s' not allowed on left-hand side of update rule" tag (AST.term_to_string sign t_lhs)
    match t_lhs with
    |   AppTerm' (_, (FctName f, ts)) ->
            let k = fct_kind f sign
            if not (k = Controlled || k = Out)
            then raise (Error ("mkUpdateRule", reg, UpdateRuleNotControlledOrOut f))
            else if not (get_type t_lhs = get_type t_rhs)
            then raise (Error ("mkUpdateRule", reg, UpdateRuleTypesOfLhsAndRhsDoNotMatch (get_type t_lhs, get_type t_rhs)))
            else UpdateRule ((f, ts), t_rhs)
    |   _ -> raise (Error ("mkUpdateRule", reg, UpdateRuleLhsNotInAppTermForm))

let rec rule (env : TypeEnv.TYPE_ENV) (s : ParserInput<PARSER_STATE>) : ParserResult<RULE, PARSER_STATE> =
    let term = term (false, env)            // false, because terms in rules do not have to be static
    let rule = rule env
    let sign = get_signature_from_input s
    (       ( (R3 term (kw ":=") term) |||>> fun reg _ (t1,_,t2) -> mkUpdateRule (Some reg) sign (t1, t2) )
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

let fct_initially env (s : ParserInput<PARSER_STATE>) : ParserResult<Map<VALUE list, VALUE>, PARSER_STATE> =
    // for the time being, only 0-ary functions can be initialised
    (       ( ((kw "initially") << (term (true, env)))   // this term must be static
                |||>> fun reg (sign, state) t ->
                            Map.add [] (Eval.eval_term t (state, Map.empty)) Map.empty )
    ) s

let fct_eqdef env (s : ParserInput<PARSER_STATE>) : ParserResult<VALUE list -> VALUE, PARSER_STATE> =
    // for the time being, only 0-ary functions can be initialised
    (       ( ((kw "=") << (term (true, env)))  // this term must be static
                |||>> fun reg (sign, _) t ->
                        let t_val = Eval.eval_term t (State.background_state  (* !!! use only background !!! *), Map.empty)
                        (function [] -> t_val | _ -> UNDEF) )
    ) s

let definition (env : TypeEnv.TYPE_ENV) (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE * STATE * RULES_DB, PARSER_STATE> =
    let (sign, state) = get_parser_state s
    let opt_state_initialisation (kind : Signature.FCT_KIND) f (tys_ran, ty_dom) (opt_static_def, opt_initially) = 
            match (opt_static_def, opt_initially) with
                |   (Some static_def, _) ->
                        state_override_static empty_state (Map.add f static_def Map.empty)
                |   (_, Some initial_values) ->
                        let _ = Map.map (fun xs y -> 
                                    if (xs >>| type_of_value sign, type_of_value sign y) <> (tys_ran, ty_dom)
                                    then failwith (sprintf "type mismatch in initialisation of function '%s'" f)
                                    else ()) initial_values
                        state_override_dynamic empty_state (Map.add f initial_values Map.empty)
                |   _ -> empty_state
    ( ( (   ( ((kw "static" >> poption (kw "function")) << new_fct_name ++ fct_parameter_types) ++ (poption (fct_eqdef env)) )
                |>> fun ((f, (tys_ran, ty_dom)), opt_fct_def) ->
                        (   add_function_name f (Static, NonInfix, (tys_ran, ty_dom)) Map.empty,
                            opt_state_initialisation (Signature.Static) f (tys_ran, ty_dom) (opt_fct_def, None),
                            empty_rules_db ) )
        <|> (   ( ((kw "controlled" <|> kw "function" <|> (kw "controlled" >> kw "function")) << new_fct_name ++ fct_parameter_types) ++ (poption (fct_initially env)) )
                |>> fun ((f, (tys_ran, ty_dom)), opt_initially) ->
                        (   add_function_name f (Controlled, NonInfix, (tys_ran, ty_dom)) Map.empty,
                            opt_state_initialisation (Signature.Controlled) f (tys_ran, ty_dom) (None, opt_initially),
                            empty_rules_db ) )
        <|> ( ((kw "rule" << new_rule_name) ++ (kw "=" << (rule env)))
                |||>> fun reg _ (rule_name, R) ->
                        (   add_rule_name rule_name [] Signature.empty_signature,
                            empty_state,
                            add_rule rule_name ([], R) empty_rules_db ) )   // parameterless rule: empty type list
    ) ||>> fun (sign, state) (sign', state', _) -> (signature_override sign sign', state_override state state' ) ) s

let rec definitions env (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE * STATE * RULES_DB, PARSER_STATE>  =
    (   ( definition env >> skip_to_eos )
    <|> ( definition env ++ definitions env
            |>> fun ((sign', state', rules_db'), (sign'', state'', rules_db'')) -> 
                    (signature_override sign' sign'', state_override state' state'', rules_db_override rules_db' rules_db'') )   // !!! inefficient, should be changed
    ) s

//--------------------------------------------------------------------

let make_parser parse_fct initial_location parser_state s =
    try
        match (parse_fct >> ws_or_comment) (parser_input_in_state_from_string initial_location parser_state s) with
        |   ParserSuccess (result, parser_state) -> (result, parser_state)
        |   ParserFailure errors -> failwith (parser_msg (ParserFailure errors))
    with ParserCombinators.SyntaxError (context, failures) ->
            let first_failure = Set.minElement failures
            let pos = fst first_failure
            raise (Error ("make_parser", Some (initial_location, pos, pos), SyntaxError (context, failures)))

//--------------------------------------------------------------------
// parser "API"

let parse_and_typecheck (parsing_fct : Parser<'a, PARSER_STATE>) (*typechecking_fct*) initial_location parser_state (s : string) =
    let sign = get_signature parser_state
    let (ast, parser_state') = make_parser parsing_fct initial_location parser_state s
//    let _   = typechecking_fct ast (sign, Map.empty)   // function result is discarded, but exceptions are thrown on typing errors
    ast

let parse_name initial_location sign s = parse_and_typecheck (name : Parser<NAME, PARSER_STATE>) initial_location (sign, empty_state) s
let parse_term initial_location sign s = parse_and_typecheck (term (false, TypeEnv.empty)) initial_location (sign, empty_state) s
let parse_rule initial_location sign s = parse_and_typecheck (rule TypeEnv.empty) initial_location (sign, empty_state) s

let parse_definitions initial_location (sign, S) s =
    let defs = fst (make_parser (definitions TypeEnv.empty) initial_location (sign, S) s)
    defs
