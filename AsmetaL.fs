module AsmetaL

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let trace = ref 0

let module_name = "AsmetaL"

type ErrorDetails =
|   SyntaxError of string
|   NotAFiniteSet of string * TYPE
|   FunctionNameNotInSignature of string
|   FunctionDefinitionTypeError of string * (TYPE list * TYPE) * (TYPE list * TYPE) list
|   ConstructorCannotBeRedefined of string
|   FunctionNotDeclaredAsControlled of string
|   FunctionNotDeclaredAsStaticOrDerived of string
|   CannotImportModule of string * string option * string option
|   InvariantNotBoolean

exception Error of string * SrcReg option * ErrorDetails

let error_msg (fct : string, reg : SrcReg option, err : ErrorDetails) = 
    sprintf "error - function %s.%s:\n%s" module_name fct (ParserCombinators.opt_src_reg_to_string reg) +
    match err with
    |   SyntaxError where ->
            sprintf "syntax error in %s" where
    |   NotAFiniteSet (v, ty) ->
            sprintf "error: range of variable '%s' must be a finite set (value of type '%s' found instead)" v (type_to_string ty)
    |   FunctionNameNotInSignature f ->
            sprintf "error in function definition: function name '%s' is not declared in the signature" f
    |   FunctionDefinitionTypeError (f, (def_ty_args, def_ty_res), sign_fct_types) ->
            sprintf "error in function definition: type mismatch in definition of function '%s':\n" f +
            sprintf "  definition: (%s) -> %s\n" (String.concat ", " (List.map type_to_string def_ty_args)) (type_to_string def_ty_res) +
            (List.map (fun (sign_ty_args, sign_ty_res) -> sprintf "  signature:  (%s) -> %s" (String.concat ", " (List.map type_to_string sign_ty_args)) (type_to_string sign_ty_res)) sign_fct_types |> String.concat "\n")
    |   ConstructorCannotBeRedefined f ->
            sprintf "error in function definition: constructor '%s' cannot be redefined" f
    |   FunctionNotDeclaredAsControlled f ->
            sprintf "error in function initialisation: function '%s' is not declared as controlled in the signature" f
    |   FunctionNotDeclaredAsStaticOrDerived f ->
            sprintf "error in function definition: function '%s' is not declared as static or derived in the signature" f
    |   CannotImportModule (mod_id, opt_dir, opt_full_path) ->
            sprintf "error in module import: cannot import module '%s'\n" mod_id +
            match (opt_dir, opt_full_path) with
            |   (Some dir, _) -> sprintf "(directory '%s' not found)\n" dir
            |   (None, Some full_path) -> sprintf "(cannot open file '%s')\n" full_path
            |   _ -> ""
    |   InvariantNotBoolean ->
            "error in invariant definition: invariant must be a Boolean term"

//--------------------------------------------------------------------

let add_var_distinct = Parser.add_var_distinct

let ID_DOMAIN = Parser.ID_DOMAIN
let ConcreteDomain = Parser.ConcreteDomain
let TypeDomain = Parser.TypeDomain
let getDomainByID = Parser.getDomainByID


//--------------------------------------------------------------------

type ASM_Definitions = {
    state : STATE;
    rules  : RULES_DB;
    macros : MACRO_DB;
}

type ASM_Content = {
    name : string;
    is_module : bool;
    is_asyncr : bool;
    imports : (string * ASM * string list option) list;
    exports : string list option;     // None means all are exported ("export*")
    signature : SIGNATURE;
    invariants : Map<string, TYPED_TERM>;      // all invariants have a name (if no name was explicitly given, a name is generated)
    definitions : ASM_Definitions;
    initial_states : (string * Map<string, STATE * MACRO_DB>) option;   // "default init" name and mapping from "init" names to corresponding definitions
}

and ASM = ASM of ASM_Content   // "asm" or "module" content

//--------------------------------------------------------------------

let asm_content (asyncr_module_name as (asyncr : bool, modul : bool, name : string))
                (imports : (string * ASM * string list option) list)
                (exports : string list option)
                (signature : SIGNATURE)
                (invariants : Map<string, TYPED_TERM>)
                (definitions : ASM_Definitions)
                (initial_states : (string * Map<string, STATE * MACRO_DB>) option)  : ASM_Content =
    {
        name = name;
        is_module = modul;
        is_asyncr = asyncr;
        imports = imports;
        exports = exports;
        signature = signature;
        invariants = invariants;
        definitions = {
            state  = definitions.state;
            rules  = definitions.rules;
            macros = definitions.macros;
        };
        initial_states = initial_states;
    }

let mkAsm   (asyncr : bool, modul : bool, name : string) (imports : (string * ASM * string list option) list) (exports : string list option)
            (signature : SIGNATURE) (invariants : Map<string, TYPED_TERM>) (definitions : ASM_Definitions) initial_states : ASM =
    ASM (asm_content (asyncr, modul, name) imports exports signature invariants definitions initial_states)

//--------------------------------------------------------------------

type PARSER_STATE = Parser.PARSER_STATE

type EXTENDED_PARSER_STATE = PARSER_STATE * (RULES_DB * MACRO_DB)

let invariant_counter = ref 1

//--------------------------------------------------------------------

let pcharf = Parser.pcharf
let ws_or_comment = Parser.ws_or_comment
let skip_to_eos = Parser.skip_to_eos
let lit = Parser.lit

let kw kw_name =
    (ws_or_comment << (pmany1 pletter))
        >>= fun s -> let s = implode s in if s = kw_name then preturn s else pfail_msg s

let alphanumeric_identifier =
    ws_or_comment << (pletter ++ (pmany palphanum_))
        |>> (fun (s, d) -> new System.String(s::d |> List.toArray))

let identifier = alphanumeric_identifier

let (popt_bool, psep0, psep1, psep1_lit, psep2_lit, opt_psep1, opt_psep2) =
    (Parser.popt_bool, Parser.psep0, Parser.psep1, Parser.psep1_lit, Parser.psep2_lit, Parser.opt_psep1, Parser.opt_psep2)

let MOD_ID =
    let escaped_char = pchar '\\' << pcharf (fun c -> c <> ' ')
    let non_quote_char = pcharf (fun c -> c <> '\"')
    ws_or_comment <<
        (   ( (pchar '\"' << (pmany (escaped_char <|> non_quote_char)) >> pchar '\"') |>> fun chars -> (implode chars) )
        <|> ( (poption (pletter >> pchar ':')) ++ (pmany1 (palphanum_ <|> pcharf (fun c -> c = '\\' || c = '/' || c = '.' || c = '-' )))
                |>> function (None, path) -> implode path | (Some drive_letter, path) -> (implode (drive_letter :: ':' :: path)) ) )

let ID_FUNCTION = identifier  //!!!! not exactly

let ID_VARIABLE = ws_or_comment << (pchar '$' ++ (pletter ++ (pmany palphanum_))) |>> fun (c1, (c2, s)) -> implode (c1 :: c2 :: s)
let ID_RULE = identifier  //!!!! not exactly
let ID_CTL = identifier       //!!!! not exactly
let ID_LTL = identifier


let Domain (s : ParserInput<PARSER_STATE>) =
    ((ConcreteDomain <|> TypeDomain) ||>> fun (sign, state) update_sign_fct -> (update_sign_fct sign, state)) s

let add_function_name f (kind, infix, (tys, ty)) sign =
    //!!! little hack to avoid overwriting of predefined background functions by Asmeta StandardLibrary.asm
    //!!! (which would destroy infix status of operators)
    if not (Map.containsKey f Background.signature)
    then add_function_name f (kind, infix, (tys, ty)) sign
    else fprintf stderr "warning: ignoring declaration of function '%s' already present in background signature\n" f; sign

let Function (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
    let (sign, _) = get_parser_state s
    // any function f : Prod(T1,...,Tn) -> T is converted into an n-ary function f : T1,...,Tn -> T  [n >= 0]
    let to_fct_type (tys : TYPE, ty_opt : TYPE option) =
        match (tys, ty_opt) with
        |   (ty, None)          -> ([], ty)
        |   (Prod tys, Some ty) -> (tys, ty)
        |   (ty, Some ty')      -> ([ty], ty')
    let StaticFunction     = R3 (kw "static"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                // !!! check whether the type is an enum type, then the static function is a constructor of this type ????
                                //    but can it be a regular function with the same name?
                                |>> fun (f, tys, opt_ty) ->
                                    let (ty_dom, ty_ran) = // correct special syntax of nullary functions
                                        match (tys, opt_ty) with
                                        |   (ty_ran, None) -> (Prod [], ty_ran)
                                        |   (ty_dom, Some ty_ran) -> (ty_dom, ty_ran)
                                    match (ty_dom, ty_ran) with
                                    |   (Prod [], TypeCons (ty, [])) ->
                                            if type_kind ty sign = EnumType then
                                                add_function_name f (Constructor, NonInfix, ([], TypeCons (ty, [])))
                                            else
                                                add_function_name f (Static, NonInfix, ([], TypeCons (ty, [])))
                                    |   _-> add_function_name f (Static, NonInfix, to_fct_type(tys, opt_ty))
    let DerivedFunction    = R3 (kw "derived" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> add_function_name f (Derived, NonInfix, to_fct_type(tys, opt_ty))
    let OutFunction        = R3 (poption (kw "dynamic") << kw "out"        << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: out function"
    let MonitoredFunction  = R3 (poption (kw "dynamic") << kw "monitored"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> add_function_name f (Monitored, NonInfix, to_fct_type(tys, opt_ty))
    let SharedFunction     = R3 (poption (kw "dynamic") << kw "shared"     << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: shared function"
    let ControlledFunction = R3 (poption (kw "dynamic") << kw "controlled" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) ->
                                    add_function_name f (Controlled, NonInfix, to_fct_type(tys, opt_ty))
    let LocalFunction      = R3 (poption (kw "dynamic") << kw "local"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: local function"
    let DynamicFunction    = OutFunction <|> MonitoredFunction  <|> SharedFunction <|> ControlledFunction <|> LocalFunction
    let BasicFunction      = StaticFunction <|> DynamicFunction
    ((BasicFunction <|> DerivedFunction)  ||>> fun (sign, state) update_sign_fct -> (update_sign_fct sign, state)) s


// --- syntactic sugar for rules ---

let let_rule_with_multiple_bindings v_t_list R =
    let rec mk_let_rule = function
    |   [] -> failwith "let_rule_with_multiple_bindings: empty list of bindings"
    |   [(v, t)] -> LetRule (v, t, R)
    |   (v, t) :: v_t_list -> LetRule (v, t, mk_let_rule v_t_list)
    in mk_let_rule v_t_list

let forall_rule_with_multiple_bindings reg sign v_tset_list t_filter R =
    let rec mk_forall_rule = function
    |   [] -> failwith "forall_rule_with_multiple_bindings: empty list of bindings"
    |   [(v, t)] -> ForallRule (v, t, t_filter, R)
    |   (v, t) :: v_t_list -> ForallRule (v, t, Parser.mkAppTerm false (Some reg) sign (BoolConst true, []), mk_forall_rule v_t_list)
    in mk_forall_rule v_tset_list

let switch_to_cond_rule reg sign (t, cases : (TYPED_TERM * RULE) list, otherwise : RULE option) =
    Parser.switch_to_cond_rule reg sign (t, cases, match otherwise with Some R -> R | None -> skipRule)

// ---------------------------------

let rec BasicRule env0 (s : ParserInput<PARSER_STATE>) =
    let Term_in_env = Parser.term
    let Rule_in_env = Rule
    let Term = Parser.term (false, env0)    // false, because terms in rules do not have to be static
    let Rule = Rule env0
    let BlockRule       = pmany1 Rule >> kw "endpar" |>> ParRule
    let ConditionalRule = R3 (Term) (kw "then" << Rule) (poption (kw "else" << Rule) |>> Option.defaultValue skipRule) >> kw "endif" |>> CondRule
    let VariableTerm    = ID_VARIABLE
    let LetRule =
        // !!! temporary: only one binding allowed
        //let p1 = (kw "let" << lit "(" << (psep1_lit ((VariableTerm >> lit "=") ++ Term) ",") >> lit ")")
        let p1 = (lit "(" << VariableTerm) ++ (lit "=" << Term >> lit ")")
        let p2 reg env (v, t1) = kw "in" << Rule_in_env (add_var_distinct reg (v, get_type t1) env) >> kw "endlet"
        (p1 >>== fun reg _ (v, t1) -> p2 reg env0 (v, t1) >>= fun R -> preturn (LetRule (v, t1, R)) )
    (*  // original rule:
        R2 (kw "let" << lit "(" << (psep1_lit ((VariableTerm >> lit "=") ++ Term) ",") >> lit ")") (kw "in" << Rule) >> (kw "endlet")
            |>> ( function
                    | ([(v, t)], R) -> LetRule (v, t, R)
                    | (v_t_list, R) -> let_rule_with_multiple_bindings v_t_list R )
    *)
    let ChooseRule = R4 (kw "choose" << psep1_lit ((VariableTerm >> kw "in") ++ Term) ",")
                        (kw "with" << Term) (kw "do" << Rule) (poption (kw "ifnone" << Rule))
                            |>> fun _ -> failwith "not implemented: choose rule"
    let ForallRule =
        // !!! temporary: only one binding allowed
        let p1 = VariableTerm ++ (kw "in" << Term)
            |||>> fun reg (sign, _) (v : string, t_range : TYPED_TERM) ->
                    // !!!! tbd: check that t_range is really a finite set, e.g. not Powerset(Integer)
                    match get_type t_range with
                    |   Powerset v_type -> ((v, v_type), t_range)
                    |   _ -> raise (Error ("BasicRule.ForallRule", Some reg, NotAFiniteSet (v, get_type t_range)))
        let p2 reg env (v, v_type) =
            let env' = add_var_distinct reg (v, v_type) env
            in (poption (kw "with" << Term_in_env (false, env'))) ++ (kw "do" << Rule_in_env env')
        p1 >>== fun reg (sign, _) ((v, v_type), t_range) ->
                    p2 reg env0 (v, v_type) >>=
                        fun (t_filter, R) ->
                                preturn (ForallRule (
                                    v, t_range,
                                    (match t_filter with
                                    |   Some tf -> tf
                                    |   None -> Parser.mkAppTerm true (Some reg) sign (BoolConst true, [])),   // missing "with"-clause is equivalent to "with true"
                                    R
                                ))

    (   (kw "skip" |>> fun _ -> skipRule)
    <|> (kw "par"    << no_backtrack "'par' rule" BlockRule)
    <|> (kw "if"     << no_backtrack "conditional rule" ConditionalRule)
    <|> (kw "let"    << no_backtrack "'let' rule" LetRule)
    <|> (kw "forall" << no_backtrack "'forall' rule" ForallRule)
    <|> MacroCallRule env0
    <|> ChooseRule
    // <|> ExtendRule
    ) s

and MacroCallRule env = ((ID_RULE >> lit "[") ++ (psep0 (Parser.term (false, env)) (lit ",") >> lit "]")) |>> MacroRuleCall

and TurboRule env (s : ParserInput<PARSER_STATE>) =
    let Rule = Rule env
    let SeqRule = pmany1 Rule >> kw "endseq" |>> AST.SeqRule
    let IterateRule = Rule >> kw "enditerate" |>> IterRule
    (   (kw "seq"     << no_backtrack "'seq' rule" SeqRule)
    <|> (kw "iterate" << no_backtrack "'iterate' rule" IterateRule)
    // <|> TurboCallRule
    // <|> TurboLocalStateRule
    ) s

and DerivedRule env (s : ParserInput<PARSER_STATE>) =
    let Term = Parser.term (false, env)
    let Rule = Rule env
    let CaseRule = R3 (Term) (pmany1 ((kw "case" << Term >> lit ":") ++ Rule)) ((poption (kw "otherwise" << Rule)) >> (kw "endswitch"))
                        |||>> fun reg (sign, _) (t, cases, otherwise) -> switch_to_cond_rule (Some reg) sign (t, cases, otherwise)
    let BasicDerivedRule   = (kw "switch" << no_backtrack "'switch' rule" CaseRule)
    let IterativeWhileRule = (kw "while" << no_backtrack "'while' rule"
                                (Term ++ (kw "do" << Rule)) )
                                |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule))
    let TurboDerivedRule =
        //  RecursiveWhileRule <|>   // what is this ?
            IterativeWhileRule
    (   BasicDerivedRule
    <|> TurboDerivedRule
    ) s

and Rule env (s : ParserInput<PARSER_STATE>) =
    let Term = Parser.term (false, env)
    let UpdateRule = (R3 (Term) (lit ":=") Term) |||>> fun reg (sign, _) (t1,_,t2) -> Parser.mkUpdateRule (Some reg) sign env (t1, t2)   // !!!! not exactly as in AsmetaL grammar
    (   BasicRule env
    <|> TurboRule env
    // <|> TurboReturnRule
    // <|> TermAsRule
    <|> DerivedRule env
    <|> UpdateRule
    ) s

// !!! temporary: global mutable variable to keep track of imported modules - to be replaced with 'modules' component of parser state
let imported_modules = ref (Map.empty : Map<string, ASM>)

let rec Asm env0 (s : ParserInput<EXTENDED_PARSER_STATE>) : ParserResult<ASM, EXTENDED_PARSER_STATE>  =
    let Term_in_env = Parser.term
    let Rule_in_env = Rule
    let StaticTerm       = Parser.term (true, env0)
    let UnrestrictedTerm = Parser.term (false, env0)
    let Rule = Rule env0
    //let (sign, state) = get_parser_state s
    let reduce_state (s : ParserInput<EXTENDED_PARSER_STATE>) : ParserInput<PARSER_STATE> * (RULES_DB * MACRO_DB) =
        let ((sign, state), (rules_db, macro_db)) = get_parser_state s
        in (chg_parser_state s (sign, state), (rules_db, macro_db))
    // let extend_state (s : ParserInput<PARSER_STATE>) (rules_db : RULES_DB) : ParserInput<EXTENDED_PARSER_STATE> =
    //     let (sign, state) = get_parser_state s
    //     in chg_parser_state s ((sign, state), rules_db)
    let isAsyncr_isModule_name (s : ParserInput<EXTENDED_PARSER_STATE>) =
            let (s, (rules_db, macro_db)) = reduce_state s
            (   ( (poption (kw "asyncr")) ++ (kw "asm" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, false, name) )
            <|> ( (poption (kw "asyncr")) ++ (kw "module" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, true, name) )
                ||>> fun (sign, state) _ -> ((sign, state), (rules_db, macro_db))  ) s
   
    let parse_imported_module mod_id (sign, state, rules_db) =
        if (!trace > 0) then fprintf stderr "importing module: '%s'\n" mod_id
        let saved_dir = System.IO.Directory.GetCurrentDirectory ()
        let filename = mod_id + ".asm"
        let full_path = System.IO.Path.GetFullPath filename
        if (!trace > 0) then fprintf stderr "  --> '%s'" full_path
        if not (Map.containsKey full_path !imported_modules) then
            if (!trace > 0) then fprintf stderr "\n"
            let new_dir = System.IO.Path.GetDirectoryName filename |> fun s -> if s = "" then "." else s
            let text =
                // move to directory where the imported file is located in order to correctly resolve
                // the relative paths of modules that may be imported in the imported module
                try System.IO.Directory.SetCurrentDirectory new_dir
                with _ -> raise (Error ("Asm", None, CannotImportModule (mod_id, Some new_dir, None)))
                try Common.readfile full_path
                with _ -> raise (Error ("Asm", None, CannotImportModule (mod_id, None, Some full_path)))
            let parse = Parser.make_parser (Asm TypeEnv.empty) (ParserCombinators.File (ref full_path)) ((sign, state), rules_db)
            let imported_module = fst (parse text)        // !!! checks missing (e.g. check that it is a 'module' and not an 'asm', etc.)
            // move to original directory (where the importing file is located)
            System.IO.Directory.SetCurrentDirectory saved_dir
            imported_modules := Map.add full_path imported_module !imported_modules
            imported_module
        else
            if (!trace > 0) then fprintf stderr "  [skipped - already loaded]\n"
            Map.find full_path !imported_modules

    let ImportClause s = 
        let (s, (rules_db, macro_db)) = reduce_state s
        let (sign, state) = get_parser_state s
        (   (   (kw "import" << MOD_ID (* or string, according to orig. grammar *))
                ++ (poption (lit "(" << (psep1_lit identifier ",") >> lit ")"))
            |>> fun (mod_name, opt_imported_names) -> (mod_name, parse_imported_module mod_name (sign, state, (rules_db, macro_db)), opt_imported_names)
            ||>> fun (sign, state) (_, ASM asm', _) ->
                    (   (sign, state),
                        (   rules_db_override rules_db asm'.definitions.rules,
                            macro_db_override macro_db asm'.definitions.macros    )   )
            ) ) s
    let ExportClause s =
            let (s, (rules_db, macro_db)) = reduce_state s
            (   (kw "export" << (psep1_lit identifier ",")) |>> fun names -> Some names
            <|> (kw "export" << (lit "*") |>> fun _ -> None )
                ||>> fun (sign, state) _ -> ((sign, state), (rules_db, macro_db)) ) s
                    // exports : string list option;     // None means all are exported ("export*")

    let Signature s =
        let (s, (rules_db, macro_db)) = reduce_state s
        (   (kw "signature" >> lit ":") <<
            (   (pmany Domain) ++
                (pmany Function)    )
                    |>> fun (domain_declarations, function_declarations) ->
                            let signature_with_domains   = List.fold (fun sign add_one_domain -> add_one_domain sign) empty_signature domain_declarations
                            let signature_with_functions = List.fold (fun sign add_one_function -> add_one_function sign) signature_with_domains function_declarations
                            signature_with_functions
                    ||>> fun (sign, state) _ -> ((sign, state), (rules_db, macro_db)) ) s

    let Header = R3
                    (pmany (ImportClause ||>> fun ((sign, state), rules_db) (_, ASM asm', _) ->
                                                (   (   signature_override sign asm'.signature,
                                                        state_override state asm'.definitions.state ),
                                                    rules_db    )))
                    (poption ExportClause |>> Option.defaultValue None)
                    Signature
                    |>> fun (imports, exports, sign) -> (imports, exports, sign)
    
    let parse_asm_with_header = isAsyncr_isModule_name ++ Header

    let typecheck_function_definition reg f param_list t sign =
        let sign_fct_types, (def_args_types, def_rhs_type) = fct_types f sign, (List.map snd param_list, get_type t)
        try match_fct_type f def_args_types sign_fct_types |> ignore
        with _ -> raise (Error ("Asm", Some reg, FunctionDefinitionTypeError(f, (def_args_types, def_rhs_type), sign_fct_types)))
    
    match parse_asm_with_header s with
    |   ParserFailure x -> ParserFailure x
    |   ParserSuccess (((asyncr, modul, asm_name), (imports, exports, sign')), s') ->
            //let sign = signature_override sign sign'
            let (sign, state), (rules_db, macro_db) : EXTENDED_PARSER_STATE = get_parser_state s'
            if !trace > 0 then fprintf stderr "parse_asm_with_header: |signature|=%d\n" (Map.count sign)

            let parameter_list = (opt_psep1 "(" ( ((ID_VARIABLE >> (kw "in")) ++ getDomainByID) ) "," ")")
            let extend_env reg env param_list = List.fold (fun env (v, t) -> add_var_distinct reg (v, t) env) env param_list

            let DomainDefinition : Parser<STATE -> STATE, PARSER_STATE> =
                ( ((kw "domain" << ID_DOMAIN) ++ (lit "=" << StaticTerm))
                    |||>> fun reg (sign, state) (d, t) ->
                        (fun state -> state_override_static state (Map.add d (fun _ -> Eval.eval_term t (state_with_signature state sign, Map.empty)) Map.empty)) )
            
            let FunctionDefinition =
                let p1 = (kw "function" << ID_FUNCTION) ++ parameter_list
                let p2 reg (static_term, env) param_list = (lit "=" << Term_in_env (static_term, extend_env reg env param_list))
                let p3 =
                        p1 >>== fun reg _ (f, param_list) ->
                        let is_static =
                            if not (is_function_name f sign)      then raise (Error ("Asm", Some reg, FunctionNameNotInSignature f))
                            else if fct_kind f sign = Constructor then raise (Error ("Asm", Some reg, ConstructorCannotBeRedefined f))
                            else fct_kind f sign = Static
                        p2 reg (is_static, env0) param_list >>= fun t ->
                        typecheck_function_definition reg f param_list t sign
                        preturn (f, param_list, t)
                // !!! to do: proper handling of function overloading
                p3 |||>> fun reg (_, _) (f, param_list, t) ->
                        if !trace > 0 then fprintf stderr "|signature| = %d - FunctionDefinition '%s'\n" (Map.count sign) f
                        let result =
                            if fct_kind f sign = Static then 
                                let parameters = List.map (fun (v, t) -> v) param_list
                                let fct = function (xs : VALUE list) -> Eval.eval_term t ((state_with_signature state sign), Map.ofList (List.zip parameters xs))
                                ( (fun (state : STATE) -> state_override_static state (Map.add f fct Map.empty)),
                                (fun (mdb : MACRO_DB) -> macro_db_override mdb (Map.add f (parameters, t) Map.empty)) )
                            else if fct_kind f sign = Derived then 
                                let parameters = List.map (fun (v, t) -> v) param_list
                                ( (fun state -> state),
                                (fun (mdb : MACRO_DB) -> macro_db_override mdb (Map.add f (parameters, t) Map.empty)) )
                            else raise (Error ("Asm", Some reg, FunctionNotDeclaredAsStaticOrDerived f))
                        result
                                                        
            let MacroDeclaration =
                let p1 = (poption (kw "macro") << kw "rule" << ID_RULE) ++ parameter_list
                let p2 reg env param_list = (lit "=" << Rule_in_env (extend_env reg env param_list))
                let p3 = (p1 >>== fun reg _ (f, param_list) -> p2 reg env0 param_list >>= fun t -> preturn (f, param_list, t))
                p3 |||>> fun reg _ (rname, param_list, r) ->
                        if List.length param_list > 0
                        then (rname, List.map snd param_list, (List.map fst param_list, r))
                        else (rname, [], ([], r))
            let TurboDeclaration = R4 (kw "turbo" << kw "rule" << ID_RULE) parameter_list (poption (kw "in" << getDomainByID)) (lit "=" << Rule)
                                        |>> fun (rname, _, _, _) -> failwith (sprintf "not implemented: turbo rule declaration ('%s')" rname)
            let RuleDeclaration = (MacroDeclaration <|> TurboDeclaration)
            let InvarConstraint = (kw "INVAR" << UnrestrictedTerm) |>> fun _ -> ()
            let JusticeConstraint = (kw "JUSTICE" << UnrestrictedTerm) |>> fun _ -> ()
            let CompassionConstraint = (kw "COMPASSION" << lit "(" << UnrestrictedTerm >> lit "," << UnrestrictedTerm >> lit ",") |>> fun _ -> ()
            let FairnessConstraint = JusticeConstraint <|> CompassionConstraint
            let Invariant = 
                let over_part = (kw "over" <<
                                psep1_lit (
                                        (ID_DOMAIN |>> fun _ -> ())
                                    <|> (ID_RULE |>> fun _ -> ())
                                    <|> (ID_FUNCTION << poption (lit "(" << poption getDomainByID << lit ")") |>> fun _ -> ())
                                ) ",")
                (  ( R3  (kw "invariant") over_part (lit ":" << UnrestrictedTerm)
                            |||>> fun reg _ (_, _, t) ->
                                    let inv_id = "_inv_"+(string !invariant_counter)
                                    invariant_counter := !invariant_counter + 1
                                    if get_type t = Boolean then [ (inv_id, t) ] else raise (Error ("Asm", Some reg, InvariantNotBoolean)) )
                <|> ( R3  (kw "invariant" << identifier) over_part (lit ":" << UnrestrictedTerm)
                            |||>> fun reg _ (name, _, t) ->
                                    if get_type t = Boolean then [ ("_inv_"+name, t) ] else raise (Error ("Asm", Some reg, InvariantNotBoolean)) ) )
            let CtlSpec = kw "CTLSPEC" << poption (ID_CTL >> lit ":") ++ UnrestrictedTerm   |>> fun _ -> ()
            let LtlSpec = kw "LTLSPEC" << poption (ID_LTL >> lit ":") ++ UnrestrictedTerm   |>> fun _ -> ()
            let TemporalProperty =
                ( CtlSpec <|> LtlSpec )
                    |>> fun _ -> fprintf stderr "warning: temporal property ignored (not implemented)"; []
            let Property = (Invariant <|> TemporalProperty)         // temporal properties are ignored for the time being
            let Body =
                    (   (kw "definitions" >> lit ":") <<
                        R6  (pmany (DomainDefinition : Parser<STATE -> STATE, PARSER_STATE>))
                            (pmany FunctionDefinition)
                            (pmany RuleDeclaration)
                            (pmany InvarConstraint)
                            (pmany FairnessConstraint)
                            (pmany Property |>> fun ps -> Map.ofList (List.concat ps)  (* !!! tbd: add check that a property name is not used more than once *) )   )
            let DomainInitialization = (kw "domain" << ID_DOMAIN) ++ (lit "=" << StaticTerm)
                                            |>> fun (id, _) -> failwith (sprintf "not implemented: initialization of domains ('%s')" id)
            let FunctionInitialization =
                let p1 = (kw "function" << ID_FUNCTION) ++ parameter_list
                let p2 reg env param_list = (lit "=" << Term_in_env (true, extend_env reg env param_list))    // term used for initialisation must be static
                let p3 = p1 >>== fun reg _ (f, param_list) ->
                                    p2 reg env0 param_list >>= fun t ->
                                    typecheck_function_definition reg f param_list t sign
                                    preturn (f, param_list, t)
                p3 |||>> fun reg _ (f, param_list, t) ->
                    if not (is_function_name f sign) then
                        raise (Error ("Asm", Some reg, FunctionNameNotInSignature f))
                    else
                        if fct_kind f sign = Controlled then 
                            let parameters = List.map (fun (v, t) -> v) param_list
                            let fct = function (xs : VALUE list) -> Eval.eval_term t ((state_with_signature state sign), Map.ofList (List.zip parameters xs))
                            fun (state : STATE, mdb : MACRO_DB) ->
                                  state_override_dynamic_initial state (Map.add f fct Map.empty, add_macro f (parameters, t) Map.empty),
                                  macro_db_override mdb (Map.add f (parameters, t) Map.empty)
                        else 
                            raise (Error ("Asm", Some reg, FunctionNotDeclaredAsControlled f))

            let AgentInitialization = (kw "agent" << ID_DOMAIN) ++ (lit ":" << (MacroCallRule env0))
                                            |>> fun (id, _) -> failwith (sprintf "not implemented: initialization of agent ('%s')" id)
            let Initialization = R4 (kw "init" << identifier >> lit ":")
                                    (pmany DomainInitialization)
                                    (pmany FunctionInitialization)
                                    (pmany AgentInitialization)
                                        |>> fun (initial_state_name, domain_init, function_init, agent_init) -> (initial_state_name, domain_init @ function_init @ agent_init)
            let parse_asm_rest s = 
                let parse =
                    ( R3
                        Body
                        (poption (kw "main" << MacroDeclaration))
                        // !!! only the default initial state is considered for the moment, the other are ignored
                        (poption (R3 (pmany Initialization) (kw "default" << Initialization) (pmany Initialization)))   
                    >>  skip_to_eos )
                        |>> fun (body, opt_main_rule, initial_states) ->
                                    body,
                                    opt_main_rule,
                                    match initial_states with
                                    |   None -> None
                                    |   Some (nondefault_init_1, default_init, nondefault_init_2) ->
                                            let default_init_name, _ = default_init
                                            let initial_states_map = Map.ofList (nondefault_init_1 @ [default_init] @ nondefault_init_2)
                                            Some (default_init_name, initial_states_map)
                                    //match default_init with None -> [] | Some default_init -> default_init  )
                (   let (s, (rules_db, macro_db)) = reduce_state s
                    (parse ||>> fun (sign, state) _ -> ((sign, state), (rules_db, macro_db)) ) s )

            match parse_asm_rest s' with
            |   ParserFailure x -> ParserFailure x
            |   ParserSuccess (
                    (   (   domain_definitions,
                            function_definitions,
                            rule_declarations,
                            _,
                            _,
                            properties  ),
                        opt_main_rule_decl,
                        initial_states
                    ), s'')
                    ->
                    let state' : STATE = List.fold (fun state f -> f state) state domain_definitions
                    let rule_declarations = rule_declarations @ (Option.fold (fun _ x -> [x]) [] opt_main_rule_decl)
                    let rdb' : RULES_DB = List.fold (fun rdb (rname, r_args_types, r) -> Map.add rname r rdb) empty_rules_db rule_declarations
                    let sign_final = List.fold (fun sign (rname, r_args_types, _) -> add_rule_name rname r_args_types sign) sign rule_declarations
                    let (state'', mdb') : STATE * MACRO_DB =
                        List.fold
                            (fun (state, mdb) (fct_def, macro_fct_def) -> (fct_def state, macro_fct_def mdb))
                            (state', empty_macro_db)
                            (function_definitions (*@ initial_states*) )
                    let initial_states' : (string * Map<string, STATE * MACRO_DB>) option =
                        let extend_state_with_fct_def (state : STATE, mdb : MACRO_DB) add_def : STATE * MACRO_DB = add_def (state, mdb)
                        match initial_states with
                        |   None -> None
                        |   Some (default_init_name, initial_states_map) ->
                                let initial_states_map' =
                                    Map.map
                                        (fun state_name transf_list -> List.fold extend_state_with_fct_def (state'', mdb') transf_list)
                                        initial_states_map
                                Some (default_init_name, initial_states_map')
                    let initial_states'' : (string * Map<string, STATE * MACRO_DB>) option =
                        // initial_states' extended with the additional constructors added to abstract (enum) types
                        Option.map (fun (default_init_name, initial_state_map) ->
                            default_init_name,
                            Map.map (fun _ (state, mdb) -> extend_with_carrier_sets (sign, state_override state state''), mdb) initial_state_map) initial_states'
                    if !trace > 0 then fprintf stderr "static function definitions found for: %s\n" (Map.keys state''._static |> String.concat ", ")
                    if !trace > 0 then fprintf stderr "dynamic function definitions found for: %s\n" (Map.keys state''._dynamic |> String.concat ", ")
                    if !trace > 0 then fprintf stderr "dynamic function initializations found for: %s\n" (Map.keys (fst state''._dynamic_initial) |> String.concat ", ")
                    let result = ASM {
                        name      = asm_name;
                        is_module = modul;
                        is_asyncr = asyncr;
                        imports   = imports;
                        exports   = exports;
                        signature = sign_final;
                        invariants = properties;        // properties are only invariants for the moment (temporal properties are ignored)
                        definitions = {
                            state  = extend_with_carrier_sets (sign_final, state_override state state'');   // !!! Agent, Reserve added twice ?
                            rules  = rules_db_override rules_db rdb';
                            macros = macro_db_override macro_db mdb';
                        };
                        initial_states = initial_states'';
                    }
                    ParserSuccess ( result, s'')

let extract_definitions_from_asmeta (asm : ASM) : SIGNATURE * STATE * RULES_DB * MACRO_DB * Map<string, TYPED_TERM> * (string * Map<string, STATE * MACRO_DB>) option =
    match asm with
    |   ASM (asm_content) ->
            let sign  = asm_content.signature
            let state = state_with_signature asm_content.definitions.state sign
            let rdb   = asm_content.definitions.rules
            let mdb   = asm_content.definitions.macros
            let invariants = asm_content.invariants
            let initial_states = asm_content.initial_states
            (sign, state, rdb, mdb, invariants, initial_states)

let parse_definitions initial_location ((sign, S), (rules_db, macro_db)) s =
    imported_modules := Map.empty
    let asm as ASM asm' = fst (Parser.make_parser (Asm TypeEnv.empty) initial_location ((sign, S), (rules_db, macro_db)) s)
    if (!trace > 1) then fprintf stderr "---\n%s\n---\n" (asm'.signature |> signature_to_string)
    asm

