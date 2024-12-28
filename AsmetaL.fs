module AsmetaL

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let trace = ref 0

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
    definitions : ASM_Definitions;
}

and ASM = ASM of ASM_Content   // "asm" or "module" content

//--------------------------------------------------------------------

let asm_content (asyncr_module_name as (asyncr : bool, modul : bool, name : string))
                (imports : (string * ASM * string list option) list)
                (exports : string list option)
                (signature : SIGNATURE)
                (definitions : ASM_Definitions) : ASM_Content =
    {
        name = name;
        is_module = modul;
        is_asyncr = asyncr;
        imports = imports;
        exports = exports;
        signature = signature;
        definitions = {
            state = definitions.state;
            rules     = definitions.rules;
            macros    = definitions.macros;
        };
    }

let mkAsm (asyncr : bool, modul : bool, name : string) (imports : (string * ASM * string list option) list) (exports : string list option) (signature : SIGNATURE) (definitions : ASM_Definitions) : ASM =
    ASM (asm_content (asyncr, modul, name) imports exports signature definitions)

//--------------------------------------------------------------------

type PARSER_STATE = Parser.PARSER_STATE

type EXTENDED_PARSER_STATE = PARSER_STATE * (RULES_DB * MACRO_DB)

//--------------------------------------------------------------------

let get_signature = Parser.get_signature
let get_state = Parser.get_state
let get_signature_from_input = Parser.get_signature_from_input
let get_state_from_input = Parser.get_state_from_input

//--------------------------------------------------------------------

let pcharf = Parser.pcharf
let one_line_comment = Parser.one_line_comment
let ML_multiline_comment = Parser.ML_multiline_comment
let C_multiline_comment = Parser.C_multiline_comment
let comment = Parser.comment
let ws_or_comment = Parser.ws_or_comment
let skip_to_eos = Parser.skip_to_eos
let lit = Parser.lit
let int = Parser.int

let kw kw_name =
    (   (ws_or_comment << (pmany1 pletter)) )
            >>= fun s ->
                    let s = implode s 
                    if s = kw_name then preturn s
                    else pfail_msg "keyword" ($"keyword '{kw_name}' expected, '{s}' found")

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


let ID_DOMAIN = identifier   //!!!! not exactly
let ID_ENUM = identifier      //!!!! not exactly
let ID_FUNCTION = identifier  //!!!! not exactly

let ID_VARIABLE = ws_or_comment << (pchar '$' ++ (pletter ++ (pmany palphanum_))) |>> fun (c1, (c2, s)) -> implode (c1 :: c2 :: s)
let ID_RULE = identifier  //!!!! not exactly
let ID_CTL = identifier       //!!!! not exactly
let ID_LTL = identifier

let EnumElement = ID_ENUM


let add_basic_domain s sign =
    if s <> "Boolean" && s <> "Integer" && s <> "String" && s <> "Undef" && s <> "Rule"
        && s <> "Complex" && s <> "Real" && s <> "Natural" && s <> "Char"   // !!! last four are not yet implemented
    then failwith (sprintf "not implemented: basic type domain '%s'" s)
    else sign   // nothing to add to the signature: basic domains are predefined, i.e. already in the signature

let rec getDomainByID (s : ParserInput<PARSER_STATE>) : ParserResult<TYPE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   (   StructuredTD
            <|> (ID_DOMAIN |>> fun s -> construct_type sign (s, []))) ) s
    and StructuredTD  (s : ParserInput<PARSER_STATE>) : ParserResult<TYPE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   let ProductDomain  = kw "Prod"     ++ (opt_psep2 "(" getDomainByID "," ")") |>> construct_type sign
            let SequenceDomain = kw "Seq"      ++ (lit "(" << (getDomainByID |>> fun t->[t]) >> lit ")") |>> construct_type sign
            let PowersetDomain = kw "Powerset" ++ (lit "(" << (getDomainByID |>> fun t->[t]) >> lit ")") |>> construct_type sign
            let BagDomain      = kw "Bag"      ++ (lit "(" << (getDomainByID |>> fun t->[t]) >> lit ")") |>> construct_type sign
            let MapDomain      = kw "Map"      ++ (lit "(" << (R3 getDomainByID (lit ",") getDomainByID |>> fun (t1,_,t2) -> [t1;t2]) >> lit ")")  |>> construct_type sign
            ProductDomain <|> SequenceDomain <|> PowersetDomain <|> BagDomain <|> MapDomain ) s
    and ConcreteDomain (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   (kw "domain" << ID_DOMAIN) ++ (kw "subsetof" << getDomainByID)          
                |>> fun (tyname, T) ->
                        // !!! for the moment, simply map to main type
                        add_type_name tyname (0, SubsetType, Some (fun _ -> T)) ) s
    and TypeDomain (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   let AnyDomain = kw "anydomain" << ID_DOMAIN
                                |>> fun tyname -> add_type_name tyname (0, AnyType, Some (fun _ -> TypeParam tyname))
            let EnumTD = (kw "enum" << kw "domain" << ID_DOMAIN) ++ (lit "=" << lit "{" << psep1 EnumElement (lit "," <|> lit "|") >> lit "}")
                                |>> fun (tyname, cons_names) ->
                                    fun sign ->
                                    (   let sign' = add_type_name tyname (0, EnumType, Some (fun _ -> TypeCons (tyname, []))) sign
                                        List.fold (fun sign f -> add_function_name f (Constructor, NonInfix, ([], TypeCons (tyname, []))) sign) sign' cons_names)
            let AbstractTD = (popt_bool (kw "dynamic") >> kw "abstract" >> kw "domain") ++ ID_DOMAIN     // !!! what about 'dynamic'?
                                |>> fun (is_dynamic, tyname) ->
                                    if is_dynamic
                                    then failwith (sprintf "not implemented: dynamic abstract domain ('%s')" tyname)
                                    else add_type_name tyname (0, EnumType, Some (fun _ -> TypeCons (tyname, [])))
            let BasicTD = (kw "basic" << kw "domain" << ID_DOMAIN) |>> fun tyname -> add_basic_domain tyname
            AnyDomain <|> EnumTD <|> AbstractTD <|> BasicTD ) s

let Domain (s : ParserInput<PARSER_STATE>) =
    ((ConcreteDomain <|> TypeDomain) ||>> fun (sign, state) update_sign_fct -> (update_sign_fct sign, state)) s

let Term s =
    if !trace > 0 then fprintf stderr "AsmetaL.Term\n"
    let DomainTerm s =
        if !trace > 0 then fprintf stderr "AsmetaL.DomainTerm\n"
        try ( getDomainByID s )
        with _ -> ParserFailure (combine_failures (Set.singleton (get_pos s, ($"type name expected, '{s}' found")), get_failures s))
    let regularTerm s =
        if !trace > 0 then fprintf stderr "Parser.term\n"
        Parser.term s
    (   ( DomainTerm  |>> fun tyname -> AST.DomainTerm tyname )
    <|> ( regularTerm ) ) s

let add_function_name f (kind, infix, (tys, ty)) sign =
    //!!! little hack to avoid overwriting of predefined background functions by Asmeta StandardLibrary.asm
    //!!! (which would destroy infix status of operators)
    if not (Map.containsKey f Background.signature)
    then add_function_name f (kind, infix, (tys, ty)) sign
    else fprintf stderr "warning: ignoring declaration of function '%s' already present in background signature\n" f; sign

let Function (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
    let (sign, state) = get_parser_state s
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

let forall_rule_with_multiple_bindings v_tset_list t_filter R =
    let rec mk_forall_rule = function
    |   [] -> failwith "forall_rule_with_multiple_bindings: empty list of bindings"
    |   [(v, t)] -> ForallRule (v, t, t_filter, R)
    |   (v, t) :: v_t_list -> ForallRule (v, t, AppTerm (BoolConst true, []), mk_forall_rule v_t_list)
    in mk_forall_rule v_tset_list

let switch_to_cond_rule (t, cases : (TERM * RULE) list, otherwise : RULE option) =
    Parser.switch_to_cond_rule (t, cases, match otherwise with Some R -> R | None -> skipRule)

// ---------------------------------

let rec BasicRule (s : ParserInput<PARSER_STATE>) =
    let BlockRule       = kw "par" << pmany1 Rule >> kw "endpar" |>> ParRule
    let ConditionalRule = R3 (kw "if" << Term) (kw "then" << Rule) (poption (kw "else" << Rule) |>> Option.defaultValue skipRule) >> kw "endif" |>> CondRule
    let VariableTerm    = ID_VARIABLE
    let LetRule    = R2 (kw "let" << lit "(" << (psep1_lit ((VariableTerm >> lit "=") ++ Term) ",") >> lit ")")
                         (kw "in" << Rule) >> (kw "endlet")
                        |>> ( function
                                | ([(v, t)], R) -> LetRule (v, t, R)
                                | (v_t_list, R) -> let_rule_with_multiple_bindings v_t_list R )
    let ChooseRule = R4 (kw "choose" << psep1_lit ((VariableTerm >> kw "in") ++ Term) ",")
                        (kw "with" << Term) (kw "do" << Rule) (poption (kw "ifnone" << Rule))
                            |>> fun _ -> failwith "not implemented: choose rule"
    let ForallRule = R3 (kw "forall" << (psep1_lit ((VariableTerm >> kw "in") ++ Term) ","))
                        (kw "with" << Term) (kw "do" << Rule)
                            |>> fun (v_tset_list, t_filter, R) -> forall_rule_with_multiple_bindings v_tset_list t_filter R
    (   kw "skip" |>> fun _ -> skipRule
    <|> BlockRule
    <|> ConditionalRule
    <|> LetRule
    <|> ChooseRule
    <|> ForallRule
    <|> MacroCallRule
    // <|> ExtendRule
    ) s

and MacroCallRule = ((ID_RULE >> lit "[") ++ (psep0 Term (lit ",") >> lit "]")) |>> MacroRuleCall

and TurboRule (s : ParserInput<PARSER_STATE>) =
    //let sign = get_signature_from_input s
    //let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
    let SeqRule = kw "seq" << pmany1 Rule >> kw "endseq" |>> AST.SeqRule
    let IterateRule = kw "iterate" << Rule >> kw "enditerate" |>> IterRule
    (   SeqRule
    <|> IterateRule
    // <|> TurboCallRule
    // <|> TurboLocalStateRule
    ) s

and DerivedRule (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
    let CaseRule = R3 (kw "switch" << Term) (pmany1 ((kw "case" << Term >> lit ":") ++ Rule)) ((poption (kw "otherwise" << Rule)) >> (kw "endswitch")) |>> switch_to_cond_rule
    let BasicDerivedRule = CaseRule
    let IterativeWhileRule = (kw "while" << Term) ++ (kw "do" << Rule)
                                |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule))
    let TurboDerivedRule =
            // RecursiveWhileRule <|>   // !!! ?
            IterativeWhileRule
    (   BasicDerivedRule
    <|> TurboDerivedRule
    ) s


and Rule (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
    let UpdateRule = (R3 (Term) (lit ":=") Term) |>> fun (t1,_,t2) -> Parser.mkUpdateRule sign (t1, t2)   // !!!! not exactly as in AsmetaL grammar
    (   BasicRule
    <|> TurboRule
    // <|> TurboReturnRule
    // <|> TermAsRule
    <|> DerivedRule
    <|> UpdateRule          // update rule is last, because for the previous ones parsing failure is easy to detect
    ) s


// !!! temporary: global mutable variable to keep track of imported modules - to be replaced with 'modules' component of parser state
let imported_modules = ref (Map.empty : Map<string, ASM>)

let rec Asm (s : ParserInput<EXTENDED_PARSER_STATE>) : ParserResult<ASM, EXTENDED_PARSER_STATE>  =
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
            // move to directory where the imported file is located
            // in order to correctly resolve the relative paths of modules
            // that may be imported in the imported module
            System.IO.Directory.SetCurrentDirectory new_dir
            let text = Common.readfile full_path
            let parse = Parser.make_parser Asm (ParserCombinators.File (ref full_path)) ((sign, state), rules_db)
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

    match parse_asm_with_header s with
    |   ParserFailure x -> ParserFailure x
    |   ParserSuccess (((asyncr, modul, asm_name), (imports, exports, sign')), s') ->
            //let sign = signature_override sign sign'
            let ((sign, state), (rules_db, macro_db)) : EXTENDED_PARSER_STATE = get_parser_state s'
            if !trace > 0 then fprintf stderr "parse_asm_with_header: |signature|=%d\n" (Map.count sign)

            let Term s = Term (chg_parser_state s (sign, state))    // !!! temporary
            let parameter_list = opt_psep1 "(" ((ID_VARIABLE >> (kw "in")) ++ getDomainByID) "," ")"
            let DomainDefinition = (kw "domain" << ID_DOMAIN) ++ (lit "=" << Term)
            
            let FunctionDefinition =
                R3 (kw "function" << ID_FUNCTION) parameter_list (lit "=" << Term)
                |||>> fun reg _ (f, param_list, t) ->
                    //!!!! no type checking
                    if !trace > 0 then fprintf stderr "|signature| = %d - FunctionDefinition '%s'\n" (Map.count sign) f
                    if not (is_function_name f sign) then
                        failwith (sprintf "error in function definition: function '%s' is not declared in the signature" f)
                    else if fct_kind f sign = Constructor then
                        failwith (sprintf "error in function definition: function '%s' is a constructor, cannot be redefined" f)
                    else 
                        let _ = Parser.typecheck_term (Some reg) t (sign, Map.ofSeq param_list)
                        //!!! to do: proper handling of function overloading
                        // !!! types of parameters are currently ignored
                        let result =
                            if fct_kind f sign = Static then 
                                let parameters = List.map (fun (v, t) -> v  (* !!! the type is not checked and discarded for the moment *) ) param_list
                                let fct = function (xs : VALUE list) -> Eval.eval_term t ((* !!! should also use prev. def. functions *) (state_with_signature state sign), Map.ofList (List.zip parameters xs))
                                //failwith (sprintf "not implemented: definition of function ('%s') with arity > 0" f)
                                ( (fun (state : STATE) -> state_override_static state (Map.add f fct Map.empty)),
                                (fun (mdb : MACRO_DB) -> macro_db_override mdb (Map.add f (parameters, t) Map.empty)) )
                            else if fct_kind f sign = Derived then 
                                let parameters = List.map (fun (v, t) -> v  (* !!! the type is not checked and discarded for the moment *) ) param_list
                                //failwith (sprintf "not implemented: definition of function ('%s') with arity > 0" f)
                                ( (fun state -> state),
                                (fun (mdb : MACRO_DB) -> macro_db_override mdb (Map.add f (parameters, t) Map.empty)) )
                            else failwith (sprintf "error in function definition: function '%s' is not declared as static or derived in the signature" f)
                        result
                                                        
            let MacroDeclaration =
                R3 (poption (kw "macro") << kw "rule" << ID_RULE) parameter_list (lit "=" << Rule)
                |>> fun (rname, param_list, r) ->
                        if List.length param_list > 0
                        then (rname, (List.map fst param_list, r))    // !!! types are currently ignored
                        else (rname, ([], r))
            let TurboDeclaration = R4 (kw "turbo" << kw "rule" << ID_RULE) parameter_list (poption (kw "in" << getDomainByID)) (lit "=" << Rule)
                                        |>> fun (rname, _, _, _) -> failwith (sprintf "not implemented: turbo rule declaration ('%s')" rname)
            let RuleDeclaration = (MacroDeclaration <|> TurboDeclaration)
            let InvarConstraint = (kw "INVAR" << Term) |>> fun _ -> ()
            let JusticeConstraint = (kw "JUSTICE" << Term) |>> fun _ -> ()
            let CompassionConstraint = (kw "COMPASSION" << lit "(" << Term >> lit "," << Term >> lit ",") |>> fun _ -> ()
            let FairnessConstraint = JusticeConstraint <|> CompassionConstraint
            let Invariant = 
                let over_part = (kw "over" <<
                                psep1_lit (
                                        (ID_DOMAIN |>> fun _ -> ())
                                    <|> (ID_RULE |>> fun _ -> ())
                                    <|> (ID_FUNCTION << poption (lit "(" << poption getDomainByID << lit ")") |>> fun _ -> ())
                                ) ",")
                (   ( R3  (kw "invariant")                       over_part (lit ":" << Term) |>> fun _ -> () )
                <|> ( R3  (kw "invariant" << poption identifier) over_part (lit ":" << Term) |>> fun _ -> () )    )
            let CtlSpec = kw "CTLSPEC" << poption (ID_CTL >> lit ":") ++ Term   |>> fun _ -> ()
            let LtlSpec = kw "LTLSPEC" << poption (ID_LTL >> lit ":") ++ Term   |>> fun _ -> ()
            let TemporalProperty = CtlSpec <|> LtlSpec
            let Property = (Invariant <|> TemporalProperty)
            let Body =
                    (   (kw "definitions" >> lit ":") <<
                        R6  (pmany DomainDefinition)
                            (pmany FunctionDefinition)
                            (pmany RuleDeclaration)
                            (pmany InvarConstraint)
                            (pmany FairnessConstraint)
                            (pmany Property)       )
            let DomainInitialization = (kw "domain" << ID_DOMAIN) ++ (lit "=" << Term)
                                            |>> fun (id, _) -> failwith (sprintf "not implemented: initialization of domains ('%s')" id)
            let FunctionInitialization =
                R3 (kw "function" << ID_FUNCTION) parameter_list (lit "=" << Term)
                |||>> fun reg _ (f, param_list, t) ->
                    //!!!! no type checking
                    if not (is_function_name f sign) then
                        failwith (sprintf "error in function definition: function '%s' is not declared in the signature" f)
                    else
                        let _ = Parser.typecheck_term (Some reg) t (sign, Map.ofSeq param_list)
                        if fct_kind f sign = Controlled then 
                            let parameters = List.map (fun (v, t) -> v  (* !!! the type is not checked and discarded for the moment *) ) param_list
                            let fct = function (xs : VALUE list) -> Eval.eval_term t ((* !!! should also use prev. def. functions *) (state_with_signature state sign), Map.ofList (List.zip parameters xs))
                            //failwith (sprintf "not implemented: definition of function ('%s') with arity > 0" f)
                            ((fun (state : STATE) -> state_override_dynamic_initial state (Map.add f fct Map.empty)), (fun (mdb : MACRO_DB) -> mdb))
                        else failwith (sprintf "error in function initialization: function '%s' is not declared as controlled in the signature" f)

            let AgentInitialization = (kw "agent" << ID_DOMAIN) ++ (lit ":" << MacroCallRule)
                                            |>> fun (id, _) -> failwith (sprintf "not implemented: initialization of agent ('%s')" id)
            let Initialization = R4 (kw "init" << identifier >> lit ":")
                                    (pmany DomainInitialization)
                                    (pmany FunctionInitialization)
                                    (pmany AgentInitialization)
                                        |>> fun (_, domain_init, function_init, agent_init) -> domain_init @ function_init @ agent_init
            let parse_asm_rest s = 
                let parse =
                    ( R3
                        Body
                        (poption (kw "main" << MacroDeclaration))
                        // !!! only the default initial state is considered for the moment, the other are ignored
                        (poption ((pmany Initialization) << (kw "default" << Initialization) >> (pmany Initialization)))   
                    >>  skip_to_eos )
                        |>> fun (body, opt_main_rule, default_init) ->
                                (   body,
                                    opt_main_rule,
                                    match default_init with None -> [] | Some default_init -> default_init  )
                (   let (s, (rules_db, macro_db)) = reduce_state s
                    (parse ||>> fun (sign, state) _ -> ((sign, state), (rules_db, macro_db)) ) s )

            match parse_asm_rest s' with
            |   ParserFailure x -> ParserFailure x
            |   ParserSuccess (((_, function_definitions, rule_declarations, _, _, _), opt_main_rule_decl, default_init), s'') ->
                    let rule_declarations = rule_declarations @ (Option.fold (fun _ x -> [x]) [] opt_main_rule_decl)
                    let rdb' : RULES_DB = List.fold (fun rdb (rname, r) -> Map.add rname r rdb) empty_rules_db rule_declarations
                    let (state', mdb') : STATE * MACRO_DB =
                        List.fold
                            (fun (state, mdb) (fct_def, macro_fct_def) -> (fct_def state, macro_fct_def mdb))
                            (empty_state, empty_macro_db)
                            (function_definitions @ default_init)
                    if !trace > 0 then fprintf stderr "static function definitions found for: %s\n" (Map.keys state'._static |> String.concat ", ")
                    if !trace > 0 then fprintf stderr "dynamic function definitions found for: %s\n" (Map.keys state'._dynamic |> String.concat ", ")
                    if !trace > 0 then fprintf stderr "dynamic function initializations found for: %s\n" (Map.keys state'._dynamic_initial |> String.concat ", ")
                    let result = ASM {
                        name      = asm_name;
                        is_module = modul;
                        is_asyncr = asyncr;
                        imports   = imports;
                        exports   = exports;
                        signature = sign;
                        definitions = {
                            state  = extend_with_carrier_sets (sign, state_override state state');   // !!! Agent, Reserve added twice ?
                            rules  = rules_db_override rules_db rdb';
                            macros = macro_db_override macro_db mdb';
                        };
                    }
                    ParserSuccess ( result, s'')

let extract_definitions_from_asmeta (asm : ASM) : SIGNATURE * STATE * RULES_DB * MACRO_DB =
    match asm with
    |   ASM (asm_content) ->
            let sign  = asm_content.signature
            let state = state_with_signature asm_content.definitions.state sign
            let rdb   = asm_content.definitions.rules
            let mdb   = asm_content.definitions.macros
            (sign, state, rdb, mdb)


let parse_definitions initial_location ((sign, S), (rules_db, macro_db)) s =
    imported_modules := Map.empty
    let asm as ASM asm' = fst (Parser.make_parser Asm initial_location ((sign, S), (rules_db, macro_db)) s)
    if (!trace > 1) then fprintf stderr "---\n%s\n---\n" (asm'.signature |> signature_to_string)
    asm

