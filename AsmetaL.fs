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
    functions : STATE;
    rules : RULES_DB;
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
            functions = definitions.functions;
            rules     = definitions.rules;
        };
    }

let mkAsm (asyncr : bool, modul : bool, name : string) (imports : (string * ASM * string list option) list) (exports : string list option) (signature : SIGNATURE) (definitions : ASM_Definitions) : ASM =
    ASM (asm_content (asyncr, modul, name) imports exports signature definitions)

//--------------------------------------------------------------------
(*
type PARSER_STATE = SIGNATURE * STATE * RULES_DB

let get_signature ((sign : SIGNATURE, state : STATE, rules_db : RULES_DB) : PARSER_STATE) = sign
let get_state ((sign : SIGNATURE, state : STATE, rules_db : RULES_DB) : PARSER_STATE) = state
let get_rules_db ((sign : SIGNATURE, state : STATE, rules_db : RULES_DB) : PARSER_STATE) = state

let get_signature_from_input (s : ParserInput<PARSER_STATE>) = get_parser_state s |> get_signature
let get_state_from_input (s : ParserInput<PARSER_STATE>)     = get_parser_state s |> get_state
let get_rules_db_from_input (s : ParserInput<PARSER_STATE>)  = get_parser_state s |> get_rules_db
*)

type PARSER_STATE = Parser.PARSER_STATE

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

let Term = Parser.term


let popt_bool p =
    poption p |>> function None -> false | Some _ -> true

let psep0 p sep =
    poption (p ++ pmany (sep << p)) |>> function Some (x, xs) -> x::xs | None -> []

let psep1 p sep =
    p ++ pmany (sep << p) |>> fun (x, xs) -> x::xs

let psep1_lit p sep =
    p ++ pmany (lit sep << p) |>> fun (x, xs) -> x::xs

let psep2_lit p sep =
    p ++ pmany1 (lit sep << p) |>> fun (x, xs) -> x::xs

let opt_psep1 encl_begin p sep encl_end =
    poption (lit encl_begin << psep1_lit p sep >> lit encl_end) |>> function None -> [] | Some xs -> xs

let opt_psep2 encl_begin p sep encl_end =
    poption (lit encl_begin << psep2_lit p sep >> lit encl_end) |>> function None -> [] | Some xs -> xs



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
let ID_VARIABLE = pchar '$' ++ identifier |>> fun (c, s) -> c.ToString() + s
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
            ProductDomain <|> SequenceDomain <|> PowersetDomain <|> BagDomain<|> MapDomain ) s
    and ConcreteDomain (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   (kw "domain" << ID_DOMAIN) ++ (kw "subsetof" << getDomainByID)          
                |>> fun (tyname, T) ->
                        // !!! for the moment, simply map to main type
                        add_type_name tyname (0, Some (fun _ -> T)) ) s
    and TypeDomain (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
        let sign = get_signature_from_input s
        (   let AnyDomain = kw "anydomain" << ID_DOMAIN
                                |>> fun tyname -> add_type_name tyname (0, Some (fun _ -> TypeParam tyname))
            let EnumTD = (kw "enum" << kw "domain" << ID_DOMAIN) ++ (lit "=" << lit "{" << psep1 EnumElement (lit "," <|> lit "|") >> lit "}")
                                |>> fun _ -> failwith "not implemented: enum type domain"
            let AbstractTD = (popt_bool (kw "dynamic") >> kw "abstract" >> kw "domain") ++ ID_DOMAIN     // !!! what about 'dynamic'?
                                |>> fun (is_dynamic, tyname) -> add_type_name tyname (0, Some (fun _ -> TypeCons (tyname, [])))
                                //|>> fun (is_dynamic, s) -> TypeCons (s, []) 
            let BasicTD = (kw "basic" << kw "domain" << ID_DOMAIN) |>> fun tyname -> add_basic_domain tyname
            AnyDomain <|> EnumTD <|> AbstractTD <|> BasicTD
            (* <|> StructuredTD  (* not really a declaration *) *) ) s

let Domain (s : ParserInput<PARSER_STATE>) =
    ((ConcreteDomain <|> TypeDomain) ||>> fun (sign, state) update_sign_fct -> (update_sign_fct sign, state)) s

let Function (s : ParserInput<PARSER_STATE>) : ParserResult<SIGNATURE -> SIGNATURE, PARSER_STATE> =
    // any function f : Prod(T1,...,Tn) -> T is converted into an n-ary function f : T1,...,Tn -> T  [n >= 0]
    let to_fct_type (tys : TYPE, ty_opt : TYPE option) =
        match (tys, ty_opt) with
        |   (ty, None)          -> ([], ty)
        |   (Prod tys, Some ty) -> (tys, ty)
        |   (ty, Some ty')      -> ([ty], ty')
    let StaticFunction     = R3 (kw "static"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> add_function_name f (Static, NonInfix, to_fct_type(tys, opt_ty))
    let DerivedFunction    = R3 (kw "derived" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: derived function"
    let OutFunction        = R3 (poption (kw "dynamic") << kw "out"        << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: out function"
    let MonitoredFunction  = R3 (poption (kw "dynamic") << kw "monitored"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: monitored function"
    let SharedFunction     = R3 (poption (kw "dynamic") << kw "shared"     << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: shared function"
    let ControlledFunction = R3 (poption (kw "dynamic") << kw "controlled" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> add_function_name f (Controlled, NonInfix, to_fct_type(tys, opt_ty))
    let LocalFunction      = R3 (poption (kw "dynamic") << kw "local"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: local function"
    let DynamicFunction    = OutFunction <|> MonitoredFunction  <|> SharedFunction <|> ControlledFunction <|> LocalFunction
    let BasicFunction      = StaticFunction <|> DynamicFunction
    ((BasicFunction <|> DerivedFunction)  ||>> fun (sign, state) update_sign_fct -> (update_sign_fct sign, state)) s



let rec BasicRule (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    if (!trace > 0) then fprintf stderr "BasicRule: " // "BasicRule: %s" (ParserInput.to_string s)
    let BlockRule = kw "par" << pmany1 Rule >> kw "endpar" |>> ParRule
    let ConditionalRule = R3 (kw "if" << Term) (kw "then" << Rule) (poption (kw "else" << Rule) |>> Option.defaultValue skipRule) >> kw "endif" |>> CondRule
    let VariableTerm = ID_VARIABLE
    let LetRule    = R2 (kw "let" << lit "(" << (psep1_lit (VariableTerm >> lit "=" << Term) ",") >> lit ")")
                        (kw "in" << Rule)
                        |>> fun _ -> failwith "not implemented: let rule"
    let ChooseRule = R4 (kw "choose" << psep1_lit ((ID_VARIABLE >> kw "in") ++ Term) ",") (kw "with" << Term) (kw "do" << Rule) (poption (kw "ifnone" << Rule))
                        |>> fun _ -> failwith "not implemented: choose rule"
    let ForallRule = R3 (kw "forall" << psep1_lit ((ID_VARIABLE >> kw "in") ++ Term) ",") (kw "with" << Term) (kw "do" << Rule)
                        |>> fun _ -> failwith "not implemented: forall rule"
    
    // /* AsmetaL grammar */    LetRule 	::= 	<LET> "(" VariableTerm "=" Term ( "," VariableTerm "=" Term )* ")" <IN> Rule <ENDLET> 
    (   kw "skip" |>> fun _ -> skipRule
    <|> BlockRule
    <|> ConditionalRule
    <|> LetRule
    <|> ChooseRule
    <|> ForallRule
    <|> MacroCallRule
    // <|> LetRule
    // <|> ExtendRule
    ) s

and MacroCallRule (s : ParserInput<PARSER_STATE>) =
    //let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
    (   ((ID_RULE >> lit "[") ++ (psep0 Term (lit ",") >> lit "]"))
            |>> fun _ -> failwith "not implemented: macro call rule" ) s

and TurboRule (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
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
    let IterativeWhileRule = (kw "while" << Term) ++ (kw "do" << Rule)
                                |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule))
    let TurboDerivedRule =
            // RecursiveWhileRule <|>   // !!! ?
            IterativeWhileRule
    (   
//      BasicDerivedRule <|>
        TurboDerivedRule
    ) s


and Rule (s : ParserInput<PARSER_STATE>) =
    let sign = get_signature_from_input s
    let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
    let UpdateRule = (R3 (Term) (lit ":=") Term) |>> fun (t1,_,t2) -> Parser.mkUpdateRule sign (t1, t2)   // !!!! not exactly as in AsmetaL grammar
    (   UpdateRule
    <|> BasicRule
    <|> TurboRule
    // <|> TurboReturnRule
    // <|> TermAsRule
    <|> DerivedRule
    ) s


// !!! temporary: global mutable variable to keep track of imported modules - to be replaced with 'modules' component of parser state
let imported_modules = ref (Map.empty : Map<string, ASM>)

let rec Asm (s : ParserInput<Parser.PARSER_STATE>) : ParserResult<ASM, Parser.PARSER_STATE>  =
    //let (sign, state) = get_parser_state s
    let isAsyncr_isModule_name =
            (   ( (poption (kw "asyncr")) ++ (kw "asm" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, false, name) )
            <|> ( (poption (kw "asyncr")) ++ (kw "module" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, true, name) ) )
    let parse_imported_module mod_id (sign, state) =
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
            let parse = Parser.make_parser Asm (sign, state)
            let imported_module = fst (parse text)        // !!! checks missing (e.g. check that it is a 'module' and not an 'asm', etc.)
            // move to original directory (where the importing file is located)
            System.IO.Directory.SetCurrentDirectory saved_dir
            imported_modules := Map.add full_path imported_module !imported_modules
            imported_module
        else
            if (!trace > 0) then fprintf stderr "  [skipped - already loaded]\n"
            Map.find full_path !imported_modules
    let ImportClause s = 
        let (sign, state) = get_parser_state s
        (   (   (kw "import" << MOD_ID (* or string, according to orig. grammar *))
                ++ (poption (lit "(" << (psep1_lit identifier ",") >> lit ")"))
            |>> fun (mod_name, opt_imported_names) -> (mod_name, parse_imported_module mod_name (sign, state), opt_imported_names) )     // !!! tbd: the 'opt_names' for the objects to import is not used
                    // imports : (string * string list option) list;
        ) s
    let ExportClause =
            (   (kw "export" << (psep1_lit identifier ",")) |>> fun names -> Some names
            <|> (kw "export" << (lit "*") |>> fun _ -> None ) )
                    // exports : string list option;     // None means all are exported ("export*")
    let Signature =
            (   (kw "signature" >> lit ":") <<
                (   (pmany Domain) ++
                    (pmany Function)    )   ) 
                        |>> fun (domain_declarations, function_declarations) ->
                            let signature_with_domains   = List.fold (fun sign add_one_domain -> add_one_domain sign) empty_signature domain_declarations
                            let signature_with_functions = List.fold (fun sign add_one_function -> add_one_function sign) signature_with_domains function_declarations
                            signature_with_functions
    let Header = R3
                    (pmany (ImportClause ||>> fun (sign, state) (_, ASM { signature = new_sign }, _) -> (signature_override sign new_sign, state)(* !!! replace with some proper function to load module at some point *)))
                    (poption ExportClause |>> Option.defaultValue None)
                    Signature
    
    let parse_asm_with_header = isAsyncr_isModule_name ++ Header

    match parse_asm_with_header s with
    |   ParserFailure x -> ParserFailure x
    |   ParserSuccess (((asyncr, modul, asm_name), (imports, exports, sign')), s') ->
            //let sign = signature_override sign sign'
            let (sign, state) = get_parser_state s'
            let Term s = Term (chg_parser_state s (sign, Parser.get_state_from_input s))    // !!! temporary
        
            let VariableTerm = ID_VARIABLE
            let parameter_list = opt_psep1 "(" ((VariableTerm >> (kw "in")) ++ getDomainByID) "," ")"
            let DomainDefinition = (kw "domain" << ID_DOMAIN) ++ (lit "=" << Term)
                                            |>> fun _ -> ()
            let FunctionDefinition = R3 (kw "function" << ID_FUNCTION) parameter_list (lit "=" << Term)
                                                |>> fun (f, param_list, t) ->
                                                        //!!!! no type checking
                                                        if List.length param_list > 0
                                                        then failwith "not implemented: definition of function with arity > 0"
                                                        else let fct = function [] -> Eval.eval_term t (State.background_state, Map.empty) | _ -> UNDEF
                                                             fun state -> state_override_static state (Map.add f fct Map.empty)
                                                        
            let MacroDeclaration = R3 (poption (kw "macro") << kw "rule" << ID_RULE) parameter_list (lit "=" << Rule)
                                        |>> fun (rname, param_list, r) ->
                                                if List.length param_list > 0
                                                then failwith "not implemented: definition of rule macros with arity > 0"
                                                else (rname, r)
            let TurboDeclaration = R4 (kw "turbo" << kw "rule" << ID_RULE) parameter_list (poption (kw "in" << getDomainByID)) (lit "=" << Rule)
                                        |>> fun _ -> failwith "not implemented: turbo rule declaration"
            let RuleDeclaration = (MacroDeclaration <|> TurboDeclaration)
            let InvarConstraint = (kw "INVAR" << Term) |>> fun _ -> ()
            let JusticeConstraint = (kw "JUSTICE" << Term) |>> fun _ -> ()
            let CompassionConstraint = (kw "COMPASSION" << lit "(" << Term >> lit "," << Term >> lit ",") |>> fun _ -> ()
            let FairnessConstraint = JusticeConstraint <|> CompassionConstraint
            let Invariant = R3  (kw "invariant" << poption identifier)
                                (kw "over" <<
                                poption (psep1_lit (
                                            (ID_DOMAIN |>> fun _ -> ())
                                        <|> (ID_RULE |>> fun _ -> ())
                                        <|> (ID_FUNCTION << poption (lit "(" << pmany1 getDomainByID << lit ")") |>> fun _ -> ())
                                ) ","))
                                (lit ":" << Term) |>> fun _ -> ()
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
                                            |>> fun _ -> failwith "not implemented: initialization of domains"
            let FunctionInitialization = R3 (kw "function" << ID_FUNCTION) parameter_list (lit "=" << Term)
                                            |>> fun _ -> failwith "not implemented: initialization of dynamic functions"
            let AgentInitialization = (kw "agent" << ID_DOMAIN) ++ (lit ":" << MacroCallRule)
                                            |>> fun _ -> failwith "not implemented: initialization of agents"
            let Initialization = R4 (kw "init" << identifier >> lit ":")
                                    (pmany DomainInitialization)
                                    (pmany FunctionInitialization)
                                    (pmany AgentInitialization) |>> fun _ -> ()
            let parse_asm_rest = 
                R3
                    Body
                    (poption (kw "main" << MacroDeclaration))
                    (poption (pmany Initialization ++ (kw "default" >> (pmany1 Initialization))))
                >>  skip_to_eos

            match parse_asm_rest s' with
            |   ParserFailure x -> ParserFailure x
            |   ParserSuccess (((_, function_definitions, rule_declarations, _, _, _), opt_main_rule_decl, opt_init), s'') ->
                    let rule_declarations = rule_declarations @ (Option.fold (fun _ x -> [x]) [] opt_main_rule_decl)
                    let rdb' = List.fold (fun rdb (rname, r) -> Map.add rname r rdb) empty_rules_db rule_declarations
                    let state' = List.fold (fun state fct_def -> fct_def state) empty_state function_definitions
                    let result = ASM {
                        name      = asm_name;
                        is_module = modul;
                        is_asyncr = asyncr;
                        imports   = imports;
                        exports   = exports;
                        signature = sign;
                        definitions = {
                            functions = state';
                            rules = rdb';
                        };
                    }
                    ParserSuccess ( result, s'')

let extract_definitions_from_asmeta (asm : ASM) : SIGNATURE * STATE * RULES_DB =
    match asm with
    |   ASM (asm_content) ->
            let sign  = asm_content.signature
            let state = state_with_signature asm_content.definitions.functions sign
            let rdb   = asm_content.definitions.rules
            (sign, state, rdb)


let parse_definitions (sign, S) s =
    imported_modules := Map.empty
    fst (Parser.make_parser Asm (sign, S) s)
