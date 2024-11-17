module AsmetaL

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

let trace = ref 1

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
            >>= fun s -> if s = explode kw_name then preturn s
                         else pfail_msg "keyword" ($"keyword '{kw_name}' expected, '{implode s}' found")


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


let type_of_basic_domain sign s =
    if s <> "Boolean" && s <> "Integer" && s <> "String" && s <> "Undef" && s <> "Rule"
        && s <> "Complex" && s <> "Real" && s <> "Natural" && s <> "Char"   // !!! last four are not yet implemented
    then failwith (sprintf "not implemented: basic type domain '%s'" s)
    else Signature.get_type s [] sign

let rec getDomainByID (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE>  =
        (   let StructuredTD = StructuredTD sign
            (   StructuredTD
            <|> (ID_DOMAIN |>> fun s -> Signature.get_type s [] sign)) ) s
    and StructuredTD (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE>  =
        (   let getDomainByID  = getDomainByID sign
            // !!! no longer mentioned in doc: let RuleDomain     = kw "Rule" << opt_psep1 "(" getDomainByID "," ")" |>> fun _ -> failwith "RuleDomain not implemented"
            let ProductDomain  = kw "Prod" << opt_psep2 "(" getDomainByID "," ")" |>> Prod
            let SequenceDomain = kw "Seq"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "SequenceDomain not implemented"
            let PowersetDomain = kw "Powerset" << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "PowersetDomain not implemented"
            let BagDomain      = kw "Bag"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "BagDomain not implemented"
            let MapDomain      = kw "Map"  << lit "(" << getDomainByID >> lit "," << getDomainByID >> lit ")" |>> fun _ -> failwith "MapDomain not implemented"
            // !!! no longer mentioned in doc: RuleDomain <|> 
            ProductDomain <|> SequenceDomain <|> PowersetDomain <|> BagDomain<|> MapDomain ) s
    and ConcreteDomain (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE> =
        (   let getDomainByID  = getDomainByID sign
            kw "domain" << ID_DOMAIN >> kw "subsetof" << getDomainByID |>> fun _ -> failwith "not implemented: concrete domain" ) s
    and TypeDomain (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<TYPE>  =
        (   let StructuredTD = StructuredTD (sign (*, state *) )
            let AnyDomain = kw "anydomain" << ID_DOMAIN |>> fun typename -> TypeParam typename
            let EnumTD = (kw "enum" << kw "domain" << ID_DOMAIN) ++ (lit "=" << lit "{" << psep1 EnumElement (lit "," <|> lit "|") >> lit "}")
                                |>> fun _ -> failwith "not implemented: enum type domain"
            let AbstractTD = (popt_bool (kw "dynamic") >> kw "abstract" >> kw "domain") ++ ID_DOMAIN     // !!! what about 'dynamic'?
                                |>> fun (is_dynamic, s) -> TypeCons (s, []) 
            let BasicTD = (kw "basic" << kw "domain" << ID_DOMAIN) |>> type_of_basic_domain sign
            AnyDomain <|> StructuredTD <|> EnumTD <|> AbstractTD <|> BasicTD ) s

let Domain (sign : SIGNATURE, state : STATE) : Parser<unit>  =
    let (ConcreteDomain, TypeDomain) = (ConcreteDomain (sign (*, state*) ), TypeDomain (sign, state))
    (ConcreteDomain <|> TypeDomain)  |>> fun _ -> ()

let Function (sign : SIGNATURE, state : STATE) : Parser<FCT_NAME * FCT_INFO>  =
    let getDomainByID = getDomainByID (sign (*, state *) )
    let prod_to_type_list ty = List.map (function Prod _ -> failwith "not supported: nested Prod type" | ty_ -> ty_) ty
    let to_fct_type (tys : TYPE, ty_opt : TYPE option) =
        match (tys, ty_opt) with
        |   (Prod tys, None)    -> failwith "not supported: nullary function of Prod type"
        |   (ty, None)          -> ([], ty)
        |   (_, Some (Prod _))  -> failwith "not supported: Prod type as range of function"
        |   (Prod tys, Some ty) -> (prod_to_type_list tys, ty)
        |   (ty, Some ty')      -> ([ty], ty')
    let StaticFunction     = R3 (kw "static"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> (f, { fct_kind = Static; fct_type = to_fct_type(tys, opt_ty); infix_status = NonInfix })
    let DerivedFunction    = R3 (kw "derived" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: derived function"
    let OutFunction        = R3 (poption (kw "dynamic") << kw "out"        << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: out function"
    let MonitoredFunction  = R3 (poption (kw "dynamic") << kw "monitored"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: monitored function"
    let SharedFunction     = R3 (poption (kw "dynamic") << kw "shared"     << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: shared function"
    let ControlledFunction = R3 (poption (kw "dynamic") << kw "controlled" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun (f, tys, opt_ty) -> (f, { fct_kind = Controlled; fct_type = to_fct_type(tys, opt_ty); infix_status = NonInfix })
    let LocalFunction      = R3 (poption (kw "dynamic") << kw "local"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID))
                                |>> fun _ -> failwith "not implemented: local function"
    let DynamicFunction    = OutFunction <|> MonitoredFunction  <|> SharedFunction <|> ControlledFunction <|> LocalFunction
    let BasicFunction      = StaticFunction <|> DynamicFunction
    (BasicFunction <|> DerivedFunction)



let rec BasicRule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE>  =
    if (!trace > 0) then fprintf stderr "BasicRule: " // "BasicRule: %s" (ParserInput.to_string s)
    let Rule = Rule sign
    let Term = Term sign
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
    let MacroCallRule = MacroCallRule sign
    
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

and MacroCallRule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE>  =
    (   (ID_RULE >> lit "[") ++ (psep0 (Term sign) (lit ",") >> lit "]")
            |>> fun _ -> failwith "not implemented: macro call rule" ) s

and TurboRule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE>  =
    let Rule = Rule sign
    let Term = Term sign
    let SeqRule = kw "seq" << pmany1 Rule >> kw "endseq" |>> AST.SeqRule
    let IterateRule = kw "iterate" << Rule >> kw "enditerate" |>> IterRule
    (   SeqRule
    <|> IterateRule
    // <|> TurboCallRule
    // <|> TurboLocalStateRule
    ) s

and DerivedRule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE>  =
    let Rule = Rule sign
    let Term = Term sign
    let IterativeWhileRule = (kw "while" << Term) ++ (kw "do" << Rule)
                                |>> fun (G, R) -> IterRule (CondRule (G, R, skipRule))
    let TurboDerivedRule =
            // RecursiveWhileRule <|>   // !!! ?
            IterativeWhileRule
    (   
//      BasicDerivedRule <|>
        TurboDerivedRule
    ) s


and Rule (sign : SIGNATURE) (s : ParserInput) : ParserResult<RULE> =
    let Term = Term sign
    let (BasicRule, TurboRule, DerivedRule) = (BasicRule sign, TurboRule sign, DerivedRule sign)
    let UpdateRule = (R3 (Term) (lit ":=") Term) |>> fun (t1,_,t2) -> Parser.mkUpdateRule sign (t1, t2)   // !!!! not exactly as in AsmetaL grammar
    (   UpdateRule
    <|> BasicRule
    <|> TurboRule
    // <|> TurboReturnRule
    // <|> TermAsRule
    <|> DerivedRule
    ) s




let rec Asm (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<ASM>  =
    let getDomainByID = getDomainByID (sign (*, state *) )
    let (Domain, Function) = (Domain (sign, state), Function (sign, state))
    let isAsyncr_isModule_name =
            (   ( (poption (kw "asyncr")) ++ (kw "asm" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, false, name) )
            <|> ( (poption (kw "asyncr")) ++ (kw "module" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, true, name) ) )
    let parse_imported_module mod_id =
        if (!trace > 0) then fprintf stderr "importing module: '%s'\n" mod_id
        let saved_dir = System.IO.Directory.GetCurrentDirectory ()
        let filename = mod_id + ".asm"
        let full_path = System.IO.Path.GetFullPath filename
        let new_dir = System.IO.Path.GetDirectoryName filename |> fun s -> if s = "" then "." else s
        // move to directory where the imported file is located
        // in order to correctly resolve the relative paths of modules
        // that may be imported in the imported module
        System.IO.Directory.SetCurrentDirectory new_dir
        let text = Common.readfile full_path
        let parse = Parser.make_parser Asm (sign, state)
        let imported_module = parse text        // !!! checks missing (e.g. check that it is a 'module' and not an 'asm', etc.)
        // move to original directory (where the importing file is located)
        System.IO.Directory.SetCurrentDirectory saved_dir
        imported_module
    let ImportClause = 
            (   (kw "import" << MOD_ID (* or string, according to orig. grammar *))
                ++ (poption (lit "(" << (psep1_lit identifier ",") >> lit ")"))
            |>> fun (mod_name, opt_imported_names) -> (mod_name, parse_imported_module mod_name, opt_imported_names) )     // !!! tbd: the 'opt_names' for the objects to import is not used
                    // imports : (string * string list option) list;
    let ExportClause =
            (   (kw "export" << (psep1_lit identifier ",")) |>> fun names -> Some names
            <|> (kw "export" << (lit "*") |>> fun _ -> None ) )
                    // exports : string list option;     // None means all are exported ("export*")
    let Signature =
            (   (kw "signature" >> lit ":") <<
                (   (pmany Domain) ++
                    (pmany Function)    )   ) 
                        |>> fun (_, fcts) ->
                            List.fold (fun sign (f, fi) -> add_function_name f (fi.fct_kind, fi.fct_type, fi.infix_status) sign) empty_signature fcts
    let Header = R3
                    (pmany ImportClause)
                    (poption ExportClause |>> Option.defaultValue None)
                    Signature
    
    let parse_asm_with_header = isAsyncr_isModule_name ++ Header

    match parse_asm_with_header s with
    |   ParserFailure x -> ParserFailure x
    |   ParserSuccess (((asyncr, modul, asm_name), (imports, exports, sign')), s') ->
            let sign = signature_override sign sign'
            let Term = Term sign
            let Rule = Rule sign
            let MacroCallRule = MacroCallRule sign
        
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


let parse_definitions (sign, S) s = Parser.make_parser Asm (sign, S) s




