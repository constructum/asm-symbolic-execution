module AsmetaL

open Common
open Background
open ParserCombinators
open Signature
open State
open AST

//--------------------------------------------------------------------

type ASM_Content = {
    asyncr_module_name : bool * bool * string;
    imports : (string * string list option) list;
    exports : string list option;     // None means all are exported ("export*")
    signature : unit;
    definitions : unit;
}

type ASM = ASM of ASM_Content

//--------------------------------------------------------------------

let asm_content (asyncr_module_name as (asyncr : bool, modul : bool, name : string))
                (imports : (string * string list option) list)
                (exports : string list option)
                (signature : unit)
                (definitions : unit) : ASM_Content =
    {
        asyncr_module_name = asyncr_module_name;
        imports = imports;
        exports = exports;
        signature = signature;
        definitions = definitions;
    }

let mkAsm (asyncr : bool, modul : bool, name : string) (imports : (string * string list option) list) (exports : string list option) (signature : unit) (definitions : unit) : ASM =
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


let ID_DOMAIN = identifier    //!!!! not exactly
let ID_ENUM = identifier      //!!!! not exactly
let ID_FUNCTION = identifier  //!!!! not exactly
let ID_VARIABLE = pchar '$' ++ identifier |>> fun (c, s) -> c.ToString() + s
let ID_RULE = identifier  //!!!! not exactly
let ID_CTL = identifier       //!!!! not exactly
let ID_LTL = identifier

let EnumElement = ID_ENUM


let id_domain_to_type id_dom =
    match id_dom with
    |   "Boolean" -> Boolean
    |   "Integer" -> Integer
    |   "String" -> String
    |   "Undef" -> Undef
    |   _ -> failwith $"id_domain_to_type: unknown type {id_dom}"

let rec getDomainByID (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE>  =
        (   let StructuredTD = StructuredTD sign
            (   (ID_DOMAIN |>> fun s -> id_domain_to_type s)
            <|> (StructuredTD |>> fun _-> failwith "not implemented: structured type domain")) ) s
    and StructuredTD (sign : SIGNATURE (*, state : STATE*) ) (s : ParserInput) : ParserResult<TYPE>  =
        (   let getDomainByID  = getDomainByID (sign (* , state *) )
            let RuleDomain     = kw "Rule" << opt_psep1 "(" getDomainByID "," ")" |>> fun _ -> failwith "RuleDomain not implemented"
            let ProductDomain  = kw "Prod" << opt_psep2 "(" getDomainByID "," ")" |>> Prod
            let SequenceDomain = kw "Seq"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "SequenceDomain not implemented"
            let PowersetDomain = kw "Powerset" << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "PowersetDomain not implemented"
            let BagDomain      = kw "Bag"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> failwith "BagDomain not implemented"
            let MapDomain      = kw "Map"  << lit "(" << getDomainByID >> lit "," << getDomainByID >> lit ")" |>> fun _ -> failwith "MapDomain not implemented"
            RuleDomain <|> ProductDomain <|> SequenceDomain <|> PowersetDomain <|> BagDomain<|> MapDomain ) s
    and ConcreteDomain (sign : SIGNATURE) (s : ParserInput) : ParserResult<TYPE> =
        (   let getDomainByID  = getDomainByID sign
            kw "domain" << ID_DOMAIN >> kw "subsetof" << getDomainByID |>> fun _ -> failwith "not implemented: concrete domain" ) s
    and TypeDomain (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<TYPE>  =
        (   let StructuredTD = StructuredTD (sign (*, state *) )
            let AnyDomain = kw "anydomain" >> ID_DOMAIN |>> fun _ -> failwith "not implemented: anydomain"
            let EnumTD = (kw "enum" << kw "domain" << ID_DOMAIN) ++ (lit "=" << lit "{" << psep1 EnumElement (lit "," <|> lit "|") >> lit "}")
                                |>> fun _ -> failwith "not implemented: enum type domain"
            let AbstractTD = (popt_bool (kw "dynamic") >> kw "abstract" >> kw "domain") ++ ID_DOMAIN
                                |>> fun _ -> failwith "not implemented: abstract type domain"
            let BasicTD = (kw "basic" << kw "domain" << ID_DOMAIN) |>> fun _ -> ()
                                |>> fun _ -> failwith "not implemented: basic type domain"
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
    let Rule = Rule sign
    let Term = Term sign
    let BlockRule = kw "par" << pmany1 Rule >> kw "endpar" |>> ParRule
    let ConditionalRule = R3 (kw "if" << Term) (kw "then" << Rule) (poption (kw "else" << Rule) |>> Option.defaultValue skipRule) >> kw "endif" |>> CondRule
    let ChooseRule = R4 (kw "choose" << psep1_lit ((ID_VARIABLE >> kw "in") ++ Term) ",") (kw "with" << Term) (kw "do" << Rule) (poption (kw "ifnone" << Rule))
                        |>> fun _ -> failwith "not implemented: choose rule"
    let ForallRule = R3 (kw "forall" << psep1_lit ((ID_VARIABLE >> kw "in") ++ Term) ",") (kw "with" << Term) (kw "do" << Rule)
                        |>> fun _ -> failwith "not implemented: forall rule"
    (   kw "skip" |>> fun _ -> skipRule
//  <|> MacroCallRule
    <|> BlockRule
    <|> ConditionalRule
    <|> ChooseRule
    <|> ForallRule
    // <|> LetRule
    // <|> ExtendRule
    ) s

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




let Asm (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =
    let getDomainByID = getDomainByID (sign (*, state *) )
    let (Domain, Function) = (Domain (sign, state), Function (sign, state))
    let asm_name =
            (   ( (poption (kw "asyncr")) ++ (kw "asm" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, false, name) )
            <|> ( (poption (kw "asyncr")) ++ (kw "module" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, true, name) ) )
    let ImportClause = 
            (   (kw "import" << MOD_ID (* or string, according to orig. grammar *)) ++ (poption (lit "(" << (psep1_lit identifier ",") >> lit ")"))
            |>> fun (name, opt_names) -> (name, opt_names) )
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
                            List.fold (fun sign (f, fi) -> add_function_name f (fi.fct_kind, fi.fct_type, fi.infix_status) sign) sign fcts
    let Header = R3
                    (pmany ImportClause)
                    (pmany ExportClause)
                    Signature
    
    let parse_asm_with_header = asm_name ++ Header

    match parse_asm_with_header s with
    |   ParserFailure x -> ParserFailure x
    |   ParserSuccess (((asyncr, modul, asm_name), (imports, exports, sign')), s') ->

            let Term = Term sign'
            let Rule = Rule sign'
        
            let VariableTerm = ID_VARIABLE
            let parameter_list = opt_psep1 "(" ((VariableTerm >> (kw "in")) ++ getDomainByID) "," ")"
            let DomainDefinition = (kw "domain" << ID_DOMAIN) ++ (lit "=" << Term)
                                            |>> fun _ -> ()
            let FunctionDefinition = R3 (kw "function" << ID_FUNCTION) parameter_list (lit "=" << Term)
                                                |>> fun _ -> ()
            let MacroDeclaration = R3 (poption (kw "macro") << kw "rule" << ID_RULE) parameter_list (lit "=" << Rule) |>> fun _ -> ()
            let TurboDeclaration = R4 (kw "turbo" << kw "rule" << ID_RULE) parameter_list (poption (kw "in" << getDomainByID)) (lit "=" << Rule) |>> fun _ -> ()
            let RuleDeclaration = (MacroDeclaration <|> TurboDeclaration)
                                                |>> fun _ -> ()
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
            let Property = Invariant <|> TemporalProperty
            let Body =
                    (   (kw "definitions" >> lit ":") <<
                        R6  (pmany DomainDefinition)
                            (pmany FunctionDefinition)
                            (pmany RuleDeclaration)
                            (pmany InvarConstraint)
                            (pmany FairnessConstraint)
                            (pmany Property)       )
            let parse_asm_rest = 
                Body >>
                poption (kw "main" << MacroDeclaration) ++
                skip_to_eos
            // let initial_state = preturn ()
            // let default_initial_state = preturn ()
            // let parse_asm_with_header = asm_name ++ Header

            match parse_asm_rest s' with
            |   ParserFailure x -> ParserFailure x
            |   ParserSuccess ((_, _, _, _, _, _), s'') ->
                    ParserSuccess ((sign', state, empty_rules_db), s'')
                    //ParserSuccess (sign', state, empty_rules_db) s''




let make_parser = Parser.make_parser

let parse_definitions (sign, S) s = make_parser Asm (sign, S) s




