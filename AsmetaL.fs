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
let Rule = Parser.rule


(*
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
    ) s

*)


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



    // ws_or_comment << (poption (lit "\"") ++ (pmany palphanum_)) >> poption (lit "\"")
    //     |>> (fun (opt, d, opt2) -> new System.String(d |> List.toArray))

// definitions (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =


let ID_DOMAIN = identifier    //!!!! not exactly
let ID_ENUM = identifier      //!!!! not exactly
let ID_FUNCTION = identifier  //!!!! not exactly
let ID_VARIABLE = identifier  //!!!! not exactly
let ID_RULE = identifier  //!!!! not exactly
let ID_CTL = identifier       //!!!! not exactly
let ID_LTL = identifier

let EnumElement = ID_ENUM


let rec getDomainByID (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<unit>  =
        (   let StructuredTD = StructuredTD (sign, state)
            (   (ID_DOMAIN |>> fun _ -> ())
            <|> StructuredTD ) ) s
    and StructuredTD (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<unit>  =
        (   let getDomainByID  = getDomainByID (sign, state)
            let RuleDomain     = kw "Rule" << opt_psep1 "(" getDomainByID "," ")" |>> fun _ -> ()
            let ProductDomain  = kw "Prod" << opt_psep2 "(" getDomainByID "," ")" |>> fun _ -> ()
            let SequenceDomain = kw "Seq"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> ()
            let PowersetDomain = kw "Powerset" << lit "(" << getDomainByID >> lit ")" |>> fun _ -> ()
            let BagDomain      = kw "Bag"  << lit "(" << getDomainByID >> lit ")" |>> fun _ -> ()
            let MapDomain      = kw "Map"  << lit "(" << getDomainByID >> lit "," << getDomainByID >> lit ")" |>> fun _ -> ()
            RuleDomain <|> ProductDomain <|> SequenceDomain <|> PowersetDomain <|> BagDomain<|> MapDomain ) s
    and ConcreteDomain (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<unit> =
        (   let getDomainByID  = getDomainByID (sign, state)
            (*poption (kw "dynamic") ++*)
            kw "domain" << ID_DOMAIN >> kw "subsetof" << getDomainByID |>> fun _ -> () ) s
    and TypeDomain (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<unit>  =
        (   let StructuredTD = StructuredTD (sign, state)
            let AnyDomain = kw "anydomain" >> ID_DOMAIN |>> fun _ -> ()
            let EnumTD = (kw "enum" << kw "domain" << ID_DOMAIN) ++ (lit "=" << lit "{" << psep1 EnumElement (lit "," <|> lit "|") >> lit "}")
            let AbstractTD = ((*popt_bool (kw "dynamic") >>*) kw "abstract" >> kw "domain") ++ ID_DOMAIN
            let BasicTD = (kw "basic" << kw "domain" << ID_DOMAIN) |>> fun _ -> ()
            AnyDomain <|> StructuredTD <|> (EnumTD |>> fun _ -> ()) <|> (AbstractTD |>> fun _ -> ()) <|> BasicTD ) s

let Domain (sign : SIGNATURE, state : STATE) : Parser<unit>  =
    let (ConcreteDomain, TypeDomain) = (ConcreteDomain (sign, state), TypeDomain (sign, state))
    (ConcreteDomain <|> TypeDomain)  |>> fun _ -> ()

let Function (sign : SIGNATURE, state : STATE) : Parser<unit>  =
    let getDomainByID = getDomainByID (sign, state)
    let StaticFunction     = R3 (kw "static"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let DerivedFunction    = R3 (kw "derived" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let OutFunction        = R3 (poption (kw "dynamic") << kw "out"        << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let MonitoredFunction  = R3 (poption (kw "dynamic") << kw "monitored"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let SharedFunction     = R3 (poption (kw "dynamic") << kw "shared"     << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let ControlledFunction = R3 (poption (kw "dynamic") << kw "controlled" << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let LocalFunction      = R3 (poption (kw "dynamic") << kw "monitored"  << ID_FUNCTION) (lit ":" << getDomainByID) (poption (lit "->" << getDomainByID)) |>> fun _ -> ()
    let DynamicFunction    = OutFunction <|> MonitoredFunction  <|> SharedFunction <|> ControlledFunction <|> LocalFunction
    let BasicFunction      = StaticFunction <|> DynamicFunction
    (BasicFunction <|> DerivedFunction)  |>> fun _ -> ()

let Asm (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =
    let Term = Term sign
    let Rule = Rule sign
    let getDomainByID = getDomainByID (sign, state)
    ((  let (Domain, Function) = (Domain (sign, state), Function (sign, state))
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
                        (pmany Function)    )   )  |>> fun _ -> ()
        let Header =
                (pmany ImportClause) ++
                (pmany ExportClause) ++
                Signature
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
                    (   (pmany DomainDefinition) ++
                        (pmany FunctionDefinition) ++
                        (pmany RuleDeclaration) ++
                        (pmany InvarConstraint) ++
                        (pmany FairnessConstraint) ++
                        (pmany Property)    )   )
                //failwith "Body: not implemented"

        // let body_section = preturn ()
        // let main_rule = preturn ()
        // let initial_state = preturn ()
        // let default_initial_state = preturn ()
        
        asm_name ++
        Header >>
        Body >>
        poption (kw "main" << MacroDeclaration) ++
        skip_to_eos)
            |>> fun ((asyncr,modul,name),(imports,exports)) -> (empty_signature, empty_state, empty_rules_db)) s




let make_parser = Parser.make_parser

let parse_definitions (sign, S) s = make_parser Asm (sign, S) s




