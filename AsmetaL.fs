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

// definitions (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =
let asm (sign : SIGNATURE, state : STATE) (s : ParserInput) : ParserResult<SIGNATURE * STATE * RULES_DB>  =
    ((  let asm_name =
                (   ( (poption (kw "asyncr")) ++ (kw "asm" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, false, name) )
                <|> ( (poption (kw "asyncr")) ++ (kw "module" << identifier) |>> fun (asyncr, name) -> (asyncr.IsSome, true, name) ) )
        asm_name )
            |>> fun _ -> (empty_signature, empty_state, empty_rules_db)) s

// 	(isAsynchr?=('asyncr')? type=( 'asm' | 'module' ) name=(extendedNameForAsm | STRING) 
// 	headerSection=Header bodySection=Body ( 'main' mainrule=MacroDeclaration )? 
// 	( ( initialState+=Initialization )* 'default' defaultInitialState=Initialization ( initialState+=Initialization )* )?)?
// ;



let make_parser = Parser.make_parser

let parse_definitions (sign, S) s = make_parser asm (sign, S) s




