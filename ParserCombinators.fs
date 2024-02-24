module ParserCombinators

open Common

type ParserInput = int * int * char list             // line, column, stream

let parser_input_from_string s = (1, 1, explode s)
let parser_input_pos (line, col, _) = (line, col)
let parser_input_getc = function
|   (line, col, []) -> (None, (line, col, []))
|   (line, col, '\n' :: cs) -> (Some '\n', (line + 1, col, cs))
|   (line, col, c :: cs) -> (Some c, (line, col + 1, cs))

type 'a ParserResult =
|   ParserSuccess of 'a * ParserInput
|   ParserFailure of string * ParserInput * string   // parser name, remaining input, message
    
type 'a Parser = ParserInput -> 'a ParserResult

let parser_msg = function
|   ParserSuccess _ -> "parsing succeeded"
|   ParserFailure (name, (l, c, s), msg) -> sprintf "parser '%s': parsing failed at line %d, column %d (%s)\nremaining input:\n%s\n" name l c msg (implode s)

let preturn x : 'a Parser = fun input -> ParserSuccess (x, input)
let pfail     : 'a Parser = fun input -> ParserFailure ("pfail", input, "always failing parser")
let pfail_msg name msg : 'a Parser = fun input -> ParserFailure (name, input, msg)

let pcharsat c_pred expected : char Parser =
    fun input ->
        match parser_input_getc input with
        |   (Some c, input') ->
                if c_pred c
                then ParserSuccess (c, input')
                else ParserFailure ("pchar", input, sprintf "character did not match: %s expected, '%c'found" expected c)
        |   (None, _) ->
                ParserFailure ("pchar", input, sprintf "%s expected, end-of-stream found." expected)

let pchar c0 = pcharsat (fun c -> c = c0) ("\""+(c0.ToString())+"\"")
let pdigit = pcharsat (fun c -> System.Char.IsDigit c) "digit"
let pletter = pcharsat (fun c -> System.Char.IsLetter c) "letter"
let palphanum = pcharsat (fun c -> System.Char.IsLetterOrDigit c) "alphanumeric character"
let palphanum_ = pcharsat (fun c -> System.Char.IsLetterOrDigit c || c = '_') "alphanumeric character or '_'"
    
let (>>=) (p: 'a Parser) (f: 'a -> 'b Parser) : 'b Parser =
    fun input ->
        match p input with
        |   ParserSuccess(x, rest) -> (f x) rest
        |   ParserFailure (name, rest, msg) -> ParserFailure (name, rest, msg)

let (<<) p1 p2 : 'b Parser = p1 >>= (fun _ -> p2)
let (>>) p1 p2 : 'a Parser = p1 >>= (fun x -> p2 >>= (fun y -> preturn x))
let (++) p1 p2 : ('a * 'b) Parser = p1 >>= (fun x -> p2 >>= (fun y -> preturn (x, y)))
let R2 p1 p2 : ('a * 'b) Parser = p1 >>= (fun x -> p2 >>= (fun y -> preturn (x, y)))
let R3 p1 p2 p3 : ('a * 'b * 'c) Parser = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> preturn (x1, x2, x3))))
let R4 p1 p2 p3 p4 : ('a * 'b * 'c * 'd) Parser = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> p4 >>= (fun x4 -> preturn (x1, x2, x3, x4)))))
let R5 p1 p2 p3 p4 p5: ('a * 'b * 'c * 'd * 'e) Parser = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> p4 >>= (fun x4 -> p5 >>= (fun x5 -> preturn (x1, x2, x3, x4, x5))))))

let (<|>) (p1: 'a Parser) (p2: 'a Parser) : 'a Parser =
    fun stream ->
        match p1 stream with
        | ParserFailure _ -> p2 stream
        | res -> res
    
let (|>>) p f : 'b Parser = p >>= (fun x -> preturn (f x))

let rec pmany p : Parser<'a list> =
    let rec F (result, stream) =
        match p stream with
        |   ParserSuccess (x, stream') -> F (x :: result, stream')
        |   ParserFailure _ -> ParserSuccess (List.rev result, stream)
    fun stream -> F ([], stream)

let pmany1 p = ((p ++ pmany p) |>> fun (x, xs) -> x :: xs)

let poption p =
        ( p |>> fun x -> Some x )
    <|> ( preturn None )

let pchoice ps : 'a Parser = Seq.reduce (fun (p1: 'a Parser) (p2: 'a Parser) -> p1 <|> p2) ps

let prun (p: 'a Parser) (s: string) = p (parser_input_from_string s)

(*
/// Parses characters which satisfy the given function.
let pcharF f: Parser<char> = function
    |   x::xs when f x -> Success(x, xs)
    |   stream -> Failure stream

*)

let pstring (s: string) input0 =
    let rec F = function
        |   (result, [], input) ->
                ParserSuccess (List.rev result, input)
        |   (result, c :: cs', input) ->
            (   match pchar c input with
                |   ParserSuccess (x, input') -> F (x :: result, cs', input')
                |   ParserFailure _ -> ParserFailure ("pstring", input0, sprintf "string \"%s\" expected" s) )
    F ([], [for c in s -> c], input0)

let pwhitespace : char list Parser =
    pmany (pcharsat (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace character (' ', '\t', '\n' or '\r')")

let pint : int Parser =
    ( ((pchar '+' <|> pchar '-') <|> preturn '+')  ++  (pmany1 pdigit) )
        >>= fun (s, d) -> preturn (int (implode (s::d)))

let peos : unit Parser = function
|   (line, col, []) -> ParserSuccess ((), (line, col, []))
|   (line, col, s) -> ParserFailure ("peos", (line, col, s), "end-of-stream expected")
