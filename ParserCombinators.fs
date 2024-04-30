module ParserCombinators

open Common

type Position = { abs : int; line : int; col : int; }
let initial_position = { abs = 0; line = 1; col = 1; }

type FailedAt = Position * string
type ParserInput = Set<FailedAt> * Position * char list             // position, stream

let parser_input_from_string s = (Set.empty, initial_position, explode s)
let get_failures : ParserInput -> Set<FailedAt> = fun (failures, _, _) -> failures
let get_pos : ParserInput -> Position = fun (_, pos, _) -> pos
let get_stream : ParserInput -> char list = fun (_, _, stream) -> stream

let input_abs_pos (_, pos, _) = pos.abs

let parser_input_getc : ParserInput -> option<char> * ParserInput = function
|   (failures, pos, []) -> (None, (failures, pos, []))
|   (failures, {abs=abs;line=line;col=_}, '\r' :: '\n' :: cs) -> (Some '\n', (failures, { abs = abs + 2; line = line + 1; col = 1; }, cs))
|   (failures, {abs=abs;line=line;col=col}, '\n' :: cs)       -> (Some '\n', (failures, { abs = abs + 1; line = line + 1; col = 1; }, cs))
|   (failures, {abs=abs;line=line;col=col}, c :: cs)          -> (Some c,    (failures, { abs = abs + 1; line = line; col = col + 1; }, cs))

type 'a ParserResult =
|   ParserSuccess of 'a * ParserInput
|   ParserFailure of Set<FailedAt>   // parser name, remaining input, message
    
type 'a Parser = ParserInput -> 'a ParserResult

let combine_failures (failures1 : Set<FailedAt>, failures2 : Set<FailedAt>) =
    if Set.isEmpty failures1 then failures2
    else if Set.isEmpty failures2 then failures1
    else
        match (Seq.head failures1, Seq.head failures2) with
        |   ((pos1,_), (pos2,_)) ->
                let (pos1, pos2) = (pos1.abs, pos2.abs)
                if pos1 > pos2 then failures1
                else if pos1 = pos2 then Set.union failures1 failures2
                else failures2

let parser_msg = function
|   ParserSuccess _ -> "parsing succeeded"
|   ParserFailure failures ->
        let output_failures = String.concat "\n" (Set.toList failures >>| fun (pos, msg) -> $"[{pos.line}:{pos.col}] {msg}")
        sprintf $"parsing failed:\n{output_failures}"
            

let preturn x : 'a Parser = fun input -> ParserSuccess (x, input)
let pfail     : 'a Parser = fun input -> ParserFailure (combine_failures (Set.singleton (get_pos input, "always failing parser"), get_failures input))   // !!!! ?????
let pfail_msg name msg : 'a Parser = fun input -> ParserFailure (combine_failures (Set.singleton (get_pos input, msg), get_failures input))
//msg

let pcharsat c_pred expected : char Parser =
    fun input ->
        match parser_input_getc input with
        |   (Some c, input') ->
                if c_pred c
                then ParserSuccess (c, input')
                else //ParserFailure (combine_failures (Set.singleton (get_pos input, $"character did not match: {expected} expected, '{c}' found"), get_failures input))
                     ParserFailure (combine_failures (Set.empty, get_failures input))
        |   (None, _) ->
                ParserFailure (combine_failures (Set.empty, (*Set.singleton (get_pos input, $"{expected} expected, end-of-stream found."),*) get_failures input))

let pchar c0 = pcharsat (fun c -> c = c0) ("\""+(c0.ToString())+"\"")
let pdigit = pcharsat (fun c -> System.Char.IsDigit c) "digit"
let pletter = pcharsat (fun c -> System.Char.IsLetter c) "letter"
let palphanum = pcharsat (fun c -> System.Char.IsLetterOrDigit c) "alphanumeric character"
let palphanum_ = pcharsat (fun c -> System.Char.IsLetterOrDigit c || c = '_') "alphanumeric character or '_'"
    
let (>>=) (p: 'a Parser) (f: 'a -> 'b Parser) : 'b Parser =
    fun input ->
        match p input with
        |   ParserSuccess(x, rest) -> (f x) rest
        |   ParserFailure failures -> ParserFailure failures

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
        |   ParserFailure failures1 ->
                let stream' = (failures1, get_pos stream, get_stream stream)
                (   match p2 stream' with
                    |   ParserFailure failures2 ->
                            ParserFailure (combine_failures (failures1, failures2))
                    |   ParserSuccess (result2, (failures2, pos2, stream2)) ->
                            ParserSuccess (result2, (combine_failures (failures1, failures2), pos2, stream2)) )
        |   res as ParserSuccess _ -> res
    
let (|>>) p f : 'b Parser = p >>= (fun x -> preturn (f x))

let rec pmany p : Parser<'a list> =
    let rec F (result, (input0 as (failures0, pos0, stream0))) =
        match p input0 with
        |   ParserSuccess (x, stream') -> F (x :: result, stream')
        |   ParserFailure failures -> ParserSuccess (List.rev result, (combine_failures (failures0, failures), pos0, stream0))
    fun stream -> F ([], stream)

let pmany1 p = ((p ++ pmany p) |>> fun (x, xs) -> x :: xs)

let poption p =
        ( p |>> fun x -> Some x )
    <|> ( preturn None )

let pchoice ps : 'a Parser = Seq.reduce (fun (p1: 'a Parser) (p2: 'a Parser) -> p1 <|> p2) ps

let prun (p: 'a Parser) (s: string) = p (parser_input_from_string s)


let pstring (s: string) input0 =
    let rec F = function
        |   (result, [], input) ->
                ParserSuccess (List.rev result, input)
        |   (result, c :: cs', input) ->
            (   match pchar c input with
                |   ParserSuccess (x, input') -> F (x :: result, cs', input')
                |   ParserFailure _ ->
                        let (pos, pos0) = (input_abs_pos input, input_abs_pos input0)
                        if get_stream input = []
                        then ParserFailure (combine_failures (Set.singleton (get_pos input0, sprintf "string \"%s\" expected, end-of-stream found" s), get_failures input0))
                        else ParserFailure (combine_failures (Set.singleton (get_pos input0, sprintf "string \"%s\" expected, \"%s\" found" s ((input0 |> get_stream |> implode)[0..pos-pos0] )), get_failures input0)) )
    F ([], [for c in s -> c], input0)

let pwhitespace : char list Parser =
    pmany (pcharsat (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') "whitespace character (' ', '\\t', '\\n' or '\\r')")

let pint : int Parser =
    ( ((pchar '+' <|> pchar '-') <|> preturn '+')  ++  (pmany1 pdigit) )
        >>= fun (s, d) -> preturn (int (implode (s::d)))

let peos : unit Parser = function
|   (failures, pos, []) -> ParserSuccess ((), (failures, pos, []))
|   (failures, pos, s)  -> ParserFailure (combine_failures (Set.singleton (pos, "end-of-stream expected"), failures))
