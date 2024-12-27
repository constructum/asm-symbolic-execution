module ParserCombinators

open Common

type SrcPos = { abs : int; line : int; col : int; }

type SrcLoc =
|   File of string ref      // name of file containing source code
|   Strg of string ref      // string containing source code

let src_loc_to_string = function
|   File f -> sprintf "file '%s'" !f
|   Strg s -> sprintf "string '%s'" !s

type SrcReg = SrcLoc * SrcPos * SrcPos     // file name, position before region, position after region

let src_reg_to_string = function
    (loc, pos1, pos2) -> sprintf "region (%s: [%d:%d]-[%d:%d])" (src_loc_to_string loc) pos1.line pos1.col pos2.line pos2.col

let initial_position = { abs = 0; line = 1; col = 1; }

type FailedAt = SrcPos * string
type 'parser_state ParserInput = Set<FailedAt> * SrcLoc * SrcPos * 'parser_state * char list             // position, stream

let parser_input_in_state_from_string initial_location state0 s = (Set.empty, (initial_location : SrcLoc), (initial_position : SrcPos), state0, explode s)
let get_failures : 'a ParserInput -> Set<FailedAt> = fun (failures, _, _, _, _) -> failures
let get_loc : 'a ParserInput -> SrcLoc = fun (_, loc, _, _, _) -> loc
let get_pos : 'a ParserInput -> SrcPos = fun (_, _, pos, _, _) -> pos
let get_parser_state : 'a ParserInput -> 'a = fun (_, _, _, parser_state, _) -> parser_state
let chg_parser_state : 'a ParserInput -> 'b -> 'b ParserInput = fun (failure, loc, pos, _, stream) parser_state' -> (failure, loc, pos, parser_state', stream)
let get_stream : 'a ParserInput -> char list = fun (_, _, _, _,stream) -> stream

let input_abs_pos (_, _, pos, _, _) = pos.abs

let parser_input_getc : 'a ParserInput -> option<char> * 'a ParserInput = function
|   (failures, loc, pos, state, []) -> (None, (failures, loc, pos, state, []))
|   (failures, loc, {abs=abs;line=line;col=_}, state, '\r' :: '\n' :: cs) -> (Some '\n', (failures, loc, { abs = abs + 2; line = line + 1; col = 1; }, state, cs))
|   (failures, loc, {abs=abs;line=line;col=col}, state, '\n' :: cs)       -> (Some '\n', (failures, loc, { abs = abs + 1; line = line + 1; col = 1; }, state, cs))
|   (failures, loc, {abs=abs;line=line;col=col}, state, c :: cs)          -> (Some c,    (failures, loc, { abs = abs + 1; line = line; col = col + 1; }, state, cs))

type ('result, 'state) ParserResult =
|   ParserSuccess of 'result * 'state ParserInput
|   ParserFailure of Set<FailedAt>   // parser name, remaining input, message
    
type ('result, 'state) Parser = 'state ParserInput -> ParserResult<'result, 'state>


let (>>=) (p: Parser<'a, 'state>) (f: 'a -> Parser<'b, 'state>) : Parser<'b, 'state> =
    fun input ->
        match p input with
        |   ParserSuccess(x, rest) -> (f x) rest
        |   ParserFailure failures -> ParserFailure failures

let (||>>) (p: Parser<'a, 'state1>) (f: 'state1 -> 'a -> 'state2) (s : ParserInput<'state1>): ParserResult<'a, 'state2> =
    match p s with
    |   ParserSuccess (result, (failure', loc, pos', state', stream')) -> ParserSuccess (result, (failure', loc, pos', f state' result, stream'))
    |   ParserFailure failures -> ParserFailure failures

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
            

let preturn x : Parser<'a, 'state> = fun input -> ParserSuccess (x, input)
let pfail     : Parser<'a, 'state> = fun input -> ParserFailure (combine_failures (Set.singleton (get_pos input, "always failing parser"), get_failures input))   // !!!! ?????
let pfail_msg name msg : Parser<'a, 'state> = fun input -> ParserFailure (combine_failures (Set.singleton (get_pos input, msg), get_failures input))
//msg
    
let (|>>) p f : Parser<'b, 'state> = p >>= (fun x -> preturn (f x))


let pcharsat c_pred expected : Parser<char, 'state> =
    fun input ->
        match parser_input_getc input with
        |   (Some c, input') ->
                if c_pred c
                then ParserSuccess (c, input')
                else //ParserFailure (combine_failures (Set.singleton (get_pos input, $"character did not match: {expected} expected, '{c}' found"), get_failures input))
                     ParserFailure (combine_failures (Set.empty, get_failures input))
        |   (None, _) ->
                ParserFailure (combine_failures (Set.empty, (*Set.singleton (get_pos input, $"{expected} expected, end-of-stream found."),*) get_failures input))

let pchar c0 s = pcharsat (fun c -> c = c0) ("\""+(c0.ToString())+"\"") s
let pdigit s = pcharsat (fun c -> System.Char.IsDigit c) "digit" s
let pletter s = pcharsat (fun c -> System.Char.IsLetter c) "letter" s
let palphanum s = pcharsat (fun c -> System.Char.IsLetterOrDigit c) "alphanumeric character" s
let palphanum_ s = pcharsat (fun c -> System.Char.IsLetterOrDigit c || c = '_') "alphanumeric character or '_'" s
    
let (<<) p1 p2 : Parser<'b, 'state> = p1 >>= (fun _ -> p2)
let (>>) (p1 : Parser<'a, 'state>) (p2 : Parser<'b, 'state>) : Parser<'a, 'state> = p1 >>= (fun x -> p2 >>= (fun y -> preturn x))
let (++) p1 p2 : Parser<'a * 'b, 'state> = p1 >>= (fun x -> p2 >>= (fun y -> preturn (x, y)))
let R2 p1 p2 : Parser<'a * 'b, 'state> = p1 >>= (fun x -> p2 >>= (fun y -> preturn (x, y)))
let R3 p1 p2 p3 : Parser<'a * 'b * 'c, 'state> = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> preturn (x1, x2, x3))))
let R4 p1 p2 p3 p4 : Parser<'a * 'b * 'c * 'd, 'state> = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> p4 >>= (fun x4 -> preturn (x1, x2, x3, x4)))))
let R5 p1 p2 p3 p4 p5: Parser<'a * 'b * 'c * 'd * 'e, 'state'> = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> p4 >>= (fun x4 -> p5 >>= (fun x5 -> preturn (x1, x2, x3, x4, x5))))))
let R6 p1 p2 p3 p4 p5 p6: Parser<'a * 'b * 'c * 'd * 'e * 'f, 'state> = p1 >>= (fun x1 -> p2 >>= (fun x2 -> p3 >>= (fun x3 -> p4 >>= (fun x4 -> p5 >>= (fun x5 -> p6 >>= (fun x6 -> preturn (x1, x2, x3, x4, x5, x6)))))))



let (<|>) (p1: Parser<'a, 'state>) (p2: Parser<'a, 'state>) : Parser<'a, 'state> =
    fun stream ->
        match p1 stream with
        |   ParserFailure failures1 ->
                let stream' = (failures1, get_loc stream, get_pos stream, get_parser_state stream, get_stream stream)
                (   match p2 stream' with
                    |   ParserFailure failures2 ->
                            ParserFailure (combine_failures (failures1, failures2))
                    |   ParserSuccess (result2, (failures2, loc, pos2, state, stream2)) ->
                            ParserSuccess (result2, (combine_failures (failures1, failures2), loc, pos2, state, stream2)) )
        |   res as ParserSuccess _ -> res

let rec pmany p : Parser<'a list, 'state> =
    let rec F (result, input0) =
        let (failures0, loc, pos0, state0, stream0) = input0
        match p input0 with
        |   ParserSuccess (x, stream') -> F (x :: result, stream')
        |   ParserFailure failures -> ParserSuccess (List.rev result, (combine_failures (failures0, failures), loc, pos0, state0, stream0))
    fun stream -> F ([], stream)

let pmany1 p = ((p ++ pmany p) |>> fun (x, xs) -> x :: xs)

let poption p =
        ( p |>> fun x -> Some x )
    <|> ( preturn None )

let pchoice ps : Parser<'a, 'state> = Seq.reduce (fun (p1: Parser<'a, 'state>) (p2: Parser<'a, 'state>) -> p1 <|> p2) ps

let prun (p: Parser<'a, 'state>) src_loc (state0 :'state) (s: string) =
    match p (parser_input_in_state_from_string src_loc state0 s) with
    |   ParserSuccess (result, _) -> result
    |   ParserFailure failures -> failwith (sprintf "parsing failed: %s" (parser_msg (ParserFailure failures)))

let pstring (s: string) input0 =
    let rec F = function
        |   (result, [], input) ->
                ParserSuccess (implode (List.rev result), input)
        |   (result, c :: cs', input) ->
            (   match pchar c input with
                |   ParserSuccess (x, input') -> F (x :: result, cs', input')
                |   ParserFailure _ ->
                        let (pos, pos0) = (input_abs_pos input, input_abs_pos input0)
                        if get_stream input = []
                        then ParserFailure (combine_failures (Set.singleton (get_pos input0, sprintf "string \"%s\" expected, end-of-stream found" s), get_failures input0))
                        else ParserFailure (combine_failures (Set.singleton (get_pos input0, sprintf "string \"%s\" expected, \"%s\" found" s ((input0 |> get_stream |> implode)[0..pos-pos0] )), get_failures input0)) )
    F ([], [for c in s -> c], input0)

let pwhitespace s =
    ( (pmany (pcharsat (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r')  ("whitespace character (' ', '\\t', '\\n' or '\\r')"))) |>> implode ) s

let pint s =
    ( ((pchar '+' <|> pchar '-') <|> preturn '+')  ++  (pmany1 pdigit)
        >>= fun (s, d) -> preturn (int (implode (s::d))) ) s

let peos s =
    ( function
    |   (failures, loc, pos, state, []) -> ParserSuccess ((), (failures, loc, pos, state, []))
    |   (failures, _, pos, _, s)  -> ParserFailure (combine_failures (Set.singleton (pos, "end-of-stream expected"), failures)) ) s
