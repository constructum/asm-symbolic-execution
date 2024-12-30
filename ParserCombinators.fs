module ParserCombinators

open Common

type SrcPos = { abs : int; line : int; col : int; }

type SrcLoc =
|   File of string ref      // name of file containing source code
|   Strg of string ref      // string containing source code

let src_loc_to_string = function
|   File f -> sprintf "%s" !f
|   Strg s -> sprintf "in string '%s'" !s

type SrcReg = SrcLoc * SrcPos * SrcPos     // file name, position before region, position after region

let src_reg_to_string = function
    (loc, pos1, pos2) -> sprintf "%s: [%d:%d]-[%d:%d]:" (src_loc_to_string loc) pos1.line pos1.col pos2.line pos2.col

let opt_src_reg_to_string = function
|   None -> ""
|   Some reg -> sprintf "%s\n" (src_reg_to_string reg)

let merge_src_reg (reg1 as (loc1, pos11, pos12) : SrcReg) (reg2 as (loc2, pos21, pos22) : SrcReg) =
    if loc1 <> loc2
    then failwith (sprintf "merge_regions: locations of regions do not match (%s, %s)" (src_loc_to_string loc1) (src_loc_to_string loc2))
    else (loc1, pos11, pos22)

let merge_opt_src_reg (reg1 : SrcReg option) (reg2 : SrcReg option) =
    match (reg1, reg2) with
    |   (Some (loc1, pos11, pos12), Some (loc2, pos21, pos22)) -> Some (merge_src_reg (loc1, pos11, pos12) (loc2, pos21, pos22))
    |   (Some reg1, None) -> Some reg1
    |   (None, Some reg2) -> Some reg2
    |   (None, None) -> None

let initial_position = { abs = 0; line = 1; col = 1; }

type FailedAt = SrcPos * string

let failure (pos, strg) = Set.singleton (pos, strg)

let combine_failures (failures1 : Set<FailedAt>, failures2 : Set<FailedAt>) =
    if Set.isEmpty failures1 then failures2
    else if Set.isEmpty failures2 then failures1
    else let compare ((pos1, _) : SrcPos * string) ((pos2, _) : SrcPos * string) = -(compare pos1.abs pos2.abs)
         let failures = Set.union failures1 failures2
         if Set.isEmpty failures
         then   Set.empty
         else   let es = Seq.sortWith compare failures
                let max_pos = (fst (Seq.head es)).abs
                let rec F result es =
                    if Seq.isEmpty es
                    then result
                    else let e = Seq.head es
                         if (fst e).abs = max_pos then F (e :: result) (Seq.tail es) else result
                F [] es |> Set.ofSeq

let failure_msg (failures : Set<FailedAt>) =
    let output_failures = String.concat "\n" (Set.toList failures >>| fun (pos, msg) -> $"[{pos.line}:{pos.col}] unexpected '{msg}'")
    sprintf $"parsing failed:\n{output_failures}"


type 'parser_state ParserInput = Set<FailedAt> * SrcLoc * SrcPos * 'parser_state * char list             // position, stream

exception SyntaxError of string * Set<FailedAt>

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

let combine_loc_pos (loc0, pos0) (loc1, pos1) =
    if loc0 <> loc1
    then failwith (sprintf "combine_loc_pos: locations do not match (%s, %s)" (src_loc_to_string loc0) (src_loc_to_string loc1))
    else (loc0, pos0, pos1)

let (>>==) (p: Parser<'a, 'state>) (f: (SrcLoc * SrcPos * SrcPos) -> 'state -> 'a -> Parser<'b, 'state>) : Parser<'b, 'state> =
    fun input ->
        let (_, loc0, pos0, state0, _) = input
        match p input with
        |   ParserSuccess(x, rest) ->
                let (_, loc1, pos1, state1, _) = rest
                let (loc, pos_start, pos_end) = combine_loc_pos (loc0, pos0) (loc1, pos1)
                (f (loc, pos_start, pos_end) state0 x) rest
        |   ParserFailure failures -> ParserFailure failures

let no_backtrack (context : string) (p: Parser<'a, 'state>) : Parser<'a, 'state> =
    fun input ->
        let (_, loc0, pos0, _, _) = input
        match p input with
        |   ParserSuccess(x, rest) -> ParserSuccess(x, rest)
        |   ParserFailure failures -> raise (SyntaxError (context, failures))

let chg_state (f :'a -> 'state -> 'state) (x :'a) : Parser<'a, 'state> =
    fun (input as (failures, loc, pos, state, stream)) ->
        ParserSuccess (x, (failures, loc, pos, f x state, stream))

// let with_state (f :'a -> 'state -> 'state) (x :'a) (p : Parser<'a, 'state>): Parser<'a, 'state> =
//     fun (input as (failures, loc, pos, state, stream)) ->
//         p (failures, loc, pos, f x state, stream)

let (||>>) (p: Parser<'a, 'state1>) (f: 'state1 -> 'a -> 'state2) (s : ParserInput<'state1>): ParserResult<'a, 'state2> =
    match p s with
    |   ParserSuccess (result, (failure', loc, pos', state', stream')) -> ParserSuccess (result, (failure', loc, pos', f state' result, stream'))
    |   ParserFailure failures -> ParserFailure failures


let parser_msg = function
|   ParserSuccess _ -> "parsing succeeded"
|   ParserFailure failures -> failure_msg failures

let preturn x : Parser<'a, 'state> = fun input -> ParserSuccess (x, input)
let pfail_msg msg : Parser<'a, 'state> = fun input -> ParserFailure (combine_failures (failure (get_pos input, msg), get_failures input))
//msg
    
let (|>>) p f : Parser<'b, 'state> = p >>= (fun x -> preturn (f x))

let (|||>>) p f : Parser<'b, 'state> = p >>== (fun (loc0, pos0, pos1) state0 x -> preturn (f (loc0, pos0, pos1) state0 x))


let (||||>>) p f : Parser<'b, 'state> =
    p >>== (fun (loc0, pos0, pos1) state0 x ->
                let (result, state1) = f (loc0, pos0, pos1) state0 x
                fun (failures, loc, pos, _, stream)  -> ParserSuccess (result, (failures, loc, pos, state1, stream)))

let pcharsat c_pred expected : Parser<char, 'state> =
    fun input ->
        match parser_input_getc input with
        |   (Some c, input') ->
                if c_pred c
                then ParserSuccess (c, input')
                else // ... is this the best way to handle this?
                     ParserFailure (get_failures input)
        |   (None, _) ->
                // ... is this the best way to handle this?
                ParserFailure (get_failures input)

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
    fun input ->
        match p1 input with
        |   ParserFailure failures1 ->
                let input' = (failures1, get_loc input, get_pos input, get_parser_state input, get_stream input)
                (   match p2 input' with
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
                        then ParserFailure (combine_failures (failure (get_pos input0, "<end-of-stream>"), get_failures input0))
                        else ParserFailure (combine_failures (failure (get_pos input0, ((input0 |> get_stream |> implode)[0..pos-pos0] )), get_failures input0)) )
    F ([], [for c in s -> c], input0)

let pwhitespace s =
    ( (pmany (pcharsat (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r')  ("whitespace character (' ', '\\t', '\\n' or '\\r')"))) |>> implode ) s

let pint s =
    ( ((pchar '+' <|> pchar '-') <|> preturn '+')  ++  (pmany1 pdigit)
        >>= (fun (s, d) -> preturn (int (implode (s::d)))) ) s

let peos s =
    ( function
    |   (failures, loc, pos, state, []) -> ParserSuccess ((), (failures, loc, pos, state, []))
    |   (failures, _, pos, _, s)  -> ParserFailure (combine_failures (failure (pos, "not <end-of-stream>"), failures)) ) s
