(*
##
## Generic Pretty Printer Module
## Adapted from: L.C. Paulson, "ML for the working programmer", p.355
##
*)

module PrettyPrinting

open Common 

type t =
|   Block of t list * int * int
|   String of string
|   Break of int
|   Line_Break

let rec breakdist = function
|   (Block(_,_,len)::es, after) -> len + breakdist (es, after)
|   (String s   :: es, after)   -> String.length s + breakdist (es, after)
|   (Break _    :: es, after)   -> 0
|   (Line_Break :: es, after)   -> 0
|   ([], after)                 -> after

let pr (os : System.IO.TextWriter) margin e =
    let output = fprintf os
    let nspace n = String.replicate n " "
    let space = ref margin
    let blanks n  = output "%s" (nspace n); space := !space - n
    let newline () = output "%s" "\n"; space := margin
    let rec printing = function
    |   ([], _, _) -> ()
    |   (e::es, blockspace, after) ->
            (   match e with
                |   Block (bes, indent, len) -> printing (bes, !space-indent, breakdist(es, after))
                |   String s -> output "%s" s; space := !space - String.length s
                |   Break len ->
                        if len + breakdist (es, after) <= !space
                        then blanks len
                        else (newline(); blanks(margin-blockspace))
                |   Line_Break -> newline(); blanks(margin-blockspace) );
            printing (es, blockspace, after)
    printing ([e], margin, 0)

let toString margin e =
    let str_writer = new System.IO.StringWriter ()
    pr str_writer margin e
    str_writer.ToString ()

let length = function
|   (Block(_, _, len)) -> len
|   (String s)         -> String.length s
|   (Break len)        -> len
|   (Line_Break)       -> 0

let (str, brk, line_brk) = (String, Break, Line_Break)

let blo (indent, es) =
    Block (es, indent, List.fold (fun sum -> fun e -> length e + sum) 0 es)

let blo0 pps = blo (0, pps)
let blo2 pps = blo (2, str "  " :: pps)
let blo4 pps = blo (4, str "    " :: pps)
