module CLI

open Common

let usage () =
    printf "%s"
        ( [ "Usage: dotnet run [OPTION]..."
            ""
            "Options:"
            "  -str <strg>   load definitions specified in string <strg>"
            "                  into the top-level environment"
            "  -file <file>  load definitions contained in file <filename>"
            "                  into top-level environment"
            ""
            "  -symbolic     symbolic execution of 'Main' rule (default)"
            "  -nonsymbolic  execute 'Main' rule non-symbolically"
            ""
            "  -turbo2basic  turbo ASM to basic ASM transformation"
            "                (all non-static functions are uninterpreted)"
            ""
            "  -nosmt        do not use SMT solver"
            ""
            "" ] |> String.concat "\n" )

let exec_symbolic symb_exec_fct =
    let R_in = try AST.get_rule "Main" (!TopLevel.rules) with _ -> failwith "rule 'Main' not defined"
    let print_time (cpu, usr, sys) =
        printfn "\n--- CPU time: %.3fs (usr: %.3fs, sys: %.3fs)"
            ((float cpu) / 1000.0) ((float usr) / 1000.0) ((float sys) / 1000.0)
    match Common.time symb_exec_fct R_in with
    |   (Some (no_of_leaves, R_out), _, _, cpu, usr, sys) ->
            printf "\n\n--- generated rule:\n"
            PrettyPrinting.pr stdout 80 (AST.pp_rule (!TopLevel.signature) R_out)
            printf "\n\n--- size of generated rule: %d\n" (AST.rule_size R_out)
            printf "\n--- number of leaves in decision tree: %d\n" (no_of_leaves)
            print_time (cpu, usr, sys)
    |   (_, Some ex, _, cpu, usr, sys) ->
            print_time (cpu, usr, sys)
            printf "\n\n--- execution failed with exception:\n"
            raise ex
    |   _ -> failwith "Failure: no result and no exception"

let exec_nonsymbolic () =
    let R = try AST.get_rule "Main" (!TopLevel.rules) with _ -> failwith "rule 'Main' not defined"
    printfn "%s\n\n  -->\n" (R |> AST.pp_rule (!TopLevel.signature) |> PrettyPrinting.toString 80)
    Updates.show_update_set sign (Eval.eval_rule R (!TopLevel.initial_state, Map.empty)) |> printfn "%s\n"

let CLI_with_ex(args) =
    let n = Array.length args
    if n = 0
    then usage (); 0
    else
        let symbolic = ref true
        let turbo2basic = ref false
        let rec parse_arguments i = 
            let load option_str load_fct s =
                if i + 1 < n
                then let s = args[i+1]
                     let len = String.length s
                     fprintfn stderr "%s '%s'" option_str s
                     load_fct (args[i+1])
                else fprintfn stderr "parameter missing after %s" option_str
            if i < n then 
                match args[i] with
                |   "-symbolic"        -> symbolic := true;    parse_arguments (i+1)
                |   "-nonsymbolic"     -> symbolic := false;   parse_arguments (i+1)
                |   "-turbo2basic"     -> turbo2basic := true; parse_arguments (i+1)
                |   "-nosmt"           -> SymbEval.use_smt_solver := false; parse_arguments (i+1)
                |   "-str"  -> load "-str"  TopLevel.loadstr  (args[i+1]); parse_arguments (i+2)
                |   "-file" -> load "-file" TopLevel.loadfile (args[i+1]); parse_arguments (i+2)
                |   s -> fprintf stderr "unknown parameter: %s" s
        parse_arguments 0
        if !turbo2basic
        then exec_symbolic SymbEval.symbolic_execution_for_turbo_asm_to_basic_asm_transformation
        else if !symbolic
        then exec_symbolic SymbEval.symbolic_execution
        else exec_nonsymbolic ()
        0

let CLI(args) =
    try
        CLI_with_ex(args)
    with
        Failure s -> fprintfn stderr "exception:\n%s" s; 1