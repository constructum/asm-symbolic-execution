module CLI

open Common

let usage () =
    write
        ( [ 
            #if DEBUG
            "Usage: dotnet run [OPTION]..."
            #else
            "Usage: asm-symbolic-execution [OPTION]..."
            #endif
            ""
            "Options:"
            "  -str <strg>   load definitions specified in string <strg>"
            "                  into the top-level environment"
            "  -file <file>  load definitions contained in file <filename>"
            "                  into top-level environment"
            ""
            "  -asmeta       use AsmetaL as input language"
            ""
            "  -symbolic     symbolic execution of 'Main' rule (default)"
            "  -nonsymbolic  execute 'Main' rule non-symbolically"
            ""
            "  -turbo2basic  turbo ASM to basic ASM transformation"
            "                (all non-static functions are uninterpreted)"
            ""
            "  -nosmt        do not use SMT solver"
            ""
            "  -license      display license information"
            "" ] |> String.concat "\n" )

let license () =
    write
        ( [ ""
            "MIT License"
            ""
            "Copyright (c) 2024 Giuseppe Del Castillo"
            ""
            "Permission is hereby granted, free of charge, to any person obtaining a copy"
            "of this software and associated documentation files (the \"Software\"), to deal"
            "in the Software without restriction, including without limitation the rights"
            "to use, copy, modify, merge, publish, distribute, sublicense, and/or sell"
            "copies of the Software, and to permit persons to whom the Software is"
            "furnished to do so, subject to the following conditions:"
            ""
            "The above copyright notice and this permission notice shall be included in all"
            "copies or substantial portions of the Software."
            ""
            "THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR"
            "IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,"
            "FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE"
            "AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER"
            "LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,"
            "OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE"
            "SOFTWARE."
            ""
            "--------------------------------------------------------------------"
            ""
            "THIRD-PARTY LIBRARIES"
            ""
            "-----"
            ""
            "Z3"
            "Copyright (c) Microsoft Corporation"
            "All rights reserved. "
            "MIT License"
            ""
            "Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the \"Software\"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:"
            ""
            "The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software."
            ""
            "THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE."
            ""
            "" ]  |> String.concat "\n" )


let exec_symbolic symb_exec_fct main_rule_name =
    let R_in = try AST.get_rule main_rule_name (!TopLevel.rules) with _ -> failwith $"rule '{main_rule_name}' not defined"
    let print_time (cpu, usr, sys) =
        writeln $"\n--- CPU time: {((float cpu) / 1000.0)}s (usr: {((float usr) / 1000.0)}s, sys: {((float sys) / 1000.0)}s)"
    match Common.time symb_exec_fct R_in with
    |   (Some (no_of_leaves, R_out), _, _, cpu, usr, sys) ->
            write "\n\n--- generated rule:\n"
            PrettyPrinting.pr stdout 80 (AST.pp_rule (!TopLevel.signature) R_out)
            write $"\n\n--- size of generated rule: {(AST.rule_size R_out)}\n"
            write $"\n--- number of leaves in decision tree: {no_of_leaves}\n" // (no_of_leaves)
            print_time (cpu, usr, sys)
    |   (_, Some ex, _, cpu, usr, sys) ->
            print_time (cpu, usr, sys)
            write "\n\n--- execution failed with exception:\n"
            raise ex
    |   _ -> failwith "Failure: no result and no exception"

let exec_nonsymbolic main_rule_name =
    let R = try AST.get_rule main_rule_name (!TopLevel.rules) with _ -> failwith $"rule '{main_rule_name}' not defined"
    let R_pretty = R |> AST.pp_rule (!TopLevel.signature) |> PrettyPrinting.toString 80
    writeln $"{R_pretty}\n\n  -->\n"
    Updates.show_update_set sign (Eval.eval_rule R (!TopLevel.initial_state, Map.empty)) |> writeln

let CLI_with_ex(args) =
    let n = Array.length args
    if n = 0
    then usage (); 0
    else
        let symbolic = ref true
        let turbo2basic = ref false
        let asmeta_flag = ref false
        let main_rule_name = ref "Main"
        let rec parse_arguments i = 
            let load option_str load_fct s =
                if i + 1 < n
                then let s = args[i+1]
                     let len = String.length s
                     writeln_err $"{option_str} {s}"
                     load_fct (args[i+1])
                else writeln_err $"parameter missing after {option_str}"
            if i < n then 
                match args[i] with
                |   "-license"         -> license (); exit 0
                |   "-asmeta"          -> asmeta_flag := true; main_rule_name := "r_Main"; parse_arguments (i+1)
                |   "-symbolic"        -> symbolic := true;    parse_arguments (i+1)
                |   "-nonsymbolic"     -> symbolic := false;   parse_arguments (i+1)
                |   "-turbo2basic"     -> turbo2basic := true; parse_arguments (i+1)
                |   "-nosmt"           -> SymbEval.use_smt_solver := false; parse_arguments (i+1)
                |   "-str"  -> load "-str"  (TopLevel.loadstr !asmeta_flag) (args[i+1]); parse_arguments (i+2)
                |   "-file" -> load "-file" (TopLevel.loadfile !asmeta_flag) (args[i+1]); parse_arguments (i+2)
                |   s -> writeln_err $"unknown option: {s}"; exit 1
        parse_arguments 0
        if !turbo2basic
        then exec_symbolic SymbEval.symbolic_execution_for_turbo_asm_to_basic_asm_transformation (!main_rule_name)
        else if !symbolic
        then exec_symbolic SymbEval.symbolic_execution (!main_rule_name)
        else exec_nonsymbolic (!main_rule_name)
        0

let CLI(args) =
    try
        CLI_with_ex(args)
    with
        Failure s -> writeln_err $"exception:\n{s}"; 1