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
            "  -str <strg>    load definitions specified in string <strg>"
            "                   into the top-level environment"
            "  -file <file>   load definitions contained in file <file>"
            "                   into top-level environment"
            ""
            "  -asmeta        use AsmetaL as input language"
            "  -init <state>  (AsmetaL only) start from initial state named <state>"
            "  -invcheck <n>  (AsmetaL only) check invariants during symbolic execution"
            "                   for at most <n> steps or indefinitely, if <n> not specified"
            ""
            "  -symbolic      symbolic execution of 'Main' rule (default)"
            "  -steps <n>     symbolic execution of <n> steps of 'Main' rule"
            "                   starting from initial state (default: n = 1)"
            ""
            "  -nonsymbolic   execute 'Main' rule non-symbolically"
            ""
            "  -turbo2basic   turbo ASM to basic ASM transformation"
            "                   (all non-static functions are uninterpreted)"
            ""
            "  -nosmt         do not use SMT solver"
            ""
            "  -license       display license information"
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

let exec_symbolic (symb_exec_fct : AST.RULE -> 'a * AST.RULE) (main_rule_name : string) : unit =
    let (_, R_in) = try AST.get_rule main_rule_name (TopLevel.rules ()) with _ -> failwith $"rule '{main_rule_name}' not defined"
    match Common.time symb_exec_fct R_in with
    |   (Some (no_of_leaves, R_out), _, _, cpu, usr, sys) ->
            write "\n\n--- generated rule:\n"
            PrettyPrinting.pr stdout 80 (AST.pp_rule (TopLevel.signature ()) R_out)
            write $"\n\n--- size of generated rule: {(AST.rule_size R_out)}\n"
            write $"\n--- number of leaves in decision tree: {no_of_leaves}\n"
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n" 
            print_time (cpu, usr, sys)
    |   (_, Some ex, _, cpu, usr, sys) ->
            print_time (cpu, usr, sys)
            write "\n\n--- execution failed with exception:\n"
            raise ex
    |   _ -> failwith "failure: no result and no exception\n"

let simple_exec exec_fct main_rule_name =
    let (_, R_in) = try AST.get_rule main_rule_name (TopLevel.rules ()) with _ -> failwith $"rule '{main_rule_name}' not defined"
    match Common.time exec_fct R_in with
    |   (Some _, _, _, cpu, usr, sys) ->
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n" 
            print_time (cpu, usr, sys)
    |   (_, Some ex, _, cpu, usr, sys) ->
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n" 
            print_time (cpu, usr, sys)
            write "\n\n--- execution failed with exception:\n"
            raise ex
    |   _ ->
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n" 
            failwith "failure: no result and no exception\n"

let exec_nonsymbolic main_rule_name =
    let (args, R) = try AST.get_rule main_rule_name (TopLevel.rules ()) with _ -> failwith $"rule '{main_rule_name}' not defined"
    let R_pretty = R |> AST.pp_rule (TopLevel.signature ()) |> PrettyPrinting.toString 80
    writeln $"{R_pretty}\n\n  -->\n"
    Updates.show_update_set sign (Eval.eval_rule R (TopLevel.initial_state (), Map.empty)) |> writeln

let loadfile (asmeta_flag : bool) initial_state_name relative_path_of_file =
    let base_path = System.IO.Directory.GetCurrentDirectory ()
    let full_path = System.IO.Path.GetFullPath (relative_path_of_file, base_path)
    // move to directory where the loaded file is located
    // in order to correctly resolve the relative paths of the imported modules
    System.IO.Directory.SetCurrentDirectory (System.IO.Path.GetDirectoryName full_path)
    let result = TopLevel.loadfile asmeta_flag initial_state_name full_path
    // move to original directory (where the CLI was called)
    System.IO.Directory.SetCurrentDirectory base_path
    result


type ObjectToLoad =
|   Str of string
|   File of string

let CLI_with_ex(args) =
    let n = Array.length args
    if n = 0
    then usage (); 0
    else
        let symbolic = ref true
        let steps = ref 1
        let turbo2basic = ref false
        let asmeta_flag = ref false
        let invcheck = ref false
        let invcheck_steps = ref None
        let objects_to_load = ref []
        let main_rule_name = ref "Main"
        let initial_state_name = ref None
        let rec parse_arguments i = 
            if i < n then 
                match args[i] with
                |   "-license"     -> license (); exit 0
                |   "-asmeta"      -> asmeta_flag := true; main_rule_name := "r_Main"; parse_arguments (i+1)
                |   "-init"        -> if i+1 < n
                                      then  initial_state_name := Some args[i+1]; parse_arguments (i+2)
                                      else writeln_err "-init requires an argument"; exit 1
                |   "-invcheck"    -> invcheck := true
                                      if i+1 < n
                                      then  try         invcheck_steps := Some (int (args[i+1]))
                                                        parse_arguments (i+2)
                                            with _ ->   invcheck_steps := None
                                                        parse_arguments (i+1)
                |   "-symbolic"    -> symbolic := true;    parse_arguments (i+1)
                |   "-steps"       -> steps := int (args[i+1]); parse_arguments (i+2)
                |   "-nonsymbolic" -> symbolic := false;   parse_arguments (i+1)
                |   "-turbo2basic" -> turbo2basic := true; parse_arguments (i+1)
                |   "-nosmt"       -> SymbEval.use_smt_solver := false; parse_arguments (i+1)
                |   "-str"         -> fprintf stderr "-str %s " args[i+1]; objects_to_load := Str args[i+1] :: !objects_to_load; parse_arguments (i+2)
                |   "-file"        -> fprintf stderr "-file %s " args[i+1]; objects_to_load := File args[i+1] :: !objects_to_load; parse_arguments (i+2)
                |   s -> writeln_err $"unknown option: {s}"; exit 1
        let rec load_everything L =
            match L with
            |   [] -> () 
            |   (Str s) :: rest  -> TopLevel.loadstr !asmeta_flag !initial_state_name s; load_everything rest
            |   (File f) :: rest -> loadfile !asmeta_flag !initial_state_name f; load_everything rest
        try parse_arguments 0 with _ -> usage (); exit 1
        let _ = TopLevel.init !asmeta_flag
        load_everything (List.rev !objects_to_load)
        // !!! tbd: for AsmetaL the main rule name it not always 'r_Main', but should be set according to the content of the ASM file
        if !invcheck
        then simple_exec (SymbEval.symbolic_execution_for_invariant_checking (!invcheck_steps)) (!main_rule_name)
        else if !turbo2basic
        then exec_symbolic SymbEval.symbolic_execution_for_turbo_asm_to_basic_asm_transformation (!main_rule_name)
        else if !symbolic
        then exec_symbolic (fun R -> SymbEval.symbolic_execution R (!steps)) (!main_rule_name)
        else exec_nonsymbolic (!main_rule_name)
        0

let CLI(args) =
    try
        CLI_with_ex(args)
    with
    |   Parser.Error (fct, reg, err)  -> writeln_err ("\n" + Parser.error_msg (fct, reg, err)); 1
    |   AsmetaL.Error (fct, reg, err) -> writeln_err ("\n" + AsmetaL.error_msg (fct, reg, err)); 1
    |   SymbUpdates.Error (mdl, fct, err) -> writeln_err ("\n" + SymbUpdates.error_msg (mdl, fct, err)); 1
    |   Failure s -> writeln_err $"\nexception:\n{s}"; 1
