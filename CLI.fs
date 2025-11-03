module CLI

open Common
open IndMap

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
            "  -asmeta-dag    use AsmetaL with experimental DAG-based symbolic execution"
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

let exec_symbolic (sign : Signature.SIGNATURE) (symb_exec_fct : 'rule -> 'a * 'rule) (R_in : 'rule) (rule_to_string, rule_size) : unit =
//    let (_, R_in) = try AST.get_rule main_rule_name (TopLevel.rules ()) with _ -> failwith $"rule '{main_rule_name}' not defined"
    match Common.time symb_exec_fct R_in with
    |   (Some (no_of_leaves, R_out), _, _, cpu, usr, sys) ->
            write "\n\n--- generated rule:\n"
            PrettyPrinting.pr stdout 80 (rule_to_string R_out)
            write $"\n\n--- size of generated rule: {(rule_size R_out)}\n"
            write $"\n--- number of leaves in decision tree: {no_of_leaves}\n"
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n"     //!!! in DAG version, Toplevel should not be used
            print_time (cpu, usr, sys)
    |   (_, Some ex, _, cpu, usr, sys) ->
            print_time (cpu, usr, sys)
            write "\n\n--- execution failed with exception:\n"
            raise ex
    |   _ -> failwith "failure: no result and no exception\n"

let simple_exec exec_fct (R_in : 'rule) =
    //let (_, R_in) = try AST.get_rule main_rule_name (TopLevel.rules ()) with _ -> failwith $"rule '{main_rule_name}' not defined"
    match Common.time exec_fct R_in with
    |   (Some _, _, _, cpu, usr, sys) ->
            write $"\n--- number of SMT solver calls: {!TopLevel.smt_ctx.ctr}\n"     //!!! in DAG version, Toplevel should not be used
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
        let asmeta_dag_flag = ref false
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
                |   "-asmeta-dag"  -> asmeta_dag_flag := true; main_rule_name := "r_Main"; parse_arguments (i+1)
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
        let load_everything L =
            TopLevel.init (!asmeta_flag || !asmeta_dag_flag)  // use AsmetaL parser
            let rec loadfiles = function
            |   [] -> () 
            |   (Str s) :: rest  -> TopLevel.loadstr !asmeta_flag !initial_state_name s; loadfiles rest
            |   (File f) :: rest -> loadfile !asmeta_flag !initial_state_name f; loadfiles rest
            loadfiles L
        try parse_arguments 0 with _ -> usage (); exit 1
        if !asmeta_dag_flag  // experimental AsmetaL DAG mode
        then
            if !asmeta_flag
            then writeln_err "AsmetaL DAG mode is not compatible with regular AsmetaL mode"; exit 1
            else if !turbo2basic
            then writeln_err "'-turbo2basic' option not yet supported with '-asmeta-dag"; exit 1
            else
                asmeta_flag := true
                load_everything (List.rev !objects_to_load)
                let sign = TopLevel.signature ()
                let (_, R_in) = try AST.get_rule !main_rule_name (TopLevel.rules ()) with _ -> failwith ("rule '" + !main_rule_name + " not defined")
                let C = Engine.new_engine (TopLevel.signature (), TopLevel.initial_state (), TopLevel.macros (), TopLevel.rules (), TopLevel.invariants (), TopLevel.smt_ctx)
                let R_in = Engine.convert_rule C R_in
                if !invcheck
                then simple_exec (Engine.symbolic_execution_for_invariant_checking C !invcheck_steps) R_in
                else exec_symbolic sign (fun (R : Engine.RULE) -> Engine.symbolic_execution C R (!steps)) R_in (Engine.pp_rule C, Engine.rule_size C)
                write $"\n--- number of generated terms (term table size): {(Engine.get_engine' C).terms |> IndMap.count}\n" 
                write $"--- number of generated rules (rule table size): {(Engine.get_engine' C).rules |> IndMap.count}\n" 
                // fprintf stderr "%s" (DAG.show_fct_tables C)  // for debugging purposes   Count
                ()
        else  // all other options
            // !!! tbd: for AsmetaL the main rule name it not always 'r_Main', but should be set according to the content of the ASM file
            load_everything (List.rev !objects_to_load)
            let sign = TopLevel.signature ()
            let exec_symbolic = exec_symbolic sign
            let (_, R_in) = try AST.get_rule (!main_rule_name) (TopLevel.rules ()) with _ -> failwith ("rule '" + !main_rule_name + "' not defined")
            if !invcheck
            then simple_exec (SymbEval.symbolic_execution_for_invariant_checking !invcheck_steps) R_in
            else if !turbo2basic
            then exec_symbolic SymbEval.symbolic_execution_for_turbo_asm_to_basic_asm_transformation R_in (AST.pp_rule sign, AST.rule_size)
            else if !symbolic
            then exec_symbolic (fun R -> SymbEval.symbolic_execution R (!steps)) R_in (AST.pp_rule sign, AST.rule_size)
            else exec_nonsymbolic (!main_rule_name)
        0

let raw_exceptions = false

let CLI(args) =
    if raw_exceptions then
        CLI_with_ex args
    else
        try
            CLI_with_ex(args)
        with
        |   ex as Parser.Error (fct, reg, err)  -> writeln_err ("\n" + Parser.error_msg (fct, reg, err)); -1
        |   ex as AsmetaL.Error (fct, reg, err) -> writeln_err ("\n" + AsmetaL.error_msg (fct, reg, err)); -1
        |   ex as SymbUpdates.Error (mdl, fct, err) -> writeln_err ("\n" + SymbUpdates.error_msg (mdl, fct, err)); -1
        |   ex as Failure s -> writeln_err $"\nexception:\n{s}"; -1



