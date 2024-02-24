module SymbUpdates

open Common
open Background
open AST
open SymbState

//--------------------------------------------------------------------

type LOCATION = string * VALUE list

type S_UPDATE = LOCATION * TERM
type S_UPDATE_SET = Set<S_UPDATE>
type S_UPDATE_MAP = Map<string, Map<VALUE list, TERM>>

let add_s_update (U : S_UPDATE_MAP) (u as (loc as (f, args), value): S_UPDATE) =
    Map.change f
        ( function None -> Some (Map.add args value Map.empty)
                 | Some table -> Some ( if Map.containsKey args table
                                        then if value <> Map.find args table  // deal with conflicting updates
                                             then failwith (sprintf "update set inconsistent at location %A" loc)
                                             else table
                                        else Map.add args value table ) )
        U

let s_update_set_to_s_update_map (U : S_UPDATE_SET) =
    Set.fold add_s_update Map.empty U

let show_s_update sign ((f, xs), t) =
    sprintf "%s := %s"
        (if List.isEmpty xs then f else sprintf "%s (%s)" f (String.concat ", " (List.map value_to_string xs)))
        (PrettyPrinting.toString 80 (pp_term sign t))

let show_s_update_set sign (U :S_UPDATE_SET) =
    "{ " +
    ( Set.toList U >>| show_s_update sign
        |> String.concat ", "   ) +
    " }"

//--------------------------------------------------------------------

let consistent (U : S_UPDATE_SET) =
    try let x = s_update_set_to_s_update_map U
        in true
    with Failure _ -> false
    
//--------------------------------------------------------------------

let locations (U : S_UPDATE_SET) : Set<LOCATION> =
    Set.map (fun (loc, value) -> loc) U

//--------------------------------------------------------------------

let seq_merge_2 (U : S_UPDATE_SET) (V : S_UPDATE_SET) =
    if not (consistent U)
    then U
    else let U_reduced = Set.filter (fun (loc, _) -> not (Set.contains loc (locations V))) U
         in Set.union U_reduced V

let seq_merge_n (Us : S_UPDATE_SET list) : S_UPDATE_SET =
    List.fold seq_merge_2 Set.empty Us

//--------------------------------------------------------------------

// type DYNAMIC_STATE = Map<string, Map<VALUE list, VALUE>>

let apply_s_update_map (S : S_STATE) (U : S_UPDATE_MAP) =
    let update_dynamic_function_table (f_table : Map<VALUE list, TERM>) (updates_of_f : Map<VALUE list, TERM>) =
            Map.fold (fun table -> fun args -> fun value -> Map.add args value table) f_table updates_of_f
    let apply_to_s_dynamic_state (dS : S_DYNAMIC_STATE) (U : S_UPDATE_MAP) =
            Map.fold
                ( fun dS_ -> fun f -> fun updates_of_f ->
                    Map.change f
                        (function None -> Some (update_dynamic_function_table Map.empty updates_of_f) 
                                | Some f_table -> Some (update_dynamic_function_table f_table updates_of_f)) dS_ )
                dS U
    in  { _signature = S._signature; _static = S._static; _dynamic = apply_to_s_dynamic_state S._dynamic U }

let apply_s_update_set S U =
    apply_s_update_map S (s_update_set_to_s_update_map U)

let sequel_s_state = apply_s_update_set

