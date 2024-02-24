module Updates

open Background
open State

//--------------------------------------------------------------------

type LOCATION = string * VALUE list

type UPDATE = LOCATION * VALUE

type UPDATE_SET = Set<UPDATE>

//--------------------------------------------------------------------

type UPDATE_MAP = Map<string, Map<VALUE list, VALUE>>

let add_update (U : UPDATE_MAP) (u as (loc as (f, args), value): UPDATE) =
    Map.change f
        ( function None -> Some (Map.add args value Map.empty)
                 | Some table -> Some ( if Map.containsKey args table
                                        then if value <> Map.find args table  // deal with conflicting updates
                                             then failwith (sprintf "update set inconsistent at location %A" loc)
                                             else table
                                        else Map.add args value table ) )
        U

let update_set_to_update_map (U : UPDATE_SET) =
    Set.fold add_update Map.empty U

let show_update sign ((f, xs), x) =
    sprintf "%s := %s\n"
        (sprintf "%s (%s)" f (String.concat ", " (List.map Background.value_to_string xs)))
        (value_to_string x)

let show_update_set sign (U :UPDATE_SET) =
    (Set.map (show_update sign) U |> String.concat "") + "\n"

//--------------------------------------------------------------------

let consistent (U : UPDATE_SET) =
    try let x = update_set_to_update_map U
        in true
    with Failure _ -> false
    
//--------------------------------------------------------------------

let locations (U : UPDATE_SET) : Set<LOCATION> =
    Set.map (fun (loc, value) -> loc) U

//--------------------------------------------------------------------

let seq_merge_2 (U : UPDATE_SET) (V : UPDATE_SET) =
    if not (consistent U)
    then U
    else let U_reduced = Set.filter (fun (loc, _) -> not (Set.contains loc (locations V))) U
         in Set.union U_reduced V

let seq_merge_n (Us : UPDATE_SET list) : UPDATE_SET =
    List.fold seq_merge_2 Set.empty Us

//--------------------------------------------------------------------

// type DYNAMIC_STATE = Map<string, Map<VALUE list, VALUE>>

let apply_update_map (S : STATE) (U : UPDATE_MAP) =
    let update_dynamic_function_table (f_table : Map<VALUE list, VALUE>) (updates_of_f : Map<VALUE list, VALUE>) =
            Map.fold (fun table -> fun args -> fun value -> Map.add args value table) f_table updates_of_f
    let apply_to_dynamic_state (dS : DYNAMIC_STATE) (U : UPDATE_MAP) =
            Map.fold
                ( fun dS_ -> fun f -> fun updates_of_f ->
                    Map.change f
                        (function None -> Some (update_dynamic_function_table Map.empty updates_of_f)
                                | Some f_table -> Some (update_dynamic_function_table f_table updates_of_f)) dS_ )
                dS U
    in  { _signature = S._signature; _static = S._static; _dynamic = apply_to_dynamic_state S._dynamic U }

let apply_update_set S U =
    apply_update_map S (update_set_to_update_map U)

let sequel_state = apply_update_set

