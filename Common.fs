module Common

open System.Diagnostics

let (>>|) xs f = List.map f xs
let explode (s:string) : char list = [for c in s -> c]
let implode (xs : char list) : string = System.String.Concat xs

let write s = printf "%s" s
let writeln s = printf "%s\n" s

let write_err s = fprintf stderr "%s" s
let writeln_err s = fprintf stderr "%s\n" s

let map_override m1 m2 =
    Map.fold (fun m k v -> Map.add k v m) m1 m2

let map_merge m1 m2 =
    Map.fold (fun m k v -> Map.add k (Set.union (try Map.find k m with _ -> Set.empty) v) m) m1 m2

let map_combine combine_fct zero m1 m2 =
    Map.fold (fun m k v -> Map.add k (combine_fct (try Map.find k m with _ -> zero) v) m) m1 m2

let set_product S1 S2 =
    Set.unionMany
        (Set.map (fun (S, y) -> Set.map (fun x -> (x, y)) S)
            (Set.unionMany (Set.map (fun x -> Set.singleton (S1, x)) S2)))

let time f args = 
    let capture_cpu_time (proc : Process) =
        (proc.TotalProcessorTime, proc.UserProcessorTime, proc.PrivilegedProcessorTime)
    let measure_cpu_time (proc : Process) (cpu0, usr0, sys0) =
        let (cpu1, usr1, sys1) = capture_cpu_time proc
        ( (cpu1 - cpu0).TotalMilliseconds, (usr1 - usr0).TotalMilliseconds, (sys1 - sys0).TotalMilliseconds )
    let timer = new Stopwatch()
    let proc = Process.GetCurrentProcess()
    let (cpu0, usr0, sys0) = capture_cpu_time proc
    timer.Start()
    try
        let result = f args
        let elapsed_time = timer.ElapsedMilliseconds
        let (cpu, usr, sys) = measure_cpu_time proc (cpu0, usr0, sys0)
        (Some result, None, elapsed_time, cpu, usr, sys)
    with ex ->
        let elapsed_time = timer.ElapsedMilliseconds
        let (cpu, usr, sys) = measure_cpu_time proc (cpu0, usr0, sys0)
        //(None, Some ex, elapsed_time, cpu, usr, sys)
        reraise ()

let readfile filename =
    try System.IO.File.ReadAllText filename
    with   :? System.IO.IOException as ex -> failwith (sprintf "error while trying to read file '%s'\nI/O error:\n%s\n" filename ex.Message)
         | _ -> failwith (sprintf "readfile('%s'): unrecognized exception" filename)

