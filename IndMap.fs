module IndMap

open System.Collections.Generic

/// <summary>
/// IndMap is an indexed map that stores objects with their attributes and provides efficient lookups.
/// </summary>
/// <typeparam name="'obj">Type of objects being stored, must support equality</typeparam>
/// <typeparam name="'attrs">Type of attributes associated with each object</typeparam>
type IndMap<'obj, 'attrs when 'obj : equality>() =
    // Dictionary for fast lookups from object to index
    let index = new Dictionary<'obj, int>(HashIdentity.Structural)
    
    // List for storing objects with their attributes
    let table = new ResizeArray<'obj * 'attrs>()
    
    /// <summary>
    /// Gets the current count of items in the map
    /// </summary>
    member this.Count = table.Count
    
    /// <summary>
    /// Returns a string representation of the index dictionary
    /// </summary>
    /// <param name="obj_to_string">Function to convert objects to string representation</param>
    /// <returns>String showing mapping from objects to indices</returns>
    member this.show_index(obj_to_string: 'obj -> string) =
        index
        |> Seq.toList
        |> List.map (fun obj_value -> sprintf "%s -> %d" (obj_to_string obj_value.Key) obj_value.Value)
        |> String.concat "\n"
        
    /// <summary>
    /// Returns a string representation of the table
    /// </summary>
    /// <param name="entry_to_string">Function to convert (object, attributes) pairs to string</param>
    /// <returns>String showing entries in the table</returns>
    member this.show_table(entry_to_string: int * 'obj * 'attrs -> string) =
        table
        |> Seq.mapi (fun idx (obj, attrs) -> entry_to_string(idx, obj, attrs))
        |> String.concat "\n"
        
    /// <summary>
    /// Adds an item to the map and returns its index
    /// </summary>
    /// <param name="obj">Object to add</param>
    /// <param name="attrs">Attributes to associate with the object</param>
    /// <returns>Index of the added item</returns>
    member this.add(obj: 'obj, attrs: 'attrs) =
        let mutable existingIndex = -1
        if index.TryGetValue(obj, &existingIndex) then
            existingIndex
        else
            let newIndex = table.Count
            index.[obj] <- newIndex
            table.Add((obj, attrs))
            newIndex
    
    /// <summary>
    /// Tries to get the index of an object
    /// </summary>
    /// <param name="obj">Object to look up</param>
    /// <returns>Some index if found, None otherwise</returns>
    member this.try_get_index(obj: 'obj) =
        let mutable idx = -1
        if index.TryGetValue(obj, &idx) then
            Some idx
        else
            None
    
    /// <summary>
    /// Gets an object and its attributes by index
    /// </summary>
    /// <param name="idx">Index to look up</param>
    /// <returns>Tuple of object and its attributes</returns>
    member this.get(idx: int) =
        if idx >= 0 && idx < table.Count then
            table.[idx]
        else
            failwith $"Index {idx} out of range (0..{table.Count-1})"
    
    /// <summary>
    /// Sets (overwrites) an entry at the specified index
    /// </summary>
    /// <param name="idx">Index to update</param>
    /// <param name="obj">New object to store</param>
    /// <param name="attrs">New attributes to store</param>
    /// <exception cref="System.ArgumentException">Thrown if index is out of range</exception>
    member this.set(idx: int) (obj: 'obj, attrs: 'attrs) =
        if idx >= 0 && idx < table.Count then
            table.[idx] <- (obj, attrs)
        else
            failwith $"Index {idx} out of range (0..{table.Count-1})"
    
    /// <summary>
    /// Gets just the object at specified index
    /// </summary>
    member this.get_object(idx: int) =
        fst (this.get(idx))
    
    /// <summary>
    /// Gets just the attributes at specified index
    /// </summary>
    member this.get_attrs(idx: int) =
        snd (this.get(idx))
    
    /// <summary>
    /// Checks if the map contains the specified object
    /// </summary>
    member this.contains(obj: 'obj) =
        index.ContainsKey(obj)
    
    /// <summary>
    /// Gets all items as an array of (object, attributes) tuples
    /// </summary>
    member this.to_array() =
        table.ToArray()
    
    /// <summary>
    /// Gets all objects as a sequence
    /// </summary>
    member this.objects = 
        table |> Seq.map fst
    
    /// <summary>
    /// Gets all attributes as a sequence
    /// </summary>
    member this.attributes = 
        table |> Seq.map snd

/// <summary>
/// Creates a new empty IndMap
/// </summary>
let newIndMap<'obj, 'attrs when 'obj : equality>() = 
    IndMap<'obj, 'attrs>()