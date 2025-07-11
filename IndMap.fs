module IndMap

open System.Collections.Generic

/// <summary>
/// IndMap is an indexed map that stores objects with their attributes and provides efficient lookups.
/// </summary>
/// <typeparam name="'obj">Type of objects being stored, must support equality</typeparam>
/// <typeparam name="'attrs">Type of attributes associated with each object</typeparam>

type IndMap<'obj, 'attrs when 'obj : equality> = {
    index : Dictionary<'obj, int>
    table : ResizeArray<'obj * 'attrs>
}

/// <summary>
/// Creates a new empty IndMap
/// </summary>
let newIndMap<'obj, 'attrs when 'obj : equality>() : IndMap<'obj, 'attrs> = 
    let index = new Dictionary<'obj, int>(HashIdentity.Structural)
    let table = new ResizeArray<'obj * 'attrs>()
    { index = index; table = table }

/// <summary>
/// Gets the current count of items in the map
/// </summary>
let inline count im = im.table.Count 
    
/// <summary>
/// Returns a string representation of the index dictionary
/// </summary>
/// <param name="obj_to_string">Function to convert objects to string representation</param>
/// <returns>String showing mapping from objects to indices</returns>
let show_index (obj_to_string: 'obj -> string) (im : IndMap<'obj, 'attrs>) =
    im.index
    |> Seq.toList
    |> List.map (fun obj_value -> sprintf "%s -> %d" (obj_to_string obj_value.Key) obj_value.Value)
    |> String.concat "\n"
    
/// <summary>
/// Returns a string representation of the table
/// </summary>
/// <param name="entry_to_string">Function to convert (object, attributes) pairs to string</param>
/// <returns>String showing entries in the table</returns>
let show_table (entry_to_string: int * 'obj * 'attrs -> string) (im : IndMap<'obj, 'attrs>) =
    im.table
    |> Seq.mapi (fun idx (obj, attrs) -> entry_to_string(idx, obj, attrs))
    |> String.concat "\n"
    
/// <summary>
/// Adds an item to the map and returns its index
/// </summary>
/// <param name="obj">Object to add</param>
/// <param name="attrs">Attributes to associate with the object</param>
/// <returns>Index of the added item</returns>
let inline add (obj: 'obj, attrs: 'attrs) (im : IndMap<'obj, 'attrs>) =
    let mutable existingIndex = -1
    if im.index.TryGetValue(obj, &existingIndex) then
        existingIndex
    else
        let newIndex = im.table.Count
        im.index.[obj] <- newIndex
        im.table.Add((obj, attrs))
        newIndex

/// <summary>
/// Tries to get the index of an object
/// </summary>
/// <param name="obj">Object to look up</param>
/// <returns>Some index if found, None otherwise</returns>
let inline try_get_index (obj: 'obj) (im : IndMap<'obj, 'attrs>) =
    let mutable idx = -1
    if im.index.TryGetValue(obj, &idx) then
        Some idx
    else
        None

/// <summary>
/// Gets an object and its attributes by index
/// </summary>
/// <param name="idx">Index to look up</param>
/// <returns>Tuple of object and its attributes</returns>
let inline get (idx: int) (im : IndMap<'obj, 'attrs>) =
    im.table.[idx]

/// <summary>
/// Sets (overwrites) an entry at the specified index
/// </summary>
/// <param name="idx">Index to update</param>
/// <param name="obj">New object to store</param>
/// <param name="attrs">New attributes to store</param>
/// <exception cref="System.ArgumentException">Thrown if index is out of range</exception>
let inline set (idx: int) (obj: 'obj, attrs: 'attrs) (im : IndMap<'obj, 'attrs>) =
    if idx >= 0 && idx < im.table.Count then
        im.table.[idx] <- (obj, attrs)
    else
        failwith $"Index {idx} out of range (0..{im.table.Count-1})"

/// <summary>
/// Gets just the object at specified index
/// </summary>
let inline get_obj (idx: int) (im : IndMap<'obj, 'attrs>) =
    fst im.table.[idx]

/// <summary>
/// Gets just the attributes at specified index
/// </summary>
let inline get_attrs (idx: int) (im : IndMap<'obj, 'attrs>) =
    snd im.table.[idx]

/// <summary>
/// Checks if the map contains the specified object
/// </summary>
let inline contains (obj: 'obj) (im : IndMap<'obj, 'attrs>) =
    im.index.ContainsKey (obj)

/// <summary>
/// Gets all items as an array of (object, attributes) tuples
/// </summary>
let to_array (im : IndMap<'obj, 'attrs>) =
    im.table.ToArray ()

/// <summary>
/// Gets all objects as a sequence
/// </summary>
let objects (im : IndMap<'obj, 'attrs>) = 
    im.table |> Seq.map fst

/// <summary>
/// Gets all attributes as a sequence
/// </summary>
let attributes (im : IndMap<'obj, 'attrs>) = 
    im.table |> Seq.map snd
