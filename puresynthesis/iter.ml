module Iter = struct

type 'a iter = {value : 'a option; next : unit -> 'a iter}

(** an iterator that always returns None *)
let rec finishedIter : unit -> 'a iter = fun () -> {value = None; next = finishedIter}

(** Takes a list and converts it into an iterator *)
let rec constructIter lst =
    match lst with
    | h::t -> {value = Some h; next= fun () -> constructIter t}
    | [] -> finishedIter ()

(** Takes all the values out of an iterator and produces a list *)
let rec constructList iter =
    match iter.value with
    | None -> []
    | Some s -> s :: (constructList (iter.next ()))

(** Takes an iterator and a constuctor for an iterator and produces  *)
let rec chainIter (iter: 'a iter) (none_case:unit -> 'a iter) : 'a iter =
    match iter.value with
    | Some i -> {value = Some i; next = fun () -> chainIter (iter.next ()) none_case}
    | None -> none_case ()

(** Takes a list + a conversion function and produces an iterator *)
let rec makeIter (f: 'a -> 'b ) (l: 'a list) : 'b iter =
    match l with
    | [] -> finishedIter ()
    | h :: t -> {value = Some (f h); next = fun () -> makeIter f t}

(** Takes an iterator and does your standard map operation *)
let rec mapIter (f:'a -> 'b) (i:'a iter) : 'b iter =
    match i.value with
    | None -> finishedIter ()
    | Some a -> {value = Some (f a); next= fun () -> mapIter f (i.next ())}

(** Takes an iterator and a map function and returns all of the `Some _` results *)
let rec mapFilterIter (f: 'a  -> 'b option) (i : 'a iter) : 'b iter =
    match i.value with
    | None -> finishedIter ()
    | Some e -> (match f e with
                | None -> mapFilterIter f (i.next ())
                | Some v -> {value = Some v; next = fun () -> mapFilterIter f (i.next ())}
                )

let rec nestedIter (f: 'a -> 'b iter) (i: 'a iter) : 'b iter =
    match i.value with
    | None -> finishedIter ()
    | Some a -> chainIter (f a) (fun () -> nestedIter f (i.next ()))

(** Take the cross product of two iter's *)
let rec productIter (a:'a iter) (b:'b iter) : ('a * 'b)iter =
    match a.value with
    | Some a1 -> chainIter (mapIter (fun b1 -> (a1, b1)) b) (fun () -> productIter (a.next ()) b)
    | _-> finishedIter ()

let rec for_eachIter (f: 'a -> unit) (a: 'a iter) : unit =
    match a.value with
    | Some (a1) -> f a1; for_eachIter f (a.next ())
    | None -> ()

end