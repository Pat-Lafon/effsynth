is_empty : (l2 : {v : list | true}) -> (u_0 : {v : int | true}) -> {v : bool | ([v = true] <=> not (mem (v, u_0) = true)) /\ [v = false]};

push : (x : {v : int | true}) -> (l1 : {v : list | true}) -> {v : list | true};

tail : (l4 : {v : list | true}) -> {v : list | true};

top : (l3 : {v : list | true}) -> {v : int | true};

goal : (l1 : {v : list | true}) -> (l2 : {v: list | true}) -> {v : list | true};


##########

let is_empty l u =
match l with
| [] -> true
| _ -> false

let push x l = x :: l

let tail = function
| [] -> []
| _::t -> t

let top = function
| [] -> 0
| h::_ -> h