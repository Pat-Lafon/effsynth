x : {v : int | [v = 0]};
y : {v : int | [v = 2]};

eq: (x1 : {v:int| true}) -> (x2 : {v:int| true}) -> {v : bool | ([v = true] <=> [x1 = x2])};

goal : (z : {v : int | true}) -> {v : bool | true };

##########

let x = 0
let y = 2

let eq x1 x2 = x1 == x2

##########

let () = assert (goal 0 == true)
let () = assert (goal 1 == false)
let () = assert (goal 2 == false)