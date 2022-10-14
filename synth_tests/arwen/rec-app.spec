x1 : {v : int | [v = 0]};
y1 : {v : int | [v = 2]};
z1 : {v : int | [v = 1]};

isZero: (x : {v:int| true}) -> {v : bool | ([v = true] <=> [x = 0])};

succ : (x : {v:int | true}) -> {v:int | v = x + 1};

unsucc : (x : {v:int | true}) -> {v:int | v = x - 1};

goal : (x : {v : int | true}) -> (x2 : {v : int | true}) -> {v : int | true};

##########

let x1 = 0
let y1 = 2
let z1 = 1

let isZero x = x == 0

let succ x = x + 1

let unsucc x = x - 1

##########

let () = assert ((goal 0 0 != 3))

let () = assert ((goal 1 3 == 4))

let () = assert ((goal 4 2 == 6))