x1 : {v : int | [v = 0]};
y1 : {v : int | [v = 2]};
succ: (x3 : {v:int| true}) -> {v : int | (v = x3 +1)};
goal : {v : int | [v = 3]};


#############

let x1 = 0
let y1 = 2
let succ x = x+1