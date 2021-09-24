tbl : ref [string];
Tbl0 : [string];
Tbl' : [string];
Tbl :  [int];



mem : (s  : { v : int | true}) -> 
			State  {\(h : heap). true} 
			v : { v : bool | true} 
			{\(h : heap), (v : bool), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				([v=true] <=> ( mem(Tbl', s) = true))/\ 
				([v=false] <=> (mem (Tbl', s) = false))};

fresh_str : State  {\(h : heap). true} 
			v : { v : int | true} 
			{\(h : heap), (v : int), (h' : heap). 
				len (v) == 3 /\
				ilssel (h', tbl) = Tbl' /\ 
				mem (Tbl', s) = false};


add : (s : {v : sint | true}) ->  
			State  {\(h : heap).ilssel (h, tbl) = Tbl /\ 
				(mem (tbl, s) = false)} 
				v : { v : unit | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				(mem (Tbl', s) = true) /\ 
				len (Tbl') == len (Tbl) + len (s) /\ 
				size (Tbl') == size (Tbl) + 1};
				


remove 	: (s : {v : int  | true}) ->  
			State  {\(h : heap).ilssel (h, tbl) = Tbl /\ 
						(mem (Tbl, s) = true)} 
				v : { v : unit | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				(mem (Tbl', s) = false) /\ 
				len (Tbl') == len (Tbl) - len (s) /\ 
				size (Tbl') == size (Tbl) - 1};

head : State  {\(h : heap).ilssel (h, tbl) = Tbl 
					/\ size (Tbl) > 0} 
				v : { v : int | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				(mem (Tbl', v) = false) /\ 
				len (Tbl') == len (Tbl) - len (v) /\ 
				size (Tbl') == size (Tbl) - 1};



average_len : State  {\(h : heap).ilssel (h, tbl) = Tbl 
					/\ size (Tbl) > 0} 
				v : { v : float | true} 
			 {\(h : heap), (v : float), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				 not (min (Tbl') > v) /\
				 not (v > max (Tbl')) /\
				ilssel (h', tbl) =ilssel (h, tbl)};


concat  : State  {\(h : heap).ilssel (h, tbl) = Tbl /\ 
				size (Tbl) > 0} 
				v : { v : string | true} 
			 {\(h : heap), (v : string), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				len (v) = len (Tbl')};



sort : State  {\(h : heap). true} 
				v : { v : unit | true} 
			 {\(h : heap), (v : unit), (h' : heap). 
				ilssel (h, tbl) = Tbl /\ 
				 sorted (Tbl) = true};






goal : (s : {v : string | true}) -> 
		
		State {\(h : heap). ilssel (h, tbl) = Tbl}
			v : {v : float | true}
		   
		   {\(h : heap), (v : float), (h' : heap). 
				ilssel (h', tbl) = Tbl' /\ 
				v >= 0 /\
				not (min (Tbl') > v) /\
				not (v > max (Tbl')) /\
				
				((not (mem (Tbl, s) = true)) 
					/\ len (Tbl') == len (tbl) + len (s) + 3) \/ 
				((mem (tbl, s) = true) 
					/\ len (tbl') == len (tbl) + 6)
			
			};



goal : string -> tbl -> float

let us try to see the programs which will be generated by the SYPET/H+
With the constraints used in the SYPET that each program variable must be used atleast once.


(*generates potentially incorrect program*)
(*synth1*)
\ s tbl. 
(*violating add contract*)
let tbl1 = add_string s tbl in 
let avg = avg_len tbl1 in 
return avg

(*a scenario which will break function*)
let t : tbl = ref []
add t s; 
add_and_take_avg t s 



(*synth2*)
\ s tbl. 
let decision = mem s tbl
if (decision) then 
    let avg = avg_len tbl in 
    return avg;
else 
	(*violating avg_len contract*)
	let avg = avg_len tbl in 
    return avg;

(*a scenario which will break the function*)
let t : tbl = ref []
synth2 t s 



(*synth3 simple programs similar to 1*)
\ s tbl. 
(*a violation*)
let tbl1 = add_string s tbl in 
let s1 = fresh_str tbl1
(*both tbl1 or tbl can  be used as the argument to add_string, by rule Klone*)
(*violation add_string*)
let tbl2 = add_string s1 tbl in 
let avg = avg_len tbl2 in 
return avg

(*synth4*)
\ s tbl. 
(*violation add_contract*)
let tbl1 = add_string s tbl in 
let tbl2 = add_string s tbl in 
let s1 = fresh_str tbl1
(*both tbl1 or tbl can  be used as the argument to add_string, by rule Klone*)
(*violation*)
let tbl2 = add_string s1 tbl in 
let avg = avg_len tbl2 in 
return avg





(*correct programs*)

\s  : string tbl : tbl
let decision = mem s tbl in 
if (decision) then 
	let s1 =  fresh_str tbl
	let tbl1 =  add_string s1 tbl;
	let avg = avg_len tbl1 in 
	return avg;
	
else (*the smallest program*)
	let tbl2 =  add_string s tbl;
	let avg = avg_len tbl2 in 
	return avg;







\s  : string tbl : tbl
let decision = mem s tbl in 
if (decision) then 
	let tbl1 = remove s tbl in 
	let tbl2 =  add_string s1 tbl;
	let avg = avg_len tbl1 in 
	return avg;
	
else (*the smallest program*)
	let tbl2 =  add_string s tbl;
	let avg = avg_len tbl2 in 
	return avg;





