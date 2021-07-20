(*defined Var or import from the specLang*)
open Printf 
open SpecLang 
    
module RefTy = RefinementType

type var = Var.t 

type caseExp = {constuctor : var;
                args : var list ;
                exp : typedMonExp}



and  monExp = 
        | Evar of var 
        | Elam of monExp * typedMonExp
        | Efix of var * typedMonExp * typedMonExp
        | Eapp of typedMonExp * typedMonExp
        | Ematch of typedMonExp * (caseExp list) 
        | Elet of monExp * typedMonExp * typedMonExp
        | Eret of typedMonExp 
        | Ebind of monExp * typedMonExp * typedMonExp
        | Elloc of typedMonExp           
        | Eget of typedMonExp 
        | Eset of typedMonExp * typedMonExp
        | Ecapp of var * ( monExp list ) 
        | Ehole (*a hole in place of an expression*)
        | Edo of monExp * monExp (*do E; retrun K*)
        | Eskip   
and typedMonExp = {expMon:monExp; ofType:RefTy.t }



let rec doExp (ls : monExp list) : monExp= 
    match ls with 
        [] -> Eskip
        | x :: xs -> Edo (x, doExp (xs))
(*normal form*)
(*
type caseIExp = Case of {constuctor : var;
                args : var list ;
                exp : monIExp}


and  monEExp = 
        | Evar of var 
        | Eapp of monEExp * monIExp (*all application will be of the form x I1 I2....*)
        | Eret of monIExp
        | Ebind of monExp * monEExp  * monEExp
        | Elloc of monExp           
        | Eget of monEExp
        | Eset of monEExp * monIExp
                  
and monIExp = 
        | Elam of monEExp * monIExp
        | Efix of var * monIExp
        | Ematch of monEExp * (caseIExp list) 
        | Elet of monEExp * monIExp * monIExp
        | Ecapp of var * ( monIExp list ) 
        | Ehole (*a hole in place of an expression*)
        | Edo of monEExp * monIExp (*do E; retrun K*)

and normalMonExp = 
        | E of monEExp 
        | I of monIExp 
and typedNormalExp = {nme:normalMonExp;rt:RefTy.t}            
*)

let rec monExp_toString (m:monExp) = 
    match m with 
        | Evar v -> ("Evar "^v)
        | Eret ret ->  ("Eret "^(typedMonExp_toString ret))
        | Ebind (mne, tmne1, tmne2) -> ("Ebind "^(monExp_toString mne)^" <- "^
                                            (typedMonExp_toString tmne1)^" in "^
                                            (typedMonExp_toString tmne2 ))  
        | Ecapp (cname, argls) -> "Ecapp "^(cname)^" ( "^(
                                List.fold_left (fun accstr ai -> 
                                                accstr^", "^(monExp_toString ai)) "" argls

                                                )^" )" 
        | _ -> "Other expression"  


(*We will add more auxiliary functions here as we go along synthesis*)
and typedMonExp_toString (t:typedMonExp) : string = 
   let {expMon;ofType} = t in  
   ("{ \n"^monExp_toString expMon^" \n }") 



let getExp (t : typedMonExp) =
    let {expMon;_} = t in expMon

let getType (t : typedMonExp) = 
   let {ofType;_} = t in ofType

(*placeholder , TODO implement complete later*)
let buildProgramTerm (ci : Var.t) (path : Var.t list) =  
        Evar ci