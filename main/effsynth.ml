open SpecLang 
module SEL = SpecElab
module Synth = Synthesis
module Lambda = Lambdasyn 
exception CompilerExc of string  

let learningON = ref false 
let bidirectional = ref false
let spec_file = ref ""
let effect_filter = ref false
let usage_msg = "effsynth [-cdcl] [-bi] [-effect] <spec-file1>" 
let anon_fun specfile = 
    spec_file := specfile


  let speclist =
  [("-effect", Arg.Set effect_filter, "Set the effect-guided filtering to true");
   ("-cdcl", Arg.Set learningON, "Set to CDCL=true");
   ("-bi", Arg.Set bidirectional, "Set bidirectional=true")] 
  
let () = 


  Arg.parse speclist anon_fun usage_msg;
  
  let () = Printf.printf "%s" "\n  EXPLORED Args.parser output " in 
  let () = Printf.printf "%s" ("\n EXPLORED learningOn  "^(string_of_bool !learningON)) in 
  let () = Printf.printf "%s" ("\n EXPLORED bidirectionality  "^(string_of_bool !bidirectional)) in
  let () = Printf.printf "%s" ("\n EXPLORED effect-filter  "^(string_of_bool !effect_filter)) in 
  let () = Printf.printf "%s" ("\n EXPLORED specfile :: "^(!spec_file)) in 

  (* raise (CompilerExc "Forced"); *)

  let maxPathlength = 5 in 
  let ast = SEL.parseLSpecFile !spec_file in 
  let string_ast = RelSpec.toString ast in 
  let () = Printf.printf "%s" string_ast in 
  let (gamma, sigma, goal) = SEL.elaborateEnvs ast in 
  let delta = P.True in 
  let () = Printf.printf "%s" " INITIAL GAMMA \n " in 
  let () = List.iter (fun (vi, rti) -> Printf.printf "%s" 
                      ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) gamma in 


  let () = Printf.printf "%s" " INITIAL SIGMA \n " in 
  let () = List.iter (fun (vi, rti) -> Printf.printf "%s" 
                      ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) sigma in 


  let synthterm = Synth.Bidirectional.synthesize gamma sigma  delta goal !learningON !bidirectional maxPathlength !effect_filter in   
    (*run the initial environment builder*)    
    match synthterm with 
        | None -> Printf.printf "%s" "Synthesis returned witout result"
        | Some t -> Printf.printf "%s" ("Success : "^(Lambda.typedMonExp_toString t))
   
(*    

  let num_args = (Array.length Sys.argv) - 1 in 
  if num_args = 4 then  
    let spec_file = Sys.argv.(1) in 
    let learningON = bool_of_string (Sys.argv.(2)) in 
    let bidirectional = bool_of_string (Sys.argv.(3)) in 
    let effectguildedFileter = bool_of_string (Sys.argv.(4)) in 
    (* (*    let maxPathlength = int_of_string (Sys.argv.(4)) in  *)
    *)
    let maxPathlength = 5 in 
    let _ = Printf.printf "%s" ("\n Show LEARNING :: "^(Sys.argv.(2))) in 
    let _ = Printf.printf "%s" ("\n Show Bidirectional :: "^(Sys.argv.(3))) in 
     
    let _ = Printf.printf "%s" ("\n specfile :: "^spec_file) in 
    let ast = SEL.parseLSpecFile spec_file in 
    (* let () = Printf.printf "%s" ("\n List of components available") in  *)
    let string_ast = RelSpec.toString ast in 
    let () = Printf.printf "%s" string_ast in 
    let (gamma, sigma, goal) = SEL.elaborateEnvs ast in 
    let delta = P.True in 
    let () = Printf.printf "%s" " INITIAL GAMMA \n " in 
    let () = List.iter (fun (vi, rti) -> Printf.printf "%s" 
                      ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) gamma in 


    let () = Printf.printf "%s" " INITIAL SIGMA \n " in 
    let () = List.iter (fun (vi, rti) -> Printf.printf "%s" 
                      ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) sigma in 


    let synthterm = Synth.Bidirectional.synthesize gamma sigma  delta goal learningON bidirectional maxPathlength effectguildedFileter in   
    	    (*run the initial environment builder*)    
    match synthterm with 
        | None -> Printf.printf "%s" "Synthesis returned witout result"
        | Some t -> Printf.printf "%s" ("Success : "^(Lambda.typedMonExp_toString t))
   
   else
    let exception_msg = (" Incorrect Number of argumnets, required 1, provided "^(string_of_int num_args)^" Usage :: ./compile.native <path_to_ml_file> <path_to_spec_file>") in  
    raise (CompilerExc  exception_msg)
  *)
  