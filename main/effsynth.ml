open SpecLang
module SEL = SpecElab
module Synth = Synthesis
module Lambda = Lambdasyn
exception CompilerExc of string

(** Set up debug/printing*)
module Printf = struct
  let debugFlag = ref true
  let printf d s = if !debugFlag then Printf.printf d s else ()
  let originalPrint = Printf.printf
end

(** Set debug information*)
let () = Printf.debugFlag := false
let () = SpecLexer.debugFlag := false
let () = SpecElab.Printf.debugFlag := false


(** Initialize global state from argument flags *)
let learningON = ref false
let bidirectional = ref false
let spec_file = ref ""
let effect_filter = ref false
let goal_number = ref 0
let maxPathlength = ref 10
let usage_msg = "effsynth [-cdcl] [-bi] [-effect] <spec-file1> -g <goal-number>"
let anon_fun specfile =
    spec_file := specfile
let speclist =
  [("-effect", Arg.Set effect_filter, "Set the effect-guided filtering to true");
   ("-cdcl", Arg.Set learningON, "Set to CDCL=true");
   ("-bi", Arg.Set bidirectional, "Set bidirectional=true");
   ("-g", Arg.Set_int goal_number, "Set the #goal number");
   ("-l", Arg.Set_int maxPathlength, "Set the max path length")]
let () = Arg.parse speclist anon_fun usage_msg;


(** Debug info *)
let () = Printf.printf "%s" ("\n EXPLORED Args.parser output ") in
let () = Printf.printf "%s" ("\n EXPLORED learningOn  "^(string_of_bool !learningON)) in
let () = Printf.printf "%s" ("\n EXPLORED bidirectionality  "^(string_of_bool !bidirectional)) in
let () = Printf.printf "%s" ("\n EXPLORED effect-filter  "^(string_of_bool !effect_filter)) in
let () = Printf.printf "%s" ("\n EXPLORED specfile :: "^(!spec_file)) in
let () = Printf.printf "%s" ("\n EXPLORED goal Number :: "^(string_of_int (!goal_number))) in

(** Parse AST *)
let ast = SEL.parseLSpecFile !spec_file in

(** Debug ast*)
let string_ast = RelSpec.toString ast in
let () = Printf.printf "\n\n Printing ast:\n%s" string_ast in


(** Initialize state for synthesis *)
(* Gamma: Starting context of components *)
(* Sigma: *)
(* Typenames: *)
(* Quals: qualifiers from ast *)
(* Goals: List of types to be synthesized *)
let (gamma, sigma, typenames, quals, goals) = SEL.elaborateEnvs ast in
let goal = List.nth goals !goal_number in
let delta = P.True in


(** Debug info *)
let () = Printf.printf "%s" "\n\n INITIAL GAMMA" in
let () = List.iter (fun (vi, rti) -> Printf.printf " %s"
                    ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) gamma in
let () = Printf.printf "%s" "\n\n INITIAL SIGMA" in
let () = List.iter (fun (vi, rti) -> Printf.printf " %s"
                    ("\n "^(Var.toString vi)^" : "^(RefTy.toString rti))) sigma in
let () = Printf.printf "%s" "\n\n TypeNames" in
let () = List.iter (fun tni -> Printf.printf " %s" ("\n "^tni)) typenames in
let () = Printf.printf "%s" "\n\n Qualifiers" in
let () = List.iter (fun (qi) -> Printf.printf " %s"
                    ("\n "^(SpecLang.RelSpec.Qualifier.toString qi))) quals in
let () = Printf.printf "%s" "\n\n Goals" in
let () = List.iter (fun rt -> Printf.printf " %s" ("\n "^(RefTy.toString rt))) goals in

(** Starts the synthesis engine*)
let synthterm = Synth.Bidirectional.toplevel gamma sigma delta typenames quals goal !learningON !bidirectional !maxPathlength !effect_filter in
  (*run the initial environment builder*)
  match synthterm with
      | None -> Printf.originalPrint "%s" "Synthesis returned witout result"
      | Some t -> Printf.originalPrint "%s" ("Success : "^(Lambda.typedMonExp_toString t))
