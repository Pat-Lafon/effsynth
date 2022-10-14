module Syn = Lambdasyn
module VC = VerificationC
open SpecLang
open Syn
module Gamma = Environment.TypingEnv
module Sigma = Environment.Constructors
module Explored = Environment.ExploredTerms
module ExploredPaths = Environment.ExploredPaths
module VCE = Vcencode
module PTypeMap = Knowledge.PathTypeMap
module P = Predicate
module BP = Predicate.BasePredicate
module SynTC = Syntypechecker

open Iter.Iter

open Message

exception SynthesisException of string

(** From https://rosettacode.org/wiki/Cartesian_product_of_two_or_more_lists#OCaml recommended by Yongwei*)
let rec product'' l =
    (* We need to do the cross product of our current list and all the others
     * so we define a helper function for that *)
    let rec aux ~acc l1 l2 = match l1, l2 with
    | [], _ | _, [] -> acc
    | h1::t1, h2::t2 ->
        let acc = (h1::h2)::acc in
        let acc = (aux ~acc t1 l2) in
        aux ~acc [h1] t2
    (* now we can do the actual computation *)
    in match l with
    | [] -> []
    | [l1] -> List.map (fun x -> [x]) l1
    | l1::tl ->
        let tail_product = product'' tl in
        aux ~acc:[] l1 tail_product

let learningOn = ref false
let bidirectionalOn = ref false
let efilterOn = ref false
let typenames = ref []
let qualifiers = ref []

(** can enumerate a variable of refined basetype, an arrow type or a effectful component*)
let enumPureE explored gamma sigma delta (spec : RefTy.t) debug : Syn.typedMonExp iter =
    Message.show debug ("Show :: In enumPureE");
    let debug = (Message.incr_depth debug) in

    match spec with
        (*Tvar case*)
        | RefTy.Base (v, t, pred) ->
        let foundTypes = Gamma.enumerateAndFind gamma spec in

        (*filter the explored*)
        (* let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in *)

        let rec verifyFound fs potentialExps : typedMonExp list =
            match fs with
                | [] -> potentialExps
                | (vi, rti) :: xs ->
                    Message.show debug ("Show :: Enumerating a Pure Term "^(Var.toString vi));
                    Message.show debug ("Show :: Type of the Pure Term "^(RefTy.toString rti));

                    (** Skip the ghost Vars like [A-Z]**)
                    let startCharvar = vi.[0] in
                    let upper = Char.uppercase_ascii startCharvar in
                    if (startCharvar = upper) then
                        verifyFound xs potentialExps
                    else
                        let isGhost =
                            if (String.length vi > 4) then
                                let initial = String.sub vi 0 4 in
                                Message.show debug ("Show ::  Initial "^(initial));
                                if (initial = "var_") then
                                    true
                                else
                                    false
                            else
                                false
                        in
                        if (isGhost) then
                            verifyFound xs potentialExps
                        else
                            (* let () = Message.show ("\n Show ::  Associated Delta "^(Predicate.toString delta)) in *)
                            (*substitute, bound variables in both with the argument variable*)
                            let rti_bound_vi = RefTy.alphaRenameToVar rti vi in
                            let spec_bound_vi = RefTy.alphaRenameToVar spec vi in
                            let vc = VC.fromTypeCheck gamma [delta] (rti_bound_vi, spec_bound_vi) in
                            (*make a direct call to the SMT solver*)
                            let vcStandard = VC.standardize vc in
                            Message.show debug ("Show :: standardized VC:");
                            VC.Message.depth := Message.depth (Message.incr_depth debug);
                            VC.print_for_vc_stt vcStandard;
                            VCE.Message.depth := Message.depth (Message.incr_depth debug);
                            let result = VCE.discharge vcStandard !typenames !qualifiers in
                            match result with
                            | VCE.Success ->
                                    let ei = {expMon = (Syn.Evar (vi));
                                                ofType = rti} in
                                    verifyFound xs (ei::potentialExps)
                            | VCE.Failure ->
                                    Message.show debug ("FaileD the subtype check T_vi <: T_goal");
                                    verifyFound xs potentialExps
                            | VCE.Undef -> raise (SynthesisException "Failing VC Check for pureEnum")

            in
            constructIter (verifyFound foundTypes [])
        | RefTy.Arrow ((_,_),_) ->
                    Message.show debug (" Show :: HOF argument required, unhanlded currently thus skipping");
                    failwith "unimplemented"
        | _ -> raise (SynthesisException "Illegal/Unhandled elimination form for PureTerm")

let rec synthesize gamma sigma delta spec debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    match spec with
        | RefTy.Base (v, t, pred) ->
            Message.show debug "Show ***********Calling Scalar synthesize***************";
            esynthesizeScalar gamma sigma delta [spec] (Message.incr_depth debug) maxPath
        | RefTy.Arrow (rta, rtb) ->
            Message.show debug "Show ***********Calling S-FUNC synthesize***************";
            isynthesizeFun gamma sigma delta spec (Message.incr_depth debug) maxPath(*applies Tfix and Tabs one after the other*)
        | _ -> raise (SynthesisException ("Unhanlded Case synthesis  for query spec "^(RefTy.toString  spec)))

and esynthesizeScalar gamma sigma delta specs_path debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else

    let () = if (List.length specs_path < 1) then raise (SynthesisException "Scalar synthesis Call without spec") in

    let explored = Explored.empty in
    let leaf_spec = List.hd specs_path in

    Message.show debug ("Show :: esynthesizeScalar for "^(RefTy.toString leaf_spec));
    let debug = Message.incr_depth debug in

    match leaf_spec with
        | RefTy.Base (_,_,_) ->
            let foundbyEnum = enumPureE explored gamma sigma delta leaf_spec (Message.incr_depth debug) in
            chainIter foundbyEnum (
                fun () -> Message.show debug ("Show :: No Scalar found, Call esynthesizePureApp ");
                    let appterm = esynthesizePureApp gamma sigma delta specs_path (Message.incr_depth debug) (maxPath -1) in
                    chainIter appterm
                    (fun () -> Message.show debug("Show :: No pureApp found, Call esynthesizeConsApp ");
                        esynthesizeConsApp gamma sigma delta specs_path (Message.incr_depth debug) (maxPath -1)
                    )
                )
        | RefTy.Arrow ((_,_),_) -> Message.show debug ("Show :: Tried to synthesize scalar for arrow type"); failwith "unimplemented"
        | _ -> raise (SynthesisException "Synthesizing Scalar of Unhandled Shape")

(*Top level syntheis goals for Lambda, same as the traditional syntehsis rules
calls the top-level macthing and application followed by if-rule and then the standard learning based rule *)
and isynthesizeFun gamma sigma delta spec debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    (*TODO unhandled case of isynthesize*)
    let uncurried_spec = RefTy.uncurry_Arrow spec in
    Message.show debug ("Show "^RefTy.toString uncurried_spec);
    let [@warning "-8"] RefTy.Uncurried ( fargs_type_list, retT) = uncurried_spec [@warning "+8"] in
    (*extend gamma*)
    (*first try a match case, if it does not succeed, try the non-matching case*)
    let gamma_extended = Gamma.append gamma fargs_type_list in
    (*ASSUMPTION, the argumnet to deconstruct will be at the head*)
    let argToMatch = List.hd (fargs_type_list) in
    (*Given disjunctions in the spec we can directly try match*)
    Message.show debug ("Show Trying :: Top-level Match");
    let match_expression = isynthesizeMatch gamma_extended sigma delta argToMatch retT (Message.incr_depth debug) (maxPath -1) in
    chainIter match_expression (
        fun () -> Message.show debug ("Show ::::::::: Match-case failed :: Try Top-level If then else ");
            let if_exp = isynthesizeIf gamma_extended sigma delta retT (Message.incr_depth debug) (maxPath -1) in
            chainIter if_exp (
                fun () -> Message.show_with_newlines debug ("Show >>>>>>>>>>>>>>>>>>>>>> If then else Failed :: Try CDCL without subdivision\n <<<<<<<<<<<<<<<<<<<");
                synthesize gamma_extended sigma delta retT (Message.incr_depth debug) maxPath
            )
        )

(*The function application synthesis for pure componenent, we can try to replace this with say SYPET*)
and esynthesizePureApp gamma sigma delta specs_path debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    (*This is a simplified version of the return typed guided component synthesis as in SYPET*)
    let () = Message.show debug ("Show :: In esynthesizePureApp ") in
    let debug = (Message.incr_depth debug) in

    let spec = List.hd specs_path in
    (*filter pyre fuctions*)
    let potentialChoices = Gamma.lambdas4RetType gamma spec in

    (*Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show debug ("Show Potential Functions");
    Message.show debug (List.fold_left (fun acc (vi, _) -> acc^", "^Var.toString vi) "Show:" potentialChoices);

    let rec choice potentialChoices gamma sigma delta = (match potentialChoices with
        | (vi, (RefTy.Arrow ((varg, argty), _) as rti)) :: xs ->
            let () = Message.show debug ("Show *************** Arrow Component ************"^(Var.toString vi)) in
            let [@warning "-8"] RefTy.Uncurried (args_ty_list, retty) = RefTy.uncurry_Arrow rti [@warning "+8"] in
            let () = Message.show debug ("Show *************** Synthesizing Args ei : ti for ************ "^(Var.toString vi)) in

            let () = Printf.printf "\n%i\n" (maxPath) in

            (* lists of terms which can be used as argument *)
            (* TODO this is super suss *)
            let e_potential_args_list : (Syn.typedMonExp iter) list =
                List.map (fun (argi, argtyi) ->
                    (*if we the synthesis goal becomes cyclic then break*)
                    (* let cycle = List.exists (fun spec_i -> RefTy.compare_types spec_i argtyi) specs_path in

                    if (cycle) then
                        finishedIter ()
                    else *)
                        let () = Message.show debug ("Show Not Equal "^(RefTy.toString spec)^" Vs "^(RefTy.toString argtyi)) in
                        esynthesizeScalar gamma sigma delta [argtyi;retty] (Message.incr_depth debug) (maxPath -1)
                ) args_ty_list in

            let all_successful = List.filter (fun e_argi -> match e_argi.value with
                                                | Some _ -> true
                                                | None -> false) e_potential_args_list in



            (* for each arg_i we have a list of potential args [pi1;pi2;pi3] *)
            (*length of synthesized args match with the formal parameter*)
            let e_allsuccessful = (if ((List.length all_successful) = (List.length args_ty_list))
                                    then Some all_successful
                                    else None) in
            (match e_allsuccessful with (*BEGIN1*)
                | None -> (*Atleast one required argument cannot be synthesized thus cannot make the call*)
                    Message.show debug ("Show *************** Synthesizing Args ei : Failed for some  arg");
                    choice xs gamma sigma delta
                | Some es ->
                    Message.show debug ("Show *************** Successfully Synthesized Args ei Forall i ");
                    let es = List.map (fun e -> constructList e) es in
                    let eg = product''(es) in
                    let () = Message.show debug ("Show :: typechecking arguments") in
                    let rec loop_through_arguments groups_argslist =
                        match groups_argslist with
                            | [] -> finishedIter ()
                            | argslist:: t ->
                                let monExps = List.map (fun e -> e.expMon) argslist in
                                let appliedMonExp = Syn.Eapp (Syn.Evar vi, monExps) in
                                let () = SynTC.Message.depth := Message.depth (Message.incr_depth debug) in
                                let funAppType =  SynTC.typecheck gamma sigma delta !typenames !qualifiers appliedMonExp spec in
                                (match funAppType with
                                    | Some type4AppliedMonExp ->
                                        Message.show debug (" Show *************** TypeChecking Succsessful "^(RefTy.toString type4AppliedMonExp));
                                        {value = Some {expMon= appliedMonExp; ofType=type4AppliedMonExp}; next = fun () -> loop_through_arguments t}
                                    | None -> Message.show debug ("FAILED TC PURE APP");
                                                    loop_through_arguments t) in
                    let foundArg = loop_through_arguments eg in
                    chainIter foundArg (fun () -> choice xs gamma sigma delta)
            ) (*END1*)
        | (vi, _):: xs ->
            let () = Message.show debug ("Show Pure Component "^(Var.toString vi)) in
            raise (SynthesisException  "Illegal choice for Pure Application")
        | [] -> finishedIter ()
    ) in
    choice potentialChoices gamma sigma delta

and esynthesizeConsApp gamma sigma delta specs_path debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    (*This is a simplified version of the return typed guided component synthesis as in SYPET*)
    let spec = List.hd specs_path in
    (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
    let foundCons = Sigma.findCons4retT sigma spec in
    Message.show debug "Found Cons";
    let () = List.iter(fun (coname, _) ->  Message.show debug (coname)) foundCons in

    Message.show debug ("Show esynthesizeConsApp:");
    let debug = (Message.incr_depth debug) in
    (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
    let potentialChoices = Sigma.findCons4retT sigma spec in
    Message.show debug "Found Cons";

    (*Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show debug (List.fold_left (fun acc (consName, _) -> acc^", "^Var.toString consName) "Show: " potentialChoices);

    let rec choice potentialChoices gamma sigma delta =
        match potentialChoices with
            | [] ->
                Message.show debug ("Show No more choices for ConsApp");
                finishedIter ()
             (*no more effectful components try pure function/constructor application*)
            | (vi, (RefTy.Arrow ((_, t1 ), t2) as rti)) :: xs ->
                Message.show debug ("Show Pure Component "^(Var.toString vi));
                let getExpandedConsType t1 =
                    match t1 with
                        | RefTy.Base(_, _, _) -> [t1]
                        | RefTy.Tuple listArgs -> listArgs
                        | _ -> raise (SynthesisException ("Illegal Constructor Type "^(RefTy.toString rti)))
                in
                let consArgs = getExpandedConsType t1 in
                Message.show debug ("Show *************** Synthesizing Constructor Args ei : ti for ************"^(Var.toString vi));

                Message.show debug ("Show *************** Synthesizing Constructor Checking for Cycles ********************");

                let e_potential_args_list = List.map (fun (cargtyi) ->
                    (* let cycle = List.exists (fun spec_i -> RefTy.compare_types spec_i cargtyi) specs_path in
                    if (cycle) then
                        raise (SynthesisException "FORCED ConsApp")
                    else *)
                        esynthesizeScalar gamma sigma delta (cargtyi::specs_path) (Message.incr_depth debug) (maxPath -1)) consArgs
                in

                let all_successful = List.filter (fun e_argi -> match e_argi.value with
                                                            | Some _ -> true
                                                            | None -> false) e_potential_args_list in

                (* for each arg_i we have a list of potential args [pi1;pi2;pi3] *)
                (*length of synthesized args match with the formal parameter*)
                let e_allsuccessful = (if ((List.length all_successful) = (List.length consArgs))
                                                then Some all_successful
                                                else None) in

                (match e_allsuccessful with (*BEGIN1*)
                    | None -> (*Atleast one required argument cannot be synthesized thus cannot make the call*)
                        Message.show debug ("Show *************** Synthesizing Args ei : Failed for some arg");
                        choice xs gamma sigma delta
                    | Some es ->
                        Message.show debug ("Show *************** Successfully Synthesized Args ei Forall i");

                        (* all args list have atleast one element, so we can call List.hd on these and run our regular incomplete version for funs (x1, x2,...) *)
                        let es = List.map (fun e -> constructList e) es in
                        let exprs = product'' es in
                        let it = makeIter (
                            fun h -> let monExps_es = List.map (fun ei -> ei.expMon) h in
                                let appliedConsMonExp = Syn.Ecapp (vi, monExps_es) in  (*apply vi e_arg*)
                                {expMon= appliedConsMonExp; ofType=spec}
                            ) exprs in
                        chainIter it (fun () -> choice xs gamma sigma delta)
                ) (*END1*)
            | _ -> raise (SynthesisException "Constructor Type must be an Arrow")
    in
    choice potentialChoices gamma sigma delta


(* TODO ::
    This is a first implementation  of a special rule for list, then generalize it to any algebraic type, say tree*)
and isynthesizeMatch gamma sigma delta argToMatch spec debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    let () = Message.show debug ("Show :: Synthesize Match "^(RefTy.toString spec)) in
    let (matchingArg, matchingArgType) = argToMatch in
    let [@warning "-8"] RefTy.Base(_, argBase, argBasePhi) = matchingArgType [@warning "+8"] in

    Message.show debug ("Show :: List "^(TyD.toString argBase));

    (*list constructor case, work on the genaral case later*)
    match argBase with
        | Ty_list _ | Ty_alpha _ ->
            if (TyD.isList argBase) then
                let () = Message.show debug ("Show LIST CASE ??"^(TyD.toString argBase)^" PHI "^(Predicate.toString argBasePhi)) in
                let x_var = Var.get_fresh_var "x" in
                let xs_var = Var.get_fresh_var "xs" in

                let gamma_c= Gamma.add gamma x_var (RefTy.fromTyD (TyD.Ty_int)) in
                let gamma_c = Gamma.add gamma_c xs_var ((RefTy.fromTyD (TyD.Ty_list TyD.Ty_int))) in


                let phi_c = SynTC.generateConsConstraints  matchingArg x_var xs_var in
                let phi_n = SynTC.generateNilConstraints   matchingArg in
                Message.show debug ("Show :: "^(Predicate.toString phi_c));
                Message.show debug ("Show :: "^(Predicate.toString phi_n));


                let delta_n = Predicate.Conj (delta, phi_n) in
                let delta_c = Predicate.Conj (delta, phi_c) in


                let gamma_n = gamma in

                let e_n = synthesize gamma_n sigma delta_n spec (Message.incr_depth debug) (maxPath -1) in
                let e_c = synthesize gamma_c sigma delta_c spec (Message.incr_depth debug) (maxPath -1) in

                mapIter (fun (exp_n, exp_c) ->
                    Message.show debug ("Show :: Successfully Synthesisized Cons Branch ");

                    let caseExps = [exp_n; exp_c] in
                    let consArgs = [[];[x_var;xs_var]] in
                    (*General Case : we will have the constructor name in the Sigma*)
                    let cons = [Var.fromString "Nil"; Var.fromString "Cons"] in
                    let matchingArg = {Syn.expMon = Syn.Evar matchingArg;
                                            Syn.ofType = matchingArgType} in
                    let matchExp = Syn.merge matchingArg cons consArgs caseExps in
                    {Syn.expMon = matchExp; Syn.ofType = spec}
                ) (productIter e_n e_c)
            else
                finishedIter ()
        | _ ->
            Message.show debug "Show :: Non List Case";
            finishedIter ()
        (*  synthesize gamma sigma delta spec learnConst !bidirectional !maxPathLength
    *)

and isynthesizeIf gamma sigma delta spec debug maxPath : Syn.typedMonExp iter =
    if maxPath == 0 then finishedIter () else
    let () = Message.show debug ("Show ::::::::::::::: iSynthesize If THEN ELSE "^(RefTy.toString spec)) in
    let debug = (Message.incr_depth debug) in
    (*val createGammai Gamma, t : (Gamma *ptrue * pfalse)*)
    let createGammai gamma t  =
        match t with
            | RefTy.Base (vn, _, pn) ->
                (*create a new var newvar for vn.
                generate truepredicate [newvar/vn]pn /\ [newvar = true]
                generate falsepredicate [newvar/vn]pn /\ [newvar = false]
                add newvar to Gamma

                *)
                let newvar = Var.get_fresh_var "v" in
                let newvarString =Var.toString newvar in
                let truep = Predicate.Conj (Predicate.Base (BP.Eq (BP.Var newvarString, (BP.Bool true))),
                                Predicate.applySubst (newvar, vn) pn) in
                let falsep = Predicate.Conj(Predicate.Base (BP.Eq (BP.Var newvarString, (BP.Bool false))),
                                Predicate.applySubst (newvar, vn) pn) in
                let gamma = VC.extend_gamma (newvar, t) gamma  in
                (gamma, truep, falsep)

            | MArrow (_, _, (vn, tn), (Predicate.Forall (bvs, predBool) as postBool)) ->
                Message.show debug ("RefTy "^(RefTy.toString t));
                Message.show debug ("Post "^(Predicate.toString postBool));
                let newvar = Var.get_fresh_var "v" in
                let newvarString =Var.toString newvar in

                let truep = Predicate.Conj (Predicate.Base (BP.Eq (BP.Var newvarString, (BP.Bool true))),
                                Predicate.applySubst (newvar, vn) predBool) in
                let falsep = Predicate.Conj(Predicate.Base (BP.Eq (BP.Var newvarString, (BP.Bool false))),
                                Predicate.applySubst (newvar, vn)  predBool) in
                let gamma = VC.extend_gamma (newvar, tn) gamma  in

                (gamma, truep, falsep)

            | _ -> raise (SynthesisException "Case must be handled in Pure Effect");
    in

    (*synthesize a boolean / rather we need to synthesize all the booleans
    now we synthesize a list of boolean scalars*)
    let v = Var.get_fresh_var "v" in
    let boolSpec = RefTy.Base (v, TyD.Ty_bool, Predicate.True) in
    Message.show debug ("Show :: iSynthesize Boolean "^(RefTy.toString boolSpec));

    let bi_list = esynthesizeScalar gamma sigma delta [boolSpec] (Message.incr_depth debug) (maxPath -1) in

    nestedIter (fun eb -> (*get the predicate \phi in the If-rule for synthesis*)
        (*either a fun-application or *)
        let eb_expmon = eb.expMon in
        (*type for the eb_expmon*)
        let eb_type = eb.ofType in
        let refTy4bi = eb_type in
        Message.show debug ("Show :: iSynthesize Boolean Successful "^(Syn.monExp_toString eb_expmon));
        Message.show debug ("Show :: iSynthesize Boolean Successful "^(RefTy.toString eb_type));
        (*create true predicate = \phi /\ [v= true] & false predicate = \phi /\ [v=false]*)

        let (gamma, true_pred4bi, false_pred4bi) = createGammai gamma refTy4bi in
        let delta_true = Predicate.Conj (delta, true_pred4bi) in
        Message.show debug ("Show :: Synthesizing the true branch");
        Message.show debug ("Show :: True Predicate "^(Predicate.toString true_pred4bi));

        (*\Gamma, [v=true]\phi |- spec ~~~> t_true*)
        let t_true = synthesize gamma sigma delta_true spec (Message.incr_depth debug) (maxPath -1) in

        Message.show debug ("Show :: Successfully Synthesisized the True Branch Now Trying False Branch");
        let delta_false = Predicate.Conj (delta, false_pred4bi) in
        (*\Gamma, [v=false]\phi |- spec ~~~> t_false*)
        Message.show debug ("Show :: Synthesizing the false branch");
        Message.show debug ("Show :: False Predicate "^(Predicate.toString false_pred4bi));

        let t_false = synthesize gamma sigma delta_false spec (Message.incr_depth debug) (maxPath -1) in

        mapFilterIter (
                fun (exp_true, exp_false) ->
                Message.show debug ("Show :: Successfully Synthesisized False Branch ");
                let monexp_t_true = exp_true.expMon in
                let monexp_t_false = exp_false.expMon in
                let eite_exp = Syn.Eite (eb_expmon, monexp_t_true, monexp_t_false) in
                Some {Syn.expMon = eite_exp; Syn.ofType = spec}
            ) (productIter t_true t_false)

    ) bi_list


let toplevel gamma sigma delta types quals spec learning bi maxPath efilter components examples : (Syn.typedMonExp option) =
    learningOn := learning;
    bidirectionalOn := bi;
    efilterOn := efilter;
    typenames := types;
    qualifiers := quals;
    let debug = (Message.create true) in
    let res = synthesize gamma sigma delta spec debug maxPath in

    let outres = mapFilterIter (fun a ->
        let a = {expMon= a.expMon; ofType = spec} in
        let prog = Lambdasyn.typedMonExp_toOcaml a in

        Printf.eprintf "\n%s" prog;

        let oc = open_out "test.ml" in
        Printf.fprintf oc "%s\n%s\n%s" components (prog) examples;
        close_out oc;
        (* let _ = Unix.alarm 1 in *)
        match Sys.command "ocamlopt test.ml && ./a.out" with
        | 0 -> Some a
        | _ -> None) res in

    outres.value