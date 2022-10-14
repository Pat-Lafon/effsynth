module VC = VerificationC

module Message : sig
    val depth : int ref
end

val z3_log : string -> unit

type result = Success | Undef | Failure

val discharge : VC.standardt -> (SpecLang.Var.t list) ->
                    (SpecLang.RelSpec.Qualifier.t list)
                    ->  result
