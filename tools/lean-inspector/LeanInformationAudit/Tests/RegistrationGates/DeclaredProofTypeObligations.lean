import LeanInformationAudit.Tests.RegistrationGates.DeclaredObligations

namespace LeanInformationAudit.Tests.DeclaredProofTypeObligations
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open DeclaredObligations (boundProof)

def hiddenBound (n m : Nat) : Prop :=
  (fun (_h : Nat.lt n (Nat.succ n)) => Nat.lt m (Nat.succ m)) (boundProof n)

theorem hiddenProof (n m : Nat) : hiddenBound n m := Nat.lt_succ_self m

def template (n m : Nat) : PrimitiveRealization (cutSignature Bool (Fin (Nat.succ m))) :=
  cutRealization (fun _ : Bool => ⟨m, hiddenProof n m⟩)

register_information_template template

def targetArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool (Fin 2)
  Law _ := Nat.lt 0 (Nat.succ 0)

def independentArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool (Fin 2)
  Law _ := Nat.lt 2 (Nat.succ 2)

instance : DecidableEq targetArena.State := instDecidableEqBool
instance : DecidableEq independentArena.State := instDecidableEqBool

information_theorem target in targetArena primitives (template 0 1)
  : Nat.lt 0 (Nat.succ 0) := Nat.zero_lt_succ 0
information_theorem independent in independentArena primitives (template 0 1)
  : Nat.lt 2 (Nat.succ 2) := Nat.lt_succ_self 2

run_meta do
  for (name, label, shouldValidate) in #[
      (``target, "proof_type_plan_discarded_input_rejected", false),
      (``independent, "proof_type_plan_independent_input_accepted", true)] do
    let some event := (TemplateBinding.inventory (← getEnv)).find? (·.key.theoremName == name)
      | throwError "setup: missing native registration"
    let descriptor ← mkAppM ``template #[mkNatLit 0, mkNatLit 1]
    let record ← TemplateBinding.assess event (some {
      key := event.key, arena := event.arena, descriptor := some descriptor,
      owner := (← getEnv).header.mainModule })
    let (ok, result) := match record.result with
      | .declaredValidated _ => (shouldValidate, "validated")
      | .declaredUnresolved diagnostic =>
        (!shouldValidate && (diagnostic.splitOn
          "reason=forbidden_dependency rule=dtr.instantiated_type site=").length == 2, diagnostic)
      | .undeclared => (false, "undeclared")
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"actual={result}"

end LeanInformationAudit.Tests.DeclaredProofTypeObligations
