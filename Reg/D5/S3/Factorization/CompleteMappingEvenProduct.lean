import D5.S3.Factorization.CompleteMappingEvenProduct
import Reg.Support.DependentFamily

open _root_.D5.S3.Factorization.CompleteMappingEvenProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Factorization.CompleteMappingEvenProduct

abbrev signature : Signature where
  Params := ℕ
  State m := ZMod 2 × ZMod (2 * m)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := ZMod 2 × ZMod (2 * m)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m x => x + theta m x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 0 < m →
    Function.Bijective (theta m) ∧ Function.Bijective (R.readout () m)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hinj := (h 1 (by omega)).2.1
  have heq : ((0, 0) : ZMod 2 × ZMod 2) = (1, 0) := hinj (by rfl)
  norm_num at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun m hm => theta_complete m hm, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨1, (0, 0), (1, 0), ?_⟩
    change (0, 0) + theta 1 (0, 0) ≠ (1, 0) + theta 1 (1, 0)
    decide

register_information_theorem theta_complete in arena
  readout via (realize signature (fun _ m x => x + theta m x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.CompleteMappingEvenProduct
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      functionOperand := true }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Factorization.CompleteMappingEvenProduct.theta_complete
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "complete-mapping registration is not declaredValidated"

#print axioms registration

end Reg.D5.S3.Factorization.CompleteMappingEvenProduct
