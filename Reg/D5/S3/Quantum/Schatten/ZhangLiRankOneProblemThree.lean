import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

/-! The full finite-attainment statement with its minimum comparison exposed. -/

namespace Reg.D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
open Matrix
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Result

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.rank ≤ 1 → ∀ ν : UINorm n,
    ∃ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        ν.N ((σ.permMatrix ℂ) ⊙ G) ≤ ν.N ((τ.permMatrix ℂ) ⊙ G)) ∧
      (∀ W : Matrix (Fin n) (Fin n) ℂ, IsUnit W.det →
        R.readout () () (ν.N ((σ.permMatrix ℂ) ⊙ G) ^ 2)
          (ν.N (W ⊙ G) * ν.N (W⁻¹ ⊙ Gᵀ))) ∧
      ν.N ((σ.permMatrix ℂ) ⊙ G) * ν.N ((σ.permMatrix ℂ)⁻¹ ⊙ Gᵀ) =
        ν.N ((σ.permMatrix ℂ) ⊙ G) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨σ, _, hproduct, _⟩ := h 0 0 (by simp) zeroDimNorm
  exact hproduct 1 (by simp)

def source_registration : Registration arena (type_of% @result) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree.Result.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
    definition := some {
      owner := `D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
      name := `D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Result

end
end Reg.D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
