import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the normalization coordinate in higher-order EPR tightness. -/

namespace Reg.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness

open _root_.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the squared norm of a finite two-mode occupation state. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ × ℕ →₀ ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ψ => normSq ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both signs, every positive order and tolerance, and the complete state condition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n → ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
    ∀ ε : ℝ, 0 < ε → ∃ ψ : ℕ × ℕ →₀ ℂ,
      R.readout () () ψ = 1 ∧ normSq (annihilateA n ψ + σ • createB n ψ) < ε

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ψ, hψ, _⟩ := h 1 (by norm_num) 1 (Or.inl rfl) 1 (by norm_num)
  change (0 : ℝ) = 1 at hψ
  exact zero_ne_one hψ

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Finsupp.single (0, 0) 1, ?_⟩
  change normSq 0 ≠ normSq (Finsupp.single (0, 0) 1)
  simp [normSq]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.unit
  realizationName := `Reg.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ψ => normSq ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
    definition := some {
      owner := `D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
      name := `D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.FockSpace.HigherOrderEPRTightness
