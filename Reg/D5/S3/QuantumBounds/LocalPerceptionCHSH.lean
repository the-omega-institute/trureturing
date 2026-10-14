import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.LocalPerceptionCHSH
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumBounds.LocalPerceptionCHSH
open _root_.D5.S3.QuantumBounds.LocalPerceptionCHSH
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the real CHSH score at its density-matrix coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ρ => lpoCHSH ρ p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

/-- Preserve every state and setting hypothesis and the complete attainment clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ ρ, ρ.PosSemidef → trace ρ = 1 → ∀ A B : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x, IsDichotomic (A x)) → (∀ y, IsDichotomic (B y)) →
        R.readout () ⟨A, B⟩ ρ ≤ 2) ∧
    (∃ ρ A B, ρ.PosSemidef ∧ trace ρ = 1 ∧ (∀ x, IsDichotomic (A x)) ∧
      (∀ y, IsDichotomic (B y)) ∧ lpoCHSH ρ A B = 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, A, B, hρ, htr, hA, hB, _⟩ := result.2
  have bad := h.1 ρ hρ htr A B hA hB
  change (3 : ℝ) ≤ 2 at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨ρ, A, B, _, _, _, _, hval⟩ := result.2
  refine ⟨⟨A, B⟩, ρ, 0, ?_⟩
  change lpoCHSH ρ A B ≠ lpoCHSH 0 A B
  rw [hval]
  norm_num [lpoCHSH, meanA, meanB, correl]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.LocalPerceptionCHSH.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.LocalPerceptionCHSH.unit
  realizationName := `Reg.D5.S3.QuantumBounds.LocalPerceptionCHSH.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ρ => lpoCHSH ρ p.1 p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.LocalPerceptionCHSH
    definition := some {
      owner := `D5.S3.QuantumBounds.LocalPerceptionCHSH
      name := `D5.S3.QuantumBounds.LocalPerceptionCHSH.claim
      path := #[] }
    coordinates := #[3, 4]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.LocalPerceptionCHSH
