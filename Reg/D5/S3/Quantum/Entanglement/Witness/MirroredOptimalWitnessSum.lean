import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
import Reg.Support.DependentFamily

/-! Source-bound audit of the optimal sum of two entanglement witnesses. -/

namespace Reg.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum

open _root_.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sum while varying the second witness at each dimension and first witness. -/
abbrev signature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
  State p := Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M => p.2 + M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain optimality and all three detection-set clauses of the original claim. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 3 ≤ d →
    ∃ W M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      IsOptimalWitness W ∧ IsOptimalWitness M ∧
      IsOptimalWitness (R.readout () ⟨d, W⟩ M) ∧
      (∃ ρ, Detects W ρ ∧ ¬ Detects M ρ) ∧
      (∃ ρ, Detects M ρ ∧ ¬ Detects W ρ) ∧
      (∃ ρ, Detects W ρ ∧ Detects M ρ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨W, M, _, _, hsum, _⟩ := h 3 (by norm_num)
  obtain ⟨ρ, _, hnegative⟩ := hsum.1.2.2
  change ((0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) * ρ).trace.re < 0 at hnegative
  simp at hnegative

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, 0⟩, 0, 1, ?_⟩
  change (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) + 0 ≠ 0 + 1
  simp

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => p.2 + M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
      name := `D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
