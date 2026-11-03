import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
import Reg.Support.DependentFamily

/-! Source-bound audit of bound coherence in every dimension at least three. -/

namespace Reg.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions

open _root_.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe a matrix's coherence at the specified dimension and mode index. -/
abbrev signature : Signature where
  Params := Σ _d : ℕ, ℕ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ρ => modeCoherence p.2 ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain the state conditions and all allowed interactions and positive modes. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 3 ≤ d → ∃ ρ : Matrix (Fin d) (Fin d) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ * numberOp d ≠ numberOp d * ρ ∧
      ¬ IsMaximallyCoherent ρ ∧
      ∀ v, IsAllowedUnitary v → ∀ j : ℕ, 1 ≤ j → j ≤ d - 1 →
        modeCoherence j (concentrated v ρ) ≤ R.readout () ⟨d, j⟩ ρ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, _, _, _, _, hρ⟩ := h 3 (by omega)
  have hunit : IsAllowedUnitary (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) := by
    constructor
    · exact one_mem _
    · simp
  have hbad := hρ 1 hunit 1 (by omega) (by omega)
  change modeCoherence 1 (concentrated 1 ρ) ≤ -1 at hbad
  have hnonneg := traceNorm_nonneg (mode 1 (concentrated 1 ρ))
  change 0 ≤ modeCoherence 1 (concentrated 1 ρ) at hnonneg
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  have hz : mode 0 (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    ext r s
    simp [mode]
  have ho : mode 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    ext r s
    fin_cases r
    fin_cases s
    simp [mode]
  change modeCoherence 0 (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠ modeCoherence 0 1
  rw [modeCoherence, modeCoherence, hz, ho]
  norm_num [traceNorm, Matrix.trace, Matrix.diag]

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
      (@_root_.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p ρ => modeCoherence p.2 ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
    definition := some {
      owner := `D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
      name := `D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions.claim
      path := #[] }
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
