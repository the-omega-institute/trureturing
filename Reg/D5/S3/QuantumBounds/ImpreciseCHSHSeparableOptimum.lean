import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp calibrated separable CHSH value. -/

namespace Reg.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum

open _root_.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
open _root_.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness (Separable)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the optimal separable value as calibration inaccuracy varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ε => separableValue ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete attained optimum and its calibration interval. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ ε ∈ Set.Icc (0 : ℝ) 1,
    IsGreatest {w | ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧
      Admissible ε a₁ a₂ b₁ b₂ ∧ w = witness ρ a₁ a₂ b₁ b₂} (r.readout () () ε)

private theorem value_zero : separableValue 0 = Real.sqrt 2 := by
  have hthreshold : (0 : ℝ) ≤ 1 / 2 - 1 / (2 * Real.sqrt 2) := by
    have h : (1 : ℝ) / (2 * Real.sqrt 2) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [Real.one_lt_sqrt_two]
    linarith
  rw [separableValue, ite_eq_left hthreshold]
  norm_num

private theorem value_one : separableValue 1 = 2 := by
  have hthreshold : ¬ (1 : ℝ) ≤ 1 / 2 - 1 / (2 * Real.sqrt 2) := by
    have h : (0 : ℝ) < 1 / (2 * Real.sqrt 2) := by positivity
    linarith
  rw [separableValue, ite_eq_right hthreshold]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0 (by constructor <;> norm_num)).unique
    (result 0 (by constructor <;> norm_num))
  change (0 : ℝ) = separableValue 0 at hbad
  rw [value_zero] at hbad
  exact (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) hbad.symm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change separableValue 0 ≠ separableValue 1
  rw [value_zero, value_one]
  intro h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h] at hs
  norm_num at hs

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
      (@_root_.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.unit
  realizationName :=
    `Reg.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.source_registration
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
    (realize signature (fun _ _ ε => separableValue ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
    definition := some {
      owner := `D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
      name := `D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
