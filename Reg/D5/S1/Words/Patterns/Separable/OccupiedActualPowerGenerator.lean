import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
import Reg.Support.DependentFamily

/-! The uniform generator error allowance varies with the normalization scale. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator

open _root_.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ C r => C * r ^ (-(1 / 80 : ℝ))) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ A > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ β : ℝ, 1 / 2 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 4 ^ 20 ≤ n →
        |(n : ℝ) ^ (β + 1 / 2) * actualGenerator (powerProfile β) (n : ℤ) - A * J β| ≤
          R.readout () C (n : ℝ) ∧
        A * (gapCoefficient * (β - 1 / 2)) - C * (n : ℝ) ^ (-(1 / 80 : ℝ)) ≤
          (n : ℝ) ^ (β + 1 / 2) * actualGenerator (powerProfile β) (n : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨A, hA, C, hC, H⟩
  have h := (H (1 / 2) le_rfl (by norm_num) (4 ^ 20) le_rfl).1
  change _ ≤ (-1 : ℝ) at h
  exact (not_le_of_gt (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (abs_nonneg _))) h

def family : Registration arena (type_of% @actual_generator_power_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_generator_power_comparison, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨1, (4 : ℝ) ^ (20 : ℕ), 2 * (4 : ℝ) ^ (20 : ℕ), ?_⟩
    change (1 : ℝ) * ((4 : ℝ) ^ (20 : ℕ)) ^ (-(1 / 80 : ℝ)) ≠
      1 * (2 * (4 : ℝ) ^ (20 : ℕ)) ^ (-(1 / 80 : ℝ))
    exact (mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_neg (by positivity) (by norm_num) (by norm_num))
      (by norm_num : (0 : ℝ) < 1)).ne'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_generator_power_comparison) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ C r => C * r ^ (-(1 / 80 : ℝ)))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
