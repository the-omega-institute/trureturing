import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
import Reg.Support.DependentFamily

/-! The real logarithm in the exact closed form changes with the spatial base. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture

open _root_.D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
open _root_.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

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
  realize signature (fun _ _ x => Real.log x) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ z : ℤ,
      let X : ℝ := 2 + |(z : ℝ)|
      actualGenerator truncatedProfile z =
        (∫ s in (0 : ℝ)..(1 / 4), actualGenerator (powerProfile (1 / 2 + s)) z) ∧
      truncatedProfile z =
        (1 - X ^ (-(1 / 4 : ℝ))) / (Real.sqrt X * R.readout () () X)) ∧
    (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      c / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) ≤ actualGenerator truncatedProfile (n : ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law.1 0).2
  change truncatedProfile 0 = _ / (Real.sqrt _ * (0 : ℝ)) at h
  have hzero : truncatedProfile 0 = 0 := by simpa using h
  have hEq : truncatedProfile 0 =
      (1 - (2 : ℝ) ^ (-(1 / 4 : ℝ))) / (Real.sqrt 2 * Real.log 2) := by
    simpa using (truncated_profile_analysis.1 0).2
  have hp : (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hpos : 0 < truncatedProfile 0 := by
    rw [hEq]
    exact div_pos (sub_pos.mpr hp)
      (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.log_pos (by norm_num)))
  exact hpos.ne' hzero

def family : Registration arena (type_of% @truncated_profile_analysis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@truncated_profile_analysis, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    change Real.log 2 ≠ Real.log 3
    exact (Real.log_lt_log (by norm_num) (by norm_num)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@truncated_profile_analysis) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
