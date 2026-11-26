import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedResidualGain
import Reg.Support.DependentFamily

/-! The squared discrepancy readout varies with the integer position. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedResidualGain

open _root_.D5.S1.Words.Patterns.Separable.OccupiedResidualGain
open _root_.D5.S1.Words.Patterns.Separable.OccupiedActualPowerGenerator
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A z => A * (discrepancyProfile z) ^ 2) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / Real.log 2 + 1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ A > (0 : ℝ), ∃ N : ℕ, ∀ z : ℤ, (N : ℤ) < |z| →
      R.readout () A z ≤ actualGenerator discrepancyProfile z

private theorem profile_nonneg (z : ℤ) : 0 ≤ discrepancyProfile z := by
  unfold discrepancyProfile
  have h : 1 < (2 : ℝ) + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  exact one_div_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.log_pos h).le)

private theorem profile_upper (z : ℤ) : discrepancyProfile z ≤ 1 / Real.log 2 := by
  unfold discrepancyProfile
  have h : (2 : ℝ) ≤ 2 + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  have hs : 1 ≤ Real.sqrt (2 + |(z : ℝ)|) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h
  apply one_div_le_one_div_of_le (Real.log_pos (by norm_num))
  simpa only [one_mul] using
    (mul_le_mul hs hl (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))

private theorem generator_upper (z : ℤ) :
    actualGenerator discrepancyProfile z ≤ 1 / Real.log 2 := by
  let w (i : ℕ) := kernelWeight i *
    (discrepancyProfile (z + (i + 1 : ℕ)) +
      discrepancyProfile (z - (i + 1 : ℕ)) - 2 * discrepancyProfile z)
  let v (i : ℕ) := kernelWeight i * (2 * (1 / Real.log 2))
  change (∑' i, w i) ≤ _
  by_cases hs : Summable w
  · have hv : Summable v := critical_shape_masses.2.2.1.mul_right _
    have hw : ∀ i, w i ≤ v i := by
      intro i
      have hk : 0 ≤ kernelWeight i := by unfold kernelWeight shapeWeight rho; positivity
      dsimp only [w, v]
      apply mul_le_mul_of_nonneg_left _ hk
      linarith only [profile_upper (z + (i + 1 : ℕ)), profile_upper (z - (i + 1 : ℕ)),
        profile_nonneg z]
    refine (hs.tsum_le_tsum hw hv).trans_eq ?_
    dsimp only [v]
    rw [tsum_mul_right, critical_shape_masses.2.2.2.1]
    ring
  · rw [tsum_eq_zero_of_not_summable hs]
    exact one_div_nonneg.mpr (Real.log_pos (by norm_num)).le

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨A, hA, N, H⟩
  have hz : (N : ℤ) < |((N + 1 : ℕ) : ℤ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.lt_succ_self N
  have h := H _ hz
  change 1 / Real.log 2 + 1 ≤ actualGenerator discrepancyProfile ((N + 1 : ℕ) : ℤ) at h
  linarith only [h, generator_upper ((N + 1 : ℕ) : ℤ)]

def family : Registration arena (type_of% @eventual_discrepancy_linear_gain) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_discrepancy_linear_gain, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    change (1 : ℝ) * discrepancyProfile 1 ^ 2 ≠ 1 * discrepancyProfile 2 ^ 2
    rw [one_mul, one_mul]
    have hd : Real.sqrt 3 * Real.log 3 < Real.sqrt 4 * Real.log 4 := by
      have hlog : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      calc
        _ < Real.sqrt 3 * Real.log 4 :=
          mul_lt_mul_of_pos_left hlog (Real.sqrt_pos.mpr (by norm_num))
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num))
          (Real.log_nonneg (by norm_num))
    have hf : discrepancyProfile 2 < discrepancyProfile 1 := by
      simpa [discrepancyProfile, show (2 : ℝ) + 1 = 3 by norm_num,
        show (2 : ℝ) + 2 = 4 by norm_num] using
        (one_div_lt_one_div_of_lt (mul_pos (Real.sqrt_pos.mpr (by norm_num))
          (Real.log_pos (by norm_num))) hd)
    exact (pow_lt_pow_left₀ hf (profile_nonneg _) (by norm_num : 2 ≠ 0)).ne'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_discrepancy_linear_gain) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedResidualGain.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedResidualGain.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A z => A * (discrepancyProfile z) ^ 2)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedResidualGain
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedResidualGain
