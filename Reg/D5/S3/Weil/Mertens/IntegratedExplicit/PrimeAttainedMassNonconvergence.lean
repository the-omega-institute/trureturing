import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence
import Reg.Support.SingleDependentReadout

/-! The real part used to select and normalize at the supplied zero controls the limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence
  (prime_tail_mass_no_finite_limit_of_attained_zero)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Complex.re) (fun e => nomatch e)

def exaggeratedRealPart : Realization signature :=
  realize signature (fun _ _ _ => 5 / 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (ρ : ℂ), IsNontrivialZero ρ →
    let β := V.readout () () ρ
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → z.re ≤ β) →
      ∀ (κ L : ℝ), 1 < κ →
        ¬ Tendsto (fun B : ℝ =>
          (∫ x in B / κ..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2))
          atTop (𝓝 L)

private theorem exaggerated_real_part_fails : ¬ arena.Law exaggeratedRealPart := by
  intro law
  have hexcludes := law (actualData.zero 0) (actualData.zero_isNontrivial 0)
    (by norm_num [exaggeratedRealPart, realize])
    (fun z hz => hz.2.2.le.trans (by norm_num [exaggeratedRealPart, realize]))
    2 0 (by norm_num)
  change ¬ Tendsto (fun B : ℝ =>
    (∫ x in B / 2..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ ((5 / 2 : ℝ) - 1 / 2))
    atTop (𝓝 0) at hexcludes
  rw [show (5 / 2 : ℝ) - 1 / 2 = 2 by norm_num] at hexcludes
  simp only [Real.rpow_two] at hexcludes
  apply hexcludes
  have htail : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (htail.eventually_const_lt (show (-1 : ℝ) < 0 by norm_num))
  have hshift : Tendsto (fun B : ℝ => B / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝 0))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x))) (sq_nonneg B)
  · filter_upwards [hshift.eventually_ge_atTop (max 1 X)] with B hleft
    have hA : 1 ≤ B / 2 := (le_max_left _ _).trans hleft
    have hB : 0 < B := by linarith
    have hAB : B / 2 ≤ B := by linarith
    have hx (x : ℝ) (hmem : x ∈ Icc (B / 2) B) : 1 ≤ x := hA.trans hmem.1
    have hcont : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Icc (B / 2) B) :=
      ((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hx).neg.sup continuousOn_const).div
        Real.continuous_sqrt.continuousOn
        (fun x hmem => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx x hmem))).ne')
    have hmass : (∫ x in B / 2..B, max (-primeTail x) 0 / Real.sqrt x) ≤ B := by
      calc
        _ ≤ ∫ _ in B / 2..B, (1 : ℝ) := by
          apply intervalIntegral.integral_mono_on hAB (hcont.intervalIntegrable_of_Icc hAB)
            intervalIntegrable_const
          intro x hmem
          have hs : 1 ≤ Real.sqrt x := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (hx x hmem)
          have ht := hX x ((le_max_right _ _).trans (hleft.trans hmem.1))
          apply (div_le_iff₀ (zero_lt_one.trans_le hs)).2
          rw [one_mul]
          exact (max_le (by linarith only [ht]) (by norm_num)).trans hs
        _ ≤ B := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
          linarith
    calc
      _ ≤ B / B ^ 2 := div_le_div_of_nonneg_right hmass (sq_nonneg B)
      _ = B⁻¹ := by field_simp

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena (type_of% @prime_tail_mass_no_finite_limit_of_attained_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_mass_no_finite_limit_of_attained_zero, exaggeratedRealPart,
    exaggerated_real_part_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual exaggeratedRealPart exaggerated_real_part_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_mass_no_finite_limit_of_attained_zero) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_mass_no_finite_limit_of_attained_zero "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Complex.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedMassNonconvergence
