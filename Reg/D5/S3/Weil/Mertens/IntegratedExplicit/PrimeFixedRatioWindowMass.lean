import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
import Reg.Support.SingleDependentReadout

/-! The fixed-ratio estimate depends on the real part used in the threshold and exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re)
    (fun e => nomatch e)

def exaggeratedRealPart : Realization signature :=
  realize signature (fun _ _ _ => 5 / 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (ρ : ℂ), IsNontrivialZero ρ →
    let β := V.readout () () ρ
    1 / 2 < β → ∃ κ c S : ℝ, 1 < κ ∧ 0 < c ∧ ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A →
      κ * A ≤ B → c * B ^ (β - 1 / 2) ≤
        ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x

private theorem exaggerated_real_part_fails : ¬ arena.Law exaggeratedRealPart := by
  intro h
  obtain ⟨κ, c, S, hκ, hc, hbound⟩ :=
    h (actualData.zero 0) (actualData.zero_isNontrivial 0) (by norm_num [exaggeratedRealPart, realize])
  have hlim : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (hlim.eventually_const_lt (by norm_num : (-1 : ℝ) < 0))
  let A : ℝ := max 2 X
  let B : ℝ := max (max S (κ * A)) (c⁻¹ + 1)
  have hA : 2 ≤ A := le_max_left _ _
  have hA₀ : 0 < A := (by norm_num : (0 : ℝ) < 2).trans_le hA
  have hBA : κ * A ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hAB : A ≤ B := (le_mul_of_one_le_left hA₀.le hκ.le).trans hBA
  have hB₀ := hA₀.trans_le hAB
  have hlarge : c⁻¹ + 1 ≤ B := le_max_right _ _
  have hlower := hbound B ((le_max_left _ _).trans (le_max_left _ _)) A hA hBA
  change c * B ^ ((5 / 2 : ℝ) - 1 / 2) ≤ _ at hlower
  rw [show (5 / 2 : ℝ) - 1 / 2 = 2 by norm_num, Real.rpow_two] at hlower
  have hx (x : ℝ) (hx : x ∈ Icc A B) : 1 ≤ x :=
    one_le_two.trans (hA.trans hx.1)
  have hm : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Icc A B) :=
    ((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hx).neg.sup continuousOn_const).div
      Real.continuous_sqrt.continuousOn
      (fun x hmem => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx x hmem))).ne')
  have hupper : (∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x) ≤ B := by
    calc
      _ ≤ ∫ _ in A..B, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hAB (hm.intervalIntegrable_of_Icc hAB)
          intervalIntegrable_const
        intro x hmem
        have hs : 1 ≤ Real.sqrt x := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (hx x hmem)
        have ht := hX x ((le_max_right _ _).trans hmem.1)
        apply (div_le_iff₀ (zero_lt_one.trans_le hs)).2
        rw [one_mul]
        exact (max_le (by linarith only [ht]) (by norm_num)).trans hs
      _ ≤ B := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; linarith
  have hcB : 1 < c * B := by
    have h := mul_le_mul_of_nonneg_left hlarge hc.le
    rw [mul_add, mul_inv_cancel₀ hc.ne', mul_one] at h
    linarith only [h, hc]
  have hcontr := mul_lt_mul_of_pos_right hcB hB₀
  have hcb : B < c * B ^ 2 := by simpa only [one_mul, pow_two, mul_assoc] using hcontr
  exact hcb.not_ge (hlower.trans hupper)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena (type_of% @prime_tail_fixed_ratio_mass_of_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_fixed_ratio_mass_of_zero, exaggeratedRealPart, exaggerated_real_part_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual exaggeratedRealPart exaggerated_real_part_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_fixed_ratio_mass_of_zero) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_fixed_ratio_mass_of_zero "__information_unit"
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
  readout := some (realize signature
    (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
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

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
