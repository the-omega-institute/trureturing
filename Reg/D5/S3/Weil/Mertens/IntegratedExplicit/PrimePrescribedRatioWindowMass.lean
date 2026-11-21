import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass
import Reg.Support.SingleDependentReadout

/-! The abscissa cutoff restricts both the unattainment test and the exponents
admitted by the mass estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass
  (prime_tail_prescribed_ratio_mass_of_unattained)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ β => Iio β) (fun e => nomatch e)

def raisedCutoff : Realization signature :=
  realize signature (fun _ _ _ => Iio 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V :=
    let belowAbscissa := V.readout () () zeroAbscissa
    (∀ z : ℂ, IsNontrivialZero z → z.re ∈ belowAbscissa) →
      ∀ {κ σ : ℝ}, 1 < κ → 1 / 2 < σ → σ ∈ belowAbscissa →
        ∃ c S : ℝ, 0 < c ∧ ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A →
          κ * A ≤ B → c * B ^ (σ - 1 / 2) ≤
            ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x

private theorem raised_cutoff_fails : ¬ arena.Law raisedCutoff := by
  intro hlaw
  have hun : ∀ z : ℂ, IsNontrivialZero z → z.re ∈ Iio (3 : ℝ) := by
    intro z hz
    exact hz.2.2.trans (by norm_num)
  obtain ⟨c, S, hc, hbound⟩ := hlaw hun (κ := 2) (σ := 5 / 2) (by norm_num) (by norm_num)
    (show (5 / 2 : ℝ) < 3 by norm_num)
  have hlim : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (hlim.eventually_const_lt (show (-1 : ℝ) < 0 by norm_num))
  let A : ℝ := max 2 X
  let B : ℝ := max (max S (2 * A)) (c⁻¹ + 1)
  have hA : 2 ≤ A := le_max_left _ _
  have hratio : 2 * A ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hAB : A ≤ B := by linarith only [hA, hratio]
  have hB₀ : 0 < B := by linarith only [hA, hAB]
  have hlarge : c⁻¹ + 1 ≤ B := le_max_right _ _
  have hlower := hbound B ((le_max_left _ _).trans (le_max_left _ _)) A hA hratio
  rw [show (5 / 2 : ℝ) - 1 / 2 = 2 by norm_num, Real.rpow_two] at hlower
  have hupper : (∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x) ≤ B := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := A) (b := B) (C := 1) (f := fun x => max (-primeTail x) 0 / Real.sqrt x) (by
        intro x hx
        rw [uIoc_of_le hAB] at hx
        have hs : 1 ≤ Real.sqrt x := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (one_le_two.trans (hA.trans hx.1.le))
        have ht := hX x ((le_max_right _ _).trans hx.1.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))]
        apply (div_le_iff₀ (zero_lt_one.trans_le hs)).2
        rw [one_mul]
        exact (max_le (by linarith only [ht]) zero_le_one).trans hs)
    rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hAB)] at hnorm
    exact (le_abs_self _).trans (hnorm.trans (by linarith only [hA]))
  have hcB : 1 < c * B := by
    have h := mul_le_mul_of_nonneg_left hlarge hc.le
    rw [mul_add, mul_inv_cancel₀ hc.ne', mul_one] at h
    linarith only [h, hc]
  have hcontr := mul_lt_mul_of_pos_right hcB hB₀
  exact (show B < c * B ^ 2 by simpa only [one_mul, pow_two, mul_assoc] using hcontr).not_ge
    (hlower.trans hupper)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Iio (0 : ℝ) ≠ Iio 1
  intro heq
  have hz : (0 : ℝ) ∈ Iio 1 := mem_Iio.mpr zero_lt_one
  rw [← heq] at hz
  exact (lt_irrefl (0 : ℝ)) hz

def family : Registration arena (type_of% @prime_tail_prescribed_ratio_mass_of_unattained) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_prescribed_ratio_mass_of_unattained, raisedCutoff, raised_cutoff_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual raisedCutoff raised_cutoff_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_prescribed_ratio_mass_of_unattained) (Realization signature) Unit Unit where
  unitName := .str ``prime_tail_prescribed_ratio_mass_of_unattained "__information_unit"
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
    (fun _ _ β => Iio β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass
