/- GID: D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit
   generality: I
   mirror-B: D5/B/S3/Analytic/MomentMinors/BoundedFifthMomentLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp Meer–Weeks fifth central moment bounds for laws bounded on one side. -/

import D5.S3.Analytic.MomentMinors.Defs
import Mathlib.Probability.Moments.Basic

/-! Fifth central moment bounds from a nonnegative quintic certificate. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open D5.S3.Analytic.MomentMinors.Defs (mean)

namespace D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit

/-- The standardized fifth moment of the extremal two-point law. -/
def fifthBound (z : ℝ) : ℝ := z ^ 3 - z + z⁻¹ - z⁻¹ ^ 3

/-- The fifth central moment bounds for arbitrary real probability laws with
finite fifth absolute moment and positive variance. -/
def claim : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    Integrable (fun x : ℝ => |x| ^ 5) μ → 0 < centralMoment id 2 μ →
    (∀ L : ℝ, (∀ᵐ x ∂μ, L ≤ x) →
      fifthBound (Real.sqrt (centralMoment id 2 μ) / (mean μ - L)) ≤
        centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5) ∧
    (∀ U : ℝ, (∀ᵐ x ∂μ, x ≤ U) →
      centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 ≤
        -fifthBound (Real.sqrt (centralMoment id 2 μ) / (U - mean μ)))

private lemma integrable_centered_pow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (c : ℝ) (k : ℕ) (hk : k ≤ 5) :
    Integrable (fun x : ℝ => (x - c) ^ k) μ := by
  have hLp : MemLp (fun x : ℝ => x) 5 μ := by
    apply (integrable_norm_rpow_iff measurable_id.aestronglyMeasurable
      (by norm_num : (5 : ℝ≥0∞) ≠ 0) (by norm_num : (5 : ℝ≥0∞) ≠ ∞)).mp
    simpa using h
  have hcenter := (hLp.sub (memLp_const c)).mono_exponent
    (show (k : ℝ≥0∞) ≤ 5 by exact_mod_cast hk)
  apply (integrable_norm_iff (f := fun x : ℝ => (x - c) ^ k) (by fun_prop)).mp
  simpa only [norm_pow, Pi.sub_apply] using hcenter.integrable_norm_pow'

private lemma mean_gap_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (L : ℝ) (hL : ∀ᵐ x ∂μ, L ≤ x) : 0 < mean μ - L := by
  have hi : Integrable (fun x : ℝ => x) μ := by
    simpa only [sub_zero, pow_one] using integrable_centered_pow μ h 0 1 (by decide)
  have hshift : Integrable (fun x : ℝ => x - L) μ := hi.sub (integrable_const L)
  have he : (∫ x : ℝ, x - L ∂μ) = mean μ - L := by
    rw [integral_sub hi (integrable_const L)]
    rw [integral_const, probReal_univ, one_smul]
    rfl
  have hn : ∀ᵐ x ∂μ, 0 ≤ x - L := hL.mono fun x hx => sub_nonneg.mpr hx
  have hnonneg : 0 ≤ mean μ - L := he ▸ integral_nonneg_of_ae hn
  by_contra hpos
  have hzero : (∫ x : ℝ, x - L ∂μ) = 0 := by rw [he]; linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hshift).mp hzero
  have hm : mean μ = L := by linarith
  have hvzero : centralMoment id 2 μ = 0 := by
    unfold centralMoment
    change (∫ x : ℝ, (x - mean μ) ^ 2 ∂μ) = 0
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂μ := integral_congr_ae (hae.mono fun x hx => by
        change x - L = 0 at hx
        rw [hm, hx, zero_pow (by decide)])
      _ = 0 := integral_zero _ _
  linarith

private lemma polynomial_minorant (a b y : ℝ) (hy : -a ≤ y) :
    (-a ^ 3 + 2 * a ^ 2 * b - 3 * a * b ^ 2 + 4 * b ^ 3) * y ^ 2 +
      (2 * a ^ 3 * b - 4 * a ^ 2 * b ^ 2 + 6 * a * b ^ 3 - 3 * b ^ 4) * y +
      (-a ^ 3 * b ^ 2 + 2 * a ^ 2 * b ^ 3 - 3 * a * b ^ 4) ≤ y ^ 5 := by
  have hQ : 0 ≤ y ^ 2 + (2 * b - a) * y + 3 * b ^ 2 - 2 * a * b + a ^ 2 := by
    nlinarith only [sq_nonneg (y + b - a / 2), sq_nonneg (b - a / 4), sq_nonneg a]
  have hR := mul_nonneg (mul_nonneg (by linarith : 0 ≤ y + a) (sq_nonneg (y - b))) hQ
  nlinarith only [hR]

private lemma integrated_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (L : ℝ)
    (hL : ∀ᵐ x ∂μ, L ≤ x) (ha : 0 < mean μ - L) :
    let a := mean μ - L
    let b := centralMoment id 2 μ / a
    a * b * (b - a) * (a ^ 2 + b ^ 2) ≤ centralMoment id 5 μ := by
  let a := mean μ - L
  let b := centralMoment id 2 μ / a
  let A := -a ^ 3 + 2 * a ^ 2 * b - 3 * a * b ^ 2 + 4 * b ^ 3
  let B := 2 * a ^ 3 * b - 4 * a ^ 2 * b ^ 2 + 6 * a * b ^ 3 - 3 * b ^ 4
  let C := -a ^ 3 * b ^ 2 + 2 * a ^ 2 * b ^ 3 - 3 * a * b ^ 4
  have h1 : Integrable (fun x : ℝ => x - mean μ) μ := by
    simpa only [pow_one] using integrable_centered_pow μ h (mean μ) 1 (by decide)
  have h2 := integrable_centered_pow μ h (mean μ) 2 (by decide)
  have h5 := integrable_centered_pow μ h (mean μ) 5 (by decide)
  have hfirst : (∫ x : ℝ, x - mean μ ∂μ) = 0 := by
    have hz := centralMoment_one (X := id) (μ := μ)
    change (∫ x : ℝ, (x - mean μ) ^ 1 ∂μ) = 0 at hz
    simpa only [pow_one] using hz
  have hsecond : (∫ x : ℝ, (x - mean μ) ^ 2 ∂μ) = a * b := by
    change centralMoment id 2 μ = a * (centralMoment id 2 μ / a)
    exact (mul_div_cancel₀ (centralMoment id 2 μ) (show a ≠ 0 from ne_of_gt ha)).symm
  have hminor : ∀ᵐ x ∂μ,
      A * (x - mean μ) ^ 2 + B * (x - mean μ) + C ≤ (x - mean μ) ^ 5 := by
    filter_upwards [hL] with x hx
    apply polynomial_minorant a b (x - mean μ)
    change -(mean μ - L) ≤ x - mean μ
    linarith
  have hi := integral_mono_ae (((h2.const_mul A).add (h1.const_mul B)).add
    (integrable_const C)) h5 hminor
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun x : ℝ => A * (x - mean μ) ^ 2 + B * (x - mean μ))
      (g := fun _ => C) ((h2.const_mul A).add (h1.const_mul B)) (integrable_const C),
    integral_add (h2.const_mul A) (h1.const_mul B), integral_const_mul,
    integral_const_mul, hfirst, hsecond, integral_const, probReal_univ, one_smul] at hi
  change a * b * (b - a) * (a ^ 2 + b ^ 2) ≤ centralMoment id 5 μ
  change A * (a * b) + B * 0 + C ≤ centralMoment id 5 μ at hi
  calc
    _ = A * (a * b) + B * 0 + C := by
      change a * b * (b - a) * (a ^ 2 + b ^ 2) =
        (-a ^ 3 + 2 * a ^ 2 * b - 3 * a * b ^ 2 + 4 * b ^ 3) * (a * b) +
          (2 * a ^ 3 * b - 4 * a ^ 2 * b ^ 2 + 6 * a * b ^ 3 - 3 * b ^ 4) * 0 +
          (-a ^ 3 * b ^ 2 + 2 * a ^ 2 * b ^ 3 - 3 * a * b ^ 4)
      ring
    _ ≤ _ := hi

private lemma normalization (a v M : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hM : a * (v / a) * (v / a - a) * (a ^ 2 + (v / a) ^ 2) ≤ M) :
    fifthBound (Real.sqrt v / a) ≤ M / Real.sqrt v ^ 5 := by
  let s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hid : fifthBound (s / a) * s ^ 5 =
      a * (v / a) * (v / a - a) * (a ^ 2 + (v / a) ^ 2) := by
    unfold fifthBound
    rw [← hs2]
    field_simp [ne_of_gt ha, ne_of_gt hs]
    ring
  apply (le_div_iff₀ (pow_pos hs 5)).mpr
  rw [hid]
  exact hM

private lemma lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (L : ℝ) (hL : ∀ᵐ x ∂μ, L ≤ x) :
    fifthBound (Real.sqrt (centralMoment id 2 μ) / (mean μ - L)) ≤
      centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 := by
  have ha := mean_gap_pos μ h hv L hL
  exact normalization _ _ _ ha hv (integrated_bound μ h L hL ha)

private lemma upper_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (U : ℝ) (hU : ∀ᵐ x ∂μ, x ≤ U) :
    centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 ≤
      -fifthBound (Real.sqrt (centralMoment id 2 μ) / (U - mean μ)) := by
  let ν := μ.map (fun x : ℝ => -x)
  have hneg : Measurable (fun x : ℝ => -x) := measurable_neg
  have hn : Integrable (fun x : ℝ => |x| ^ 5) ν := by
    apply (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x| ^ 5) ν)
      hneg.aemeasurable).mpr
    simpa only [Function.comp_def, abs_neg] using h
  have hm : mean ν = -mean μ := by
    exact (ContinuousLinearEquiv.neg ℝ).integral_id_map
  have hc (k : ℕ) : centralMoment id k ν = (-1 : ℝ) ^ k * centralMoment id k μ := by
    unfold centralMoment
    change (∫ x : ℝ, (x - mean ν) ^ k ∂μ.map (fun x : ℝ => -x)) =
      (-1 : ℝ) ^ k * ∫ x : ℝ, (x - mean μ) ^ k ∂μ
    rw [integral_map hneg.aemeasurable (by fun_prop), hm, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [show -x - -mean μ = (-1) * (x - mean μ) by ring, mul_pow]
  have hc2 : centralMoment id 2 ν = centralMoment id 2 μ := by
    rw [hc]; norm_num
  have hc5 : centralMoment id 5 ν = -centralMoment id 5 μ := by
    rw [hc]; norm_num
  have hL : ∀ᵐ x ∂ν, -U ≤ x := by
    apply (ae_map_iff hneg.aemeasurable measurableSet_Ici).mpr
    filter_upwards [hU] with x hx
    exact neg_le_neg hx
  have hb := lower_bound ν hn (hc2.symm ▸ hv) (-U) hL
  rw [hc2, hc5, hm, show -mean μ - -U = U - mean μ by ring, neg_div] at hb
  linarith

/-- Both one-sided Meer–Weeks fifth-moment inequalities. -/
theorem result : claim := by
  intro μ _ h hv
  exact ⟨fun L hL => lower_bound μ h hv L hL, fun U hU => upper_bound μ h hv U hU⟩

end D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
