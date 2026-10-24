/- GID: D5/S3/Analytic/IncompleteBetaShape/Mixture
   generality: I
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Mixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.JacobianOneDim]
   utility: none
   digest: Beta mixture representation of the first parameter coefficient convolution. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Analytic.IncompleteBetaShape.Defs
import D5.S3.Analytic.KummerRatio.BetaIntegral
import D5.S3.Analytic.IncompleteBetaShape.Kernel
import D5.S3.Analytic.IncompleteBeta.Comparison
import Mathlib.MeasureTheory.Function.JacobianOneDim
import D5.S3.Quantum.Measurement.QubitIncompatibilityProbability

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open private w_continuousAt from D5.S3.Analytic.IncompleteBetaShape.Kernel
open private w_nonneg from D5.S3.Analytic.IncompleteBetaShape.Kernel
open private F_nonneg from D5.S3.Analytic.IncompleteBetaShape.Kernel
open D5.S3.Analytic.IncompleteBeta
open D5.S3.Analytic.KummerRatio.BetaIntegral

namespace D5.S3.Analytic.IncompleteBetaShape.Mixture

def convolution (p q b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), coeff p b k * coeff q b (n - k)

/-- The uniform mixture of the beta densities with shapes
`p+k+1` and `q+n-k+1`, for `k` from zero through `n`. -/
def mixtureDensity (p q : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.Gamma (p + q + n + 2) / (n + 1) *
    ∑ k ∈ Finset.range (n + 1),
      y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))

/-- The positive prefactor depends on the two shape parameters only through their sum. -/
def mixtureFactor (c : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  (n + 1) * Real.Gamma (c + n + 2 * b) /
    (Real.Gamma b ^ 2 * Real.Gamma (c + n + 2))

private lemma mixtureDensity_nonneg {p q y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) (hy : y ∈ Ioo 0 1) : 0 ≤ mixtureDensity p q n y := by
  unfold mixtureDensity
  apply mul_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by positivity)).le (by positivity))
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg hy.1.le _)
    (Real.rpow_nonneg (by linarith [hy.2]) _))
      (mul_pos (Real.Gamma_pos_of_pos (by positivity))
        (Real.Gamma_pos_of_pos (by positivity))).le

private lemma weighted_term_eq (p q b : ℝ) (n k : ℕ) (y : ℝ)
    (hy : y ∈ Ioo 0 1) :
    (y * (1 - y)) ^ (b - 1) *
        (y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
          (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))) =
      y ^ (p + b + k - 1) * (1 - y) ^ (q + b + (n - k : ℕ) - 1) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
  rw [Real.mul_rpow hy.1.le (sub_pos.mpr hy.2).le]
  calc
    _ = (y ^ (b - 1) * y ^ (p + k)) *
        ((1 - y) ^ (b - 1) * (1 - y) ^ (q + (n - k : ℕ))) /
          (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hy.1, ← Real.rpow_add (sub_pos.mpr hy.2)]
      congr 3 <;> ring

private lemma weighted_term_integrable {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) (n k : ℕ) :
    IntervalIntegrable (fun y : ℝ => (y * (1 - y)) ^ (b - 1) *
        (y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
          (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)))) volume 0 1 := by
  apply ((intervalIntegrable_beta (by positivity : 0 < p + b + k)
    (by positivity : 0 < q + b + (n - k : ℕ))).div_const
      (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))).congr_uIoo
  intro y hy
  rw [uIoo_of_le zero_le_one] at hy
  exact (weighted_term_eq p q b n k y hy).symm

/-- The coefficient convolution is a beta-mixture mean of the symmetric power weight. -/
theorem convolution_eq_mixtureMean {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) (n : ℕ) :
    convolution p q b n = mixtureFactor (p + q) n b *
      ∫ y in (0 : ℝ)..1, (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y := by
  let F := fun k : ℕ => fun y : ℝ =>
    (y * (1 - y)) ^ (b - 1) *
      (y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)))
  have he (k : ℕ) (y : ℝ) (hy : y ∈ Ioo 0 1) :
      F k y = y ^ (p + b + k - 1) * (1 - y) ^ (q + b + (n - k : ℕ) - 1) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) :=
    weighted_term_eq p q b n k y hy
  have hi (k : ℕ) (_hk : k ∈ Finset.range (n + 1)) :
      IntervalIntegrable (F k) volume 0 1 := weighted_term_integrable hp hq hb n k
  have ht (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Real.Gamma (p + q + n + 2 * b) / Real.Gamma b ^ 2 *
        (∫ y in (0 : ℝ)..1, F k y) = coeff p b k * coeff q b (n - k) := by
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsum : p + b + k + (q + b + (n - k : ℕ)) = p + q + n + 2 * b := by
      rw [Nat.cast_sub hk']
      ring
    have hI : (∫ y in (0 : ℝ)..1, F k y) =
        (Real.Gamma (p + b + k) * Real.Gamma (q + b + (n - k : ℕ)) /
          Real.Gamma (p + q + n + 2 * b)) /
            (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
      calc
        _ = ∫ y in (0 : ℝ)..1,
            (y ^ (p + b + k - 1) * (1 - y) ^ (q + b + (n - k : ℕ) - 1)) /
              (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) :=
          intervalIntegral.integral_congr_Ioo_of_le zero_le_one (fun y hy => he k y hy)
        _ = _ := by
          rw [intervalIntegral.integral_div,
            integral_beta (by positivity : 0 < p + b + k)
              (by positivity : 0 < q + b + (n - k : ℕ)), hsum]
    rw [hI]
    unfold coeff
    have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2 * b)).ne'
    field_simp (disch := assumption)
    <;> ring
  have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2)).ne'
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hrewrite :
      (fun y => (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y) =
      (fun y => (Real.Gamma (p + q + n + 2) / (n + 1)) *
        ∑ k ∈ Finset.range (n + 1), F k y) := by
    funext y
    simp only [mixtureDensity, F, Finset.mul_sum]
    ring
  rw [hrewrite, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hi]
  have hfactor : mixtureFactor (p + q) n b *
      (Real.Gamma (p + q + n + 2) / (n + 1)) =
      Real.Gamma (p + q + n + 2 * b) / Real.Gamma b ^ 2 := by
    unfold mixtureFactor
    field_simp (disch := assumption)
  rw [← mul_assoc, hfactor, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k hk => (ht k hk).symm)

private def affineDomain (y : ℝ) : Set (ℝ × ℝ) :=
  {t | t.1 ∈ Ioo 0 1 ∧ t.2 ∈ Ioo 0 1 ∧ t.2 * t.1 < y ∧ t.2 * (1 - t.1) < 1 - y}

private def rectangleMap (t : ℝ × ℝ) : ℝ × ℝ :=
  (t.2 * t.1, t.2 * (1 - t.1))

private lemma rectangle_change (y : ℝ)
    (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z in Ioo 0 y ×ˢ Ioo 0 (1 - y), f z) =
      ∫⁻ t in affineDomain y, ENNReal.ofReal t.2 * f (rectangleMap t) := by
  let R : Set (ℝ × ℝ) := Ioo 0 y ×ˢ Ioo 0 (1-y)
  have hR : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : R ⊆ D5.S3.Quantum.Measurement.OrderedRootCoordinates.radialBody := by
    intro z hz
    exact ⟨hz.1.1, hz.2.1, by linarith [hz.1.2, hz.2.2]⟩
  have h := D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.triangle_change_lintegral
    (R.indicator f)
  rw [setLIntegral_indicator hR, inter_eq_left.mpr hsub] at h
  have hswap (g : ℝ × ℝ → ℝ≥0∞) :
      (∫⁻ t in D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain, g t) =
      ∫⁻ t in D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain,
        g t.swap := by
    rw [D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain,
      Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (lintegral_prod_swap
      (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := volume.restrict (Ioo (0 : ℝ) 1)) g).symm
  rw [hswap] at h
  have hd : MeasurableSet (affineDomain y) := by
    dsimp only [affineDomain]
    exact (measurable_fst measurableSet_Ioo).inter
      ((measurable_snd measurableSet_Ioo).inter
        ((measurableSet_lt (measurable_snd.mul measurable_fst) measurable_const).inter
          (measurableSet_lt
            (measurable_snd.mul (measurable_const.sub measurable_fst)) measurable_const)))
  have hds : affineDomain y ⊆
      D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain :=
    fun t ht => ⟨ht.1, ht.2.1⟩
  change (∫⁻ z in R, f z) = _
  calc
    _ = ∫⁻ t in D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain,
        ENNReal.ofReal t.2 * R.indicator f (rectangleMap t) := h
    _ = ∫⁻ t in D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.squareDomain,
        (affineDomain y).indicator (fun t => ENNReal.ofReal t.2 * f (rectangleMap t)) t := by
      apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro t ht
      change t.1 ∈ Ioo 0 1 ∧ t.2 ∈ Ioo 0 1 at ht
      dsimp only
      by_cases hr : rectangleMap t ∈ R
      · have htD : t ∈ affineDomain y := ⟨ht.1, ht.2, hr.1.2, hr.2.2⟩
        rw [Set.indicator_of_mem hr, Set.indicator_of_mem htD]
      · have htD : t ∉ affineDomain y := by
          intro hD
          apply hr
          exact ⟨⟨mul_pos ht.2.1 ht.1.1, hD.2.2.1⟩,
            ⟨mul_pos ht.2.1 (sub_pos.mpr ht.1.2), hD.2.2.2⟩⟩
        rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem htD, mul_zero]
    _ = _ := by rw [setLIntegral_indicator hd, inter_eq_left.mpr hds]


private lemma rectangle_beta_sum {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) (y : ℝ) :
    (∫ x in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
      x ^ (p - 1) * z ^ (q - 1) * (y * (1 - x) + (1 - y) * (1 - z)) ^ n) =
      Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 1) *
        ∑ k ∈ Finset.range (n + 1), y ^ k * (1 - y) ^ (n - k) /
          (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
  let C := fun k : ℕ => (n.choose k : ℝ) * y ^ k * (1 - y) ^ (n - k)
  let A := fun k : ℕ => fun x : ℝ => x ^ (p - 1) * (1 - x) ^ k
  let B := fun k : ℕ => fun z : ℝ => z ^ (q - 1) * (1 - z) ^ (n - k)
  have hiA (k : ℕ) : IntervalIntegrable (A k) volume 0 1 := by
    simpa only [A, add_sub_cancel_right, Real.rpow_natCast] using
      intervalIntegrable_beta hp (by positivity : 0 < (k : ℝ) + 1)
  have hiB (k : ℕ) : IntervalIntegrable (B k) volume 0 1 := by
    simpa only [B, add_sub_cancel_right, Real.rpow_natCast] using
      intervalIntegrable_beta hq (by positivity : 0 < ((n - k : ℕ) : ℝ) + 1)
  have hA (k : ℕ) : (∫ x in (0 : ℝ)..1, A k x) =
      Real.Gamma p * Real.Gamma ((k : ℝ) + 1) / Real.Gamma (p + k + 1) := by
    simpa only [A, add_sub_cancel_right, Real.rpow_natCast, ← add_assoc] using
      integral_beta hp (by positivity : 0 < (k : ℝ) + 1)
  have hB (k : ℕ) : (∫ z in (0 : ℝ)..1, B k z) =
      Real.Gamma q * Real.Gamma ((n - k : ℕ) + 1) /
        Real.Gamma (q + (n - k : ℕ) + 1) := by
    simpa only [B, add_sub_cancel_right, Real.rpow_natCast, ← add_assoc] using
      integral_beta hq (by positivity : 0 < ((n - k : ℕ) : ℝ) + 1)
  have hpoly (x z : ℝ) :
      x ^ (p - 1) * z ^ (q - 1) * (y * (1 - x) + (1 - y) * (1 - z)) ^ n =
      ∑ k ∈ Finset.range (n + 1), C k * A k x * B k z := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [C, A, B, mul_pow]
    ring
  have hinner (x : ℝ) :
      (∫ z in (0 : ℝ)..1,
        x ^ (p - 1) * z ^ (q - 1) * (y * (1 - x) + (1 - y) * (1 - z)) ^ n) =
      ∑ k ∈ Finset.range (n + 1), C k * A k x *
        (Real.Gamma q * Real.Gamma ((n - k : ℕ) + 1) /
          Real.Gamma (q + (n - k : ℕ) + 1)) := by
    simp_rw [hpoly]
    rw [intervalIntegral.integral_finsetSum (fun k _ => (hiB k).const_mul (C k * A k x))]
    simp_rw [intervalIntegral.integral_const_mul, hB]
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => ((hiA k).const_mul (C k)).mul_const _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hA]
  dsimp only [C]
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  have hfac : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  field_simp
  linear_combination (y ^ k * (1 - y) ^ (n - k)) * hfac




private lemma rectangle_real {p q y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hy : y ∈ Ioo 0 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..y, ∫ z in (0 : ℝ)..(1 - y),
      x ^ (p - 1) * z ^ (q - 1) * (1 - x - z) ^ n) =
    (Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
      Real.Gamma (p + q + n + 2)) * mixtureDensity p q n y := by
  have hz : 0 < 1 - y := sub_pos.mpr hy.2
  let G := fun x z : ℝ => x ^ (p - 1) * z ^ (q - 1) * (1 - x - z) ^ n
  have hscale :
      (∫ x in (0 : ℝ)..y, ∫ z in (0 : ℝ)..(1 - y), G x z) =
      y ^ p * (1 - y) ^ q *
        ∫ u in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          u ^ (p - 1) * r ^ (q - 1) * (y * (1 - u) + (1 - y) * (1 - r)) ^ n := by
    have hout := intervalIntegral.smul_integral_comp_mul_left
      (fun x => ∫ z in (0 : ℝ)..(1 - y), G x z) y (a := 0) (b := 1)
    simp only [smul_eq_mul, mul_zero, mul_one] at hout
    rw [← hout]
    have hin (u : ℝ) := intervalIntegral.smul_integral_comp_mul_left
      (G (y * u)) (1 - y) (a := 0) (b := 1)
    simp only [smul_eq_mul, mul_zero, mul_one] at hin
    simp_rw [← hin]
    rw [intervalIntegral.integral_const_mul]
    have hG :
        (∫ u in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, G (y * u) ((1 - y) * r)) =
        y ^ (p - 1) * (1 - y) ^ (q - 1) *
          ∫ u in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
            u ^ (p - 1) * r ^ (q - 1) *
              (y * (1 - u) + (1 - y) * (1 - r)) ^ n := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro u hu
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro r hr
      dsimp only [G]
      rw [Real.mul_rpow hy.1.le hu.1.le, Real.mul_rpow hz.le hr.1.le,
        show 1 - y * u - (1 - y) * r = y * (1 - u) + (1 - y) * (1 - r) by ring]
      ring
    rw [hG, show p = 1 + (p - 1) by ring, Real.rpow_add hy.1,
      show q = 1 + (q - 1) by ring, Real.rpow_add hz, Real.rpow_one, Real.rpow_one]
    ring
  change (∫ x in (0 : ℝ)..y, ∫ z in (0 : ℝ)..(1 - y), G x z) = _
  rw [hscale, rectangle_beta_sum hp hq]
  have hpowers : y ^ p * (1 - y) ^ q *
      (∑ k ∈ Finset.range (n + 1), y ^ k * (1 - y) ^ (n - k) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1))) =
      ∑ k ∈ Finset.range (n + 1), y ^ (p + k) * (1 - y) ^ (q + (n - k : ℕ)) /
        (Real.Gamma (p + k + 1) * Real.Gamma (q + (n - k : ℕ) + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.rpow_add hy.1, Real.rpow_add hz, Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [mul_left_comm (y ^ p * (1 - y) ^ q)
    (Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 1)), hpowers]
  have hG := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2)).ne'
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold mixtureDensity
  rw [show (n : ℝ) + 2 = ((n : ℝ) + 1) + 1 by ring, Real.Gamma_add_one hn]
  field_simp


private lemma rectangle_kernel_integrable {p q y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hy : y ∈ Ioo 0 1) (n : ℕ) :
    IntegrableOn (fun z : ℝ × ℝ => z.1 ^ (p - 1) * z.2 ^ (q - 1) * (1 - z.1 - z.2) ^ n)
      (Ioo 0 y ×ˢ Ioo 0 (1 - y)) (volume.prod volume) := by
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (p - 1)) (Ioo 0 y) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hy.1.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hi2 : IntegrableOn (fun x : ℝ => x ^ (q - 1)) (Ioo 0 (1 - y)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [hy.2])).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hi := hi1.mul_prod hi2
  rw [Measure.prod_restrict] at hi
  apply hi.mul_bdd (c := 1) (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hz.1.2, hz.2.2]) n)]
  exact pow_le_one₀ (by linarith [hz.1.2, hz.2.2]) (by linarith [hz.1.1, hz.2.1])

private lemma rectangle_lintegral {p q y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hy : y ∈ Ioo 0 1) (n : ℕ) :
    (∫⁻ z in Ioo 0 y ×ˢ Ioo 0 (1 - y),
      ENNReal.ofReal (z.1 ^ (p - 1) * z.2 ^ (q - 1) * (1 - z.1 - z.2) ^ n)) =
    ENNReal.ofReal ((Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
      Real.Gamma (p + q + n + 2)) * mixtureDensity p q n y) := by
  rw [Measure.volume_eq_prod]
  have hi := rectangle_kernel_integrable hp hq hy n
  have hn : 0 ≤ᵐ[(volume.prod volume).restrict (Ioo 0 y ×ˢ Ioo 0 (1 - y))]
      (fun z : ℝ × ℝ => z.1 ^ (p - 1) * z.2 ^ (q - 1) * (1 - z.1 - z.2) ^ n) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hz.1.1.le _) (Real.rpow_nonneg hz.2.1.le _))
      (pow_nonneg (by linarith [hz.1.2, hz.2.2]) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, setIntegral_prod _ hi]
  congr 1
  rw [← rectangle_real hp hq hy n]
  simp_rw [intervalIntegral.integral_of_le hy.1.le,
    intervalIntegral.integral_of_le (by linarith [hy.2] : 0 ≤ 1 - y), integral_Ioc_eq_integral_Ioo]

private lemma affine_density_integral {p q y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hy : y ∈ Ioo 0 1) (n : ℕ) :
    (∫⁻ t in affineDomain y,
      ENNReal.ofReal (t.1 ^ (p - 1) * (1 - t.1) ^ (q - 1) *
        t.2 ^ (p + q - 1) * (1 - t.2) ^ n)) =
    ENNReal.ofReal ((Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
      Real.Gamma (p + q + n + 2)) * mixtureDensity p q n y) := by
  rw [← rectangle_lintegral hp hq hy n, rectangle_change y]
  symm
  apply setLIntegral_congr_fun (show MeasurableSet (affineDomain y) by
    dsimp only [affineDomain]; measurability)
  intro t ht
  dsimp only
  rw [← ENNReal.ofReal_mul ht.2.1.1.le]
  congr 1
  dsimp only [rectangleMap]
  rw [Real.mul_rpow ht.2.1.1.le ht.1.1.le,
    Real.mul_rpow ht.2.1.1.le (sub_pos.mpr ht.1.2).le,
    show 1 - t.2 * t.1 - t.2 * (1 - t.1) = 1 - t.2 by ring,
    show p + q - 1 = 1 + (p - 1) + (q - 1) by ring,
    Real.rpow_add ht.2.1.1, Real.rpow_add ht.2.1.1, Real.rpow_one]
  ring


private lemma window_lintegral {v s : ℝ} (hs : s ∈ Ioo 0 1)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ioo (s * v) (1 - s + s * v), g y) =
      ENNReal.ofReal (1 - s) * ∫⁻ u in Ioo (0 : ℝ) 1, g (s * v + (1 - s) * u) := by
  have hpos : 0 < 1 - s := sub_pos.mpr hs.2
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := fun u : ℝ => (1 - s) * u + s * v) (f' := fun _ => 1 - s)
    measurableSet_Ioo
    (fun u _ => by
      apply HasDerivAt.hasDerivWithinAt
      convert! (((hasDerivAt_id u).const_mul (1 - s)).add_const (s * v)) using 1 <;> simp)
    (show InjOn (fun u : ℝ => (1 - s) * u + s * v) (Ioo 0 1) by
      intro x _ y _ he
      exact mul_left_cancel₀ hpos.ne' (add_right_cancel he)) g
  rw [image_affine_Ioo hpos, mul_zero, zero_add, mul_one] at h
  simp only [abs_of_pos hpos] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  simpa only [add_comm] using h

private lemma affine_lintegral {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (n : ℕ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (v ^ (p - 1) * (1 - v) ^ (q - 1) *
        s ^ (p + q - 1) * (1 - s) ^ n) * ENNReal.ofReal (1 - s) *
          ∫⁻ u in Ioo (0 : ℝ) 1, g (s * v + (1 - s) * u)) =
    ENNReal.ofReal (Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
      Real.Gamma (p + q + n + 2)) *
      ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (mixtureDensity p q n y) * g y := by
  let U : Set ℝ := Ioo 0 1
  let A := fun t : ℝ × ℝ => t.1 ^ (p - 1) * (1 - t.1) ^ (q - 1) *
    t.2 ^ (p + q - 1) * (1 - t.2) ^ n
  let K := fun (t : ℝ × ℝ) (y : ℝ) =>
    ENNReal.ofReal (A t) * (Ioo (t.2 * t.1) (1 - t.2 + t.2 * t.1)).indicator g y
  have hA : Measurable (fun t => ENNReal.ofReal (A t)) := by dsimp [A]; fun_prop
  have hK : Measurable (Function.uncurry K) := by
    dsimp only [K, Set.indicator, Function.uncurry]
    apply (hA.comp measurable_fst).mul
    exact Measurable.ite (by measurability) (hg.comp measurable_snd) measurable_const
  have hpoint (t : ℝ × ℝ) :
      (∫⁻ y, K t y) = ENNReal.ofReal (A t) *
        ∫⁻ y in Ioo (t.2 * t.1) (1 - t.2 + t.2 * t.1), g y := by
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfirst :
      (∫⁻ v in U, ∫⁻ s in U, ENNReal.ofReal (A (v, s)) * ENNReal.ofReal (1 - s) *
        ∫⁻ u in U, g (s * v + (1 - s) * u)) =
        ∫⁻ t in U ×ˢ U, ∫⁻ y, K t y := by
    have hm : Measurable (fun t => ∫⁻ y, K t y) := hK.lintegral_prod_right'
    rw [Measure.volume_eq_prod, setLIntegral_prod (fun t => ∫⁻ y, K t y) hm.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    dsimp only
    rw [hpoint, window_lintegral hs, mul_assoc]
  have hswap : (∫⁻ t in U ×ˢ U, ∫⁻ y, K t y) =
      ∫⁻ y, ∫⁻ t in U ×ˢ U, K t y :=
    lintegral_lintegral_swap hK.aemeasurable
  have hfiber (y : ℝ) : (∫⁻ t in U ×ˢ U, K t y) =
      g y * ∫⁻ t in affineDomain y, ENNReal.ofReal (A t) := by
    let V : Set (ℝ × ℝ) := {t | y ∈ Ioo (t.2 * t.1) (1 - t.2 + t.2 * t.1)}
    have hV : MeasurableSet V := by dsimp [V]; measurability
    have he : V ∩ (U ×ˢ U) = affineDomain y := by
      ext t
      simp only [V, affineDomain, U, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨h3, h4, h1, by nlinarith⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h3, by nlinarith⟩, h1, h2⟩
    have heq : (fun t => K t y) = V.indicator (fun t => g y * ENNReal.ofReal (A t)) := by
      funext t
      by_cases h : y ∈ Ioo (t.2 * t.1) (1 - t.2 + t.2 * t.1)
      · have ht : t ∈ V := h
        simp only [K, Set.indicator_of_mem h, Set.indicator_of_mem ht]
        exact mul_comm _ _
      · have ht : t ∉ V := h
        simp only [K, Set.indicator_of_notMem h, Set.indicator_of_notMem ht, mul_zero]
    rw [heq, setLIntegral_indicator hV, he,
      lintegral_const_mul _ hA]
  have hdensity (y : ℝ) : (∫⁻ t in affineDomain y, ENNReal.ofReal (A t)) =
      U.indicator (fun y => ENNReal.ofReal ((Real.Gamma p * Real.Gamma q *
        Real.Gamma ((n : ℝ) + 2) / Real.Gamma (p + q + n + 2)) * mixtureDensity p q n y)) y := by
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      exact affine_density_integral hp hq hy n
    · rw [Set.indicator_of_notMem hy]
      have hempty : affineDomain y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        apply hy
        have hx := mul_pos ht.2.1.1 ht.1.1
        have hz := mul_pos ht.2.1.1 (sub_pos.mpr ht.1.2)
        exact ⟨lt_trans hx ht.2.2.1, by nlinarith [ht.2.2.2]⟩
      rw [hempty, setLIntegral_empty]
  change (∫⁻ v in U, ∫⁻ s in U, ENNReal.ofReal (A (v, s)) * ENNReal.ofReal (1 - s) *
    ∫⁻ u in U, g (s * v + (1 - s) * u)) = _
  rw [hfirst, hswap]
  simp_rw [hfiber, hdensity]
  have hconst : 0 ≤ Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
      Real.Gamma (p + q + n + 2) := by
    exact (div_pos (mul_pos (mul_pos (Real.Gamma_pos_of_pos hp) (Real.Gamma_pos_of_pos hq))
      (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity))).le
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ Ioo (0 : ℝ) 1
  · simp only [U, Set.indicator_of_mem hy, ENNReal.ofReal_mul hconst]
    ring
  · simp only [U, Set.indicator_of_notMem hy, mul_zero]


/-- The uniform shifted-beta mixture has the affine beta-mixture law. -/
theorem mixture_eq_affine {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (n : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : IntervalIntegrable (fun y => mixtureDensity p q n y * g y) volume 0 1) :
    (∫ y in (0 : ℝ)..1, mixtureDensity p q n y * g y) =
      (Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
        Real.Gamma (p + q + n + 2))⁻¹ *
        ∫ v in (0 : ℝ)..1, v ^ (p - 1) * (1 - v) ^ (q - 1) *
          ∫ s in (0 : ℝ)..1, s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
            ∫ u in (0 : ℝ)..1, g (s * v + (1 - s) * u) := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 1)
  let ν : Measure (ℝ × ℝ × ℝ) := μ.prod (μ.prod μ)
  let A := fun (v s : ℝ) => v ^ (p - 1) * (1 - v) ^ (q - 1) *
    s ^ (p + q - 1) * (1 - s) ^ n
  let W := fun t : ℝ × ℝ × ℝ => ENNReal.ofReal (A t.1 t.2.1) * ENNReal.ofReal (1 - t.2.1)
  let X := fun t : ℝ × ℝ × ℝ => t.2.1 * t.1 + (1 - t.2.1) * t.2.2
  let C := Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
    Real.Gamma (p + q + n + 2)
  let ρ := mixtureDensity p q n
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (mul_pos (Real.Gamma_pos_of_pos hp) (Real.Gamma_pos_of_pos hq))
      (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity))
  have hW : Measurable W := by dsimp [W, A]; fun_prop
  have hWfin (t) : W t < ∞ := by dsimp [W]; finiteness
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hρ : Measurable (fun y => ENNReal.ofReal (ρ y)) := by
    dsimp [ρ, mixtureDensity]; fun_prop
  have hρnn (y : ℝ) (hy : y ∈ Ioo 0 1) : 0 ≤ ρ y :=
    mixtureDensity_nonneg hp hq n hy
  have hmeasure : Measure.map X (ν.withDensity W) =
      ENNReal.ofReal C • μ.withDensity (fun y => ENNReal.ofReal (ρ y)) := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_map hf hX]
    change (∫⁻ t, (f ∘ X) t ∂ν.withDensity W) = _
    rw [lintegral_withDensity_eq_lintegral_mul ν hW (hf.comp hX), lintegral_smul_measure,
      lintegral_withDensity_eq_lintegral_mul μ hρ hf]
    change (∫⁻ t, W t * f (X t) ∂ν) = _
    calc
      _ = ∫⁻ v, (∫⁻ s, ENNReal.ofReal (A v s) * ENNReal.ofReal (1 - s) *
          (∫⁻ u, f (s * v + (1 - s) * u) ∂μ) ∂μ) ∂μ := by
        rw [lintegral_prod _ (by dsimp [W, A, X]; fun_prop)]
        apply lintegral_congr
        intro v
        rw [lintegral_prod _ (by dsimp [W, A, X]; fun_prop)]
        apply lintegral_congr
        intro s
        change (∫⁻ u, (ENNReal.ofReal (A v s) * ENNReal.ofReal (1 - s)) *
          f (s * v + (1 - s) * u) ∂μ) = _
        exact lintegral_const_mul' _ _ (by finiteness)
      _ = _ := affine_lintegral hp hq n f hf
  have hμ : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hiμ : Integrable (fun y => ρ y * g y) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi
  have hitarget : Integrable g (μ.withDensity (fun y => ENNReal.ofReal (ρ y))) := by
    apply (integrable_withDensity_iff_integrable_smul' hρ (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    apply hiμ.congr
    filter_upwards [hμ] with y hy
    rw [ENNReal.toReal_ofReal (hρnn y hy), smul_eq_mul]
  have himap : Integrable g (Measure.map X (ν.withDensity W)) := by
    rw [hmeasure]
    exact hitarget.smul_measure ENNReal.ofReal_ne_top
  have hiwith := (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mp himap
  have hiT := (integrable_withDensity_iff_integrable_smul' hW
    (Filter.Eventually.of_forall hWfin)).mp hiwith
  change Integrable (fun t => (W t).toReal * g (X t)) ν at hiT
  have hsource : (∫ t, (W t).toReal * g (X t) ∂ν) = C * ∫ y, ρ y * g y ∂μ := by
    calc
      _ = ∫ t, g (X t) ∂ν.withDensity W :=
        (integral_withDensity_eq_integral_toReal_smul hW
          (Filter.Eventually.of_forall hWfin) (fun t => g (X t))).symm
      _ = ∫ y, g y ∂Measure.map X (ν.withDensity W) :=
        (integral_map hX.aemeasurable hg.aestronglyMeasurable).symm
      _ = _ := by
        rw [hmeasure, integral_smul_measure, ENNReal.toReal_ofReal hC.le,
          integral_withDensity_eq_integral_toReal_smul hρ
            (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
        congr 1
        apply integral_congr_ae
        filter_upwards [hμ] with y hy
        rw [ENNReal.toReal_ofReal (hρnn y hy), smul_eq_mul]
  have htrip : (∫ t, (W t).toReal * g (X t) ∂ν) =
      ∫ v, (∫ s, (∫ u, (W (v, s, u)).toReal * g (X (v, s, u)) ∂μ) ∂μ) ∂μ := by
    rw [integral_prod _ hiT]
    apply integral_congr_ae
    filter_upwards [hiT.prod_right_ae] with v hv
    exact integral_prod _ hv
  have hpoint (v s : ℝ) (hv : v ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) :
      (∫ u, (W (v, s, u)).toReal * g (X (v, s, u)) ∂μ) =
      v ^ (p - 1) * (1 - v) ^ (q - 1) *
        (s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
          ∫ u, g (s * v + (1 - s) * u) ∂μ) := by
    have hA : 0 ≤ A v s := by
      dsimp [A]
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hv.1.le _) (Real.rpow_nonneg (by linarith [hv.2]) _))
        (Real.rpow_nonneg hs.1.le _)) (pow_nonneg (by linarith [hs.2]) _)
    simp only [W, X, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
      ENNReal.toReal_ofReal (show 0 ≤ 1 - s by linarith [hs.2]), integral_const_mul]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ]
    dsimp only [A]
    ring
  have hweighted : (∫ v, (∫ s, (∫ u, (W (v, s, u)).toReal * g (X (v, s, u)) ∂μ) ∂μ) ∂μ) =
      ∫ v in (0 : ℝ)..1, v ^ (p - 1) * (1 - v) ^ (q - 1) *
        ∫ s in (0 : ℝ)..1, s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
          ∫ u in (0 : ℝ)..1, g (s * v + (1 - s) * u) := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [hμ] with v hv
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hμ] with s hs
    exact hpoint v s hv hs
  rw [← hweighted, ← htrip, hsource]
  change (∫ y in (0 : ℝ)..1, ρ y * g y) = C⁻¹ * (C * ∫ y, ρ y * g y ∂μ)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  field_simp
  rfl


private lemma mixture_weight_integrable {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) (n : ℕ) :
    IntervalIntegrable (fun y => mixtureDensity p q n y * (y * (1 - y)) ^ (b - 1))
      volume 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 1)
  let B := fun v : ℝ => v ^ (p - 1) * (1 - v) ^ (q - 1)
  let D := Real.Gamma (p + q) * Real.Gamma ((n : ℝ) + 2) /
    Real.Gamma (p + q + n + 2)
  let C := Real.Gamma p * Real.Gamma q * Real.Gamma ((n : ℝ) + 2) /
    Real.Gamma (p + q + n + 2)
  have hμ : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hD : 0 < D := by
    dsimp [D]
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos (add_pos hp hq))
      (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity))
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (mul_pos (Real.Gamma_pos_of_pos hp) (Real.Gamma_pos_of_pos hq))
      (Real.Gamma_pos_of_pos (by positivity))) (Real.Gamma_pos_of_pos (by positivity))
  have hw (y : ℝ) (hy : y ∈ Icc 0 1) : 0 ≤ Kernel.w b y := w_nonneg b hy
  have hF (v : ℝ) (hv : v ∈ Ioo 0 1) (s : ℝ) (hs : s ∈ Ioo 0 1) :
      0 ≤ Kernel.F b s v := F_nonneg ⟨hs.1.le, hs.2.le⟩ ⟨hv.1.le, hv.2.le⟩
  have hinner (v : ℝ) (hv : v ∈ Ioo 0 1) (s : ℝ) (hs : s ∈ Ioo 0 1) :
      (∫⁻ u, ENNReal.ofReal (Kernel.w b (s * v + (1 - s) * u)) ∂μ) =
        ENNReal.ofReal (Kernel.F b s v) := by
    have hi : IntervalIntegrable (fun u => Kernel.w b (s * v + (1 - s) * u))
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable _
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      have hxu : s * v + (1 - s) * u ∈ Ioo (0 : ℝ) 1 := by
        constructor
        · exact add_pos_of_pos_of_nonneg (mul_pos hs.1 hv.1)
            (mul_nonneg (sub_nonneg.mpr hs.2.le) hu.1)
        · nlinarith [mul_pos hs.1 (sub_pos.mpr hv.2),
            mul_nonneg (sub_nonneg.mpr hs.2.le) (sub_nonneg.mpr hu.2)]
      exact (w_continuousAt b hxu).comp_continuousWithinAt
        (f := fun u : ℝ => s * v + (1 - s) * u)
        (by fun_prop : ContinuousWithinAt (fun u : ℝ => s * v + (1 - s) * u)
          (uIcc (0 : ℝ) 1) u)
    have hin := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi
    have he := ofReal_integral_eq_lintegral_ofReal hin (by
      filter_upwards [hμ] with u hu
      apply hw
      constructor
      · exact add_nonneg (mul_nonneg hs.1.le hv.1.le)
          (mul_nonneg (sub_nonneg.mpr hs.2.le) hu.1.le)
      · nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hv.2.le),
          mul_nonneg (sub_nonneg.mpr hs.2.le) (sub_nonneg.mpr hu.2.le)])
    simpa only [Kernel.F, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, μ] using he.symm
  have hB (v : ℝ) (hv : v ∈ Ioo 0 1) : 0 ≤ B v :=
    mul_nonneg (Real.rpow_nonneg hv.1.le _) (Real.rpow_nonneg (by linarith [hv.2]) _)
  have hweighted (v : ℝ) (hv : v ∈ Ioo 0 1) :
      (∫⁻ s, ENNReal.ofReal (B v * s ^ (p + q - 1) * (1 - s) ^ n) *
          ENNReal.ofReal (1 - s) *
            ∫⁻ u, ENNReal.ofReal (Kernel.w b (s * v + (1 - s) * u)) ∂μ ∂μ) =
        ENNReal.ofReal D * ENNReal.ofReal (B v * Kernel.H (p + q) n b v) := by
    have hsi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (Kernel.H_integrand_intervalIntegrable (add_pos hp hq) hb n ⟨hv.1.le, hv.2.le⟩)
    have he := ofReal_integral_eq_lintegral_ofReal hsi (by
      filter_upwards [hμ] with s hs
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _)
        (Real.rpow_nonneg (by linarith [hs.2]) _)) (hF v hv s hs))
    have hnorm : (∫ s, s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
        Kernel.F b s v ∂μ) = D * Kernel.H (p + q) n b v := by
      unfold Kernel.H
      change _ = D * (D⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have hBv : 0 ≤ B v := hB v hv
    calc
      _ = ENNReal.ofReal (B v) *
          ∫⁻ s, ENNReal.ofReal (s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
            Kernel.F b s v) ∂μ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [hμ] with s hs
        rw [hinner v hv s hs, Real.rpow_add_one (sub_pos.mpr hs.2).ne', Real.rpow_natCast]
        have hA : 0 ≤ B v * s ^ (p + q - 1) * (1 - s) ^ n :=
          mul_nonneg (mul_nonneg hBv (Real.rpow_nonneg hs.1.le _))
            (pow_nonneg (sub_pos.mpr hs.2).le _)
        rw [← ENNReal.ofReal_mul hBv, ← ENNReal.ofReal_mul hA,
          ← ENNReal.ofReal_mul (mul_nonneg hA (sub_pos.mpr hs.2).le)]
        congr 1
        ring
      _ = _ := by
        rw [← he, hnorm, ENNReal.ofReal_mul hD.le,
          ENNReal.ofReal_mul (hB v hv)]
        ring
  rcases Kernel.H_bounded (add_pos hp hq) hb n with ⟨M, hM⟩
  have hiB : Integrable B μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (intervalIntegrable_beta hp hq)
  have hiBH : Integrable (fun v => B v * Kernel.H (p + q) n b v) μ :=
    hiB.mul_bdd (((Kernel.H_continuousOn (add_pos hp hq) hb n).mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
      (by filter_upwards [hμ] with v hv; exact hM v ⟨hv.1.le, hv.2.le⟩)
  have hfinite : (∫⁻ v, ENNReal.ofReal (B v * Kernel.H (p + q) n b v) ∂μ) < ∞ :=
    lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hiBH.hasFiniteIntegral
  have hlaw := affine_lintegral hp hq n (fun y => ENNReal.ofReal (Kernel.w b y))
    (by unfold Kernel.w; fun_prop)
  change (∫⁻ v, (∫⁻ s, ENNReal.ofReal (B v * s ^ (p + q - 1) * (1 - s) ^ n) *
      ENNReal.ofReal (1 - s) *
        (∫⁻ u, ENNReal.ofReal (Kernel.w b (s * v + (1 - s) * u)) ∂μ) ∂μ) ∂μ) =
    ENNReal.ofReal C * (∫⁻ y, ENNReal.ofReal (mixtureDensity p q n y) *
      ENNReal.ofReal (Kernel.w b y) ∂μ) at hlaw
  have hleft : (∫⁻ v, (∫⁻ s, ENNReal.ofReal (B v * s ^ (p + q - 1) * (1 - s) ^ n) *
      ENNReal.ofReal (1 - s) *
        (∫⁻ u, ENNReal.ofReal (Kernel.w b (s * v + (1 - s) * u)) ∂μ) ∂μ) ∂μ) < ∞ := by
    have he : (∫⁻ v, (∫⁻ s, ENNReal.ofReal (B v * s ^ (p + q - 1) * (1 - s) ^ n) *
        ENNReal.ofReal (1 - s) *
          (∫⁻ u, ENNReal.ofReal (Kernel.w b (s * v + (1 - s) * u)) ∂μ) ∂μ) ∂μ) =
        ENNReal.ofReal D * ∫⁻ v, ENNReal.ofReal (B v * Kernel.H (p + q) n b v) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [hμ] with v hv
      exact hweighted v hv
    rw [he]
    finiteness
  have htarget : (∫⁻ y, ENNReal.ofReal (mixtureDensity p q n y) *
      ENNReal.ofReal (Kernel.w b y) ∂μ) < ∞ := by
    rw [hlaw] at hleft
    by_contra h
    have ht : (∫⁻ y, ENNReal.ofReal (mixtureDensity p q n y) *
        ENNReal.ofReal (Kernel.w b y) ∂μ) = ∞ := eq_top_iff.mpr (not_lt.mp h)
    simpa [ht, ENNReal.ofReal_eq_zero, hC.not_ge] using hleft
  have hρ (y : ℝ) (hy : y ∈ Ioo 0 1) : 0 ≤ mixtureDensity p q n y :=
    mixtureDensity_nonneg hp hq n hy
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine ⟨(by dsimp [mixtureDensity]; fun_prop), ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (by
    filter_upwards [hμ] with y hy
    exact mul_nonneg (hρ y hy) (hw y ⟨hy.1.le, hy.2.le⟩))).mpr
  convert htarget using 1
  apply lintegral_congr_ae
  filter_upwards [hμ] with y hy
  exact ENNReal.ofReal_mul (hρ y hy)

/-- The first-parameter convolution is the beta mean of the averaged sliding kernel. -/
theorem convolution_eq_betaMean_H {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) (n : ℕ) :
    convolution p q b n = mixtureFactor (p + q) n b *
      D5.S3.Analytic.IncompleteBeta.Comparison.betaMean (Kernel.H (p + q) n b)
        ((p + q) / 2) ((p - q) / 2) := by
  rw [convolution_eq_mixtureMean hp hq hb]
  congr 1
  have hweight : (∫ y in (0 : ℝ)..1,
      (y * (1 - y)) ^ (b - 1) * mixtureDensity p q n y) =
      ∫ y in (0 : ℝ)..1, mixtureDensity p q n y * Kernel.w b y := by
    unfold Kernel.w
    apply intervalIntegral.integral_congr
    intro y _
    exact mul_comm _ _
  rw [hweight, mixture_eq_affine hp hq n (Kernel.w b)
    (by unfold Kernel.w; fun_prop) (mixture_weight_integrable hp hq hb n)]
  unfold D5.S3.Analytic.IncompleteBeta.Comparison.betaMean
  rw [show (p + q) / 2 + (p - q) / 2 = p by ring,
    show (p + q) / 2 - (p - q) / 2 = q by ring,
    show 2 * ((p + q) / 2) = p + q by ring]
  let J := ∫ v in (0 : ℝ)..1, v ^ (p - 1) * (1 - v) ^ (q - 1) *
    ∫ s in (0 : ℝ)..1, s ^ (p + q - 1) * (1 - s) ^ ((n : ℝ) + 1) *
      ∫ u in (0 : ℝ)..1, Kernel.w b (s * v + (1 - s) * u)
  have hH : (∫ v in (0 : ℝ)..1,
      v ^ (p - 1) * (1 - v) ^ (q - 1) * Kernel.H (p + q) n b v) =
      (Real.Gamma (p + q) * Real.Gamma ((n : ℝ) + 2) /
        Real.Gamma (p + q + n + 2))⁻¹ * J := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    unfold Kernel.H Kernel.F
    ring
  rw [hH]
  change _ * J = _ * (_ * J)
  have hGp := (Real.Gamma_pos_of_pos hp).ne'
  have hGq := (Real.Gamma_pos_of_pos hq).ne'
  have hGc := (Real.Gamma_pos_of_pos (add_pos hp hq)).ne'
  have hGn := (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 2)).ne'
  have hGcn := (Real.Gamma_pos_of_pos (by positivity : 0 < p + q + n + 2)).ne'
  field_simp

end D5.S3.Analytic.IncompleteBetaShape.Mixture
