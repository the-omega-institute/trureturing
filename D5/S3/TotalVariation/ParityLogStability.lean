/- GID: D5/S3/TotalVariation/ParityLogStability
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityLogStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive sign-moment floor gives a sharp total-variation bound for log recovery. -/

import D5.S3.TotalVariation.Pinsker
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Sharp stability of the logarithmic parity coefficients of a finite binary law. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.ParityLogStability

open D5.S3.TotalVariation.Pinsker (totalVariation)

private theorem log_step {e x y : ℝ} (he : 0 < e) (hx : e ≤ x) (hxy : x ≤ y) :
    Real.log y - Real.log x ≤ (y - x) / e := by
  have hx₀ := he.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  calc
    Real.log y - Real.log x = Real.log (y / x) := (Real.log_div hy₀.ne' hx₀.ne').symm
    _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy₀ hx₀)
    _ = (y - x) / x := by rw [sub_div, div_self hx₀.ne']
    _ ≤ (y - x) / e := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) he hx

private theorem log_abs_slope {e x y : ℝ} (he : 0 < e) (hx : e ≤ |x|) (hy : e ≤ |y|) :
    ∃ slope : ℝ, |slope| ≤ 1 / e ∧
      Real.log |x| - Real.log |y| = slope * (x - y) := by
  have habs : |Real.log (|x|) - Real.log (|y|)| ≤ |x - y| / e := by
    have hposx := he.trans_le hx
    have hposy := he.trans_le hy
    rcases le_total (|x|) (|y|) with h | h
    · have hlog := Real.strictMonoOn_log.monotoneOn hposx hposy h
      rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub]
      apply (log_step he hx h).trans
      exact div_le_div_of_nonneg_right (by
        simpa [abs_of_nonpos (sub_nonpos.mpr h), neg_sub] using abs_abs_sub_abs_le_abs_sub x y) he.le
    · have hlog := Real.strictMonoOn_log.monotoneOn hposy hposx h
      rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
      apply (log_step he hy h).trans
      exact div_le_div_of_nonneg_right (by
        simpa [abs_of_nonneg (sub_nonneg.mpr h)] using
          abs_abs_sub_abs_le_abs_sub x y) he.le
  by_cases h : x = y
  · subst y
    exact ⟨0, by rw [abs_zero]; positivity, by simp⟩
  · have hsub : x - y ≠ 0 := sub_ne_zero.mpr h
    refine ⟨(Real.log |x| - Real.log |y|) / (x - y), ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr hsub)]
      simpa [div_eq_mul_inv, mul_comm] using habs
    · exact (div_mul_cancel₀ _ hsub).symm

theorem abs_expectation_le_oscillation {A : Type*} [Fintype A] [Nonempty A]
    (p q k : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x)
    (bound : ℝ) (hbound : ∀ x y, |k x - k y| ≤ bound) :
    |∑ x, (p x - q x) * k x| ≤ bound * totalVariation p q := by
  classical
  obtain ⟨hi, _, hmax⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
  obtain ⟨lo, _, hmin⟩ := Finset.exists_min_image Finset.univ k Finset.univ_nonempty
  let mid := (k hi + k lo) / 2
  have hrange : k hi - k lo ≤ bound := le_trans (le_abs_self _) (hbound hi lo)
  have hpoint (x : A) : |k x - mid| ≤ bound / 2 := by
    have hu := hmax x (Finset.mem_univ x)
    have hl := hmin x (Finset.mem_univ x)
    apply abs_le.mpr
    dsimp [mid]
    constructor <;> linarith
  have hshift : (∑ x, (p x - q x) * k x) = ∑ x, (p x - q x) * (k x - mid) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib _ (f := p),
      hmass, sub_self, zero_mul, sub_zero]
  rw [hshift]
  calc
    _ ≤ ∑ x, |(p x - q x) * (k x - mid)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |p x - q x| * (bound / 2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpoint x) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold totalVariation; ring

variable {A : Type*} [AddCommGroup A]

def sign (ψ : AddChar A ℂ) (x : A) : ℝ := (ψ x).re

private theorem value_cases (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ) (x : A) :
    ψ x = 1 ∨ ψ x = -1 := by
  apply mul_self_eq_one_iff.mp
  rw [← AddChar.map_add_eq_mul, two, AddChar.map_zero_eq_one]

theorem abs_sign (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ) (x : A) :
    |sign ψ x| = 1 := by
  rcases value_cases two ψ x with h | h <;> simp [sign, h]

variable [Fintype A]

open Classical in
theorem sign_difference_sum (two : ∀ x : A, x + x = 0) (x y : A) :
    (∑ ψ : AddChar A ℂ, |sign ψ x - sign ψ y|) ≤ (Fintype.card A : ℝ) := by
  by_cases hxy : x = y
  · subst y
    simp
  have hsub : x + y ≠ 0 := fun h =>
    hxy ((eq_neg_iff_add_eq_zero.mpr h).trans (eq_neg_iff_add_eq_zero.mpr (two y)).symm)
  have hsum : (∑ ψ : AddChar A ℂ, sign ψ (x + y)) = 0 := by
    have h := congrArg Complex.re (AddChar.sum_apply_eq_ite (x + y))
    simpa [sign, Complex.re_sum, hsub] using h
  have hterm (ψ : AddChar A ℂ) : |sign ψ x - sign ψ y| = 1 - sign ψ (x + y) := by
    rcases value_cases two ψ x with hx | hx <;>
      rcases value_cases two ψ y with hy | hy <;>
      norm_num [sign, AddChar.map_add_eq_mul, hx, hy]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, hsum, sub_zero]
  simp [AddChar.card_eq]

noncomputable def moment (p : A → ℝ) (ψ : AddChar A ℂ) : ℝ :=
  ∑ x, p x * sign ψ x

noncomputable def logCoefficient (a : A) (p : A → ℝ) : ℝ :=
  (-2 / (Fintype.card A : ℝ)) * ∑ ψ : AddChar A ℂ, sign ψ a * Real.log |moment p ψ|

/-- The logarithmic parity coefficient is Lipschitz in total variation on pairs
of equal-mass input functions with a common positive absolute sign-moment floor. -/
theorem log_parity_coefficient_stability (two : ∀ x : A, x + x = 0)
    (p q : A → ℝ) (hmass : ∑ x, p x = ∑ x, q x) (a : A) (e : ℝ) (he : 0 < e)
    (hp : ∀ ψ, e ≤ |moment p ψ|) (hq : ∀ ψ, e ≤ |moment q ψ|) :
    |logCoefficient a p - logCoefficient a q| ≤ 2 * totalVariation p q / e := by
  classical
  choose w hw hlog using fun ψ => log_abs_slope he (hp ψ) (hq ψ)
  let k (x : A) := ∑ ψ : AddChar A ℂ, sign ψ a * w ψ * sign ψ x
  have hosc (x y : A) : |k x - k y| ≤ (Fintype.card A : ℝ) / e := by
    dsimp [k]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ ψ : AddChar A ℂ, |sign ψ a * w ψ * sign ψ x - sign ψ a * w ψ * sign ψ y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ψ : AddChar A ℂ, (1 / e) * |sign ψ x - sign ψ y| := by
        apply Finset.sum_le_sum
        intro ψ _
        rw [← mul_sub, abs_mul, abs_mul, abs_sign two, one_mul]
        exact mul_le_mul_of_nonneg_right (hw ψ) (abs_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right (sign_difference_sum two x y) he.le
  have hcoef : logCoefficient a p - logCoefficient a q =
      (-2 / (Fintype.card A : ℝ)) * ∑ x, (p x - q x) * k x := by
    unfold logCoefficient
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    have hdiff (ψ : AddChar A ℂ) :
        moment p ψ - moment q ψ = ∑ x, (p x - q x) * sign ψ x := by
      simp only [moment, sub_mul, Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hlog, hdiff]
    calc
      _ = ∑ ψ : AddChar A ℂ, ∑ x, (p x - q x) * (sign ψ a * w ψ * sign ψ x) := by
        apply Finset.sum_congr rfl
        intro ψ _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [k, Finset.mul_sum]
  rw [hcoef, abs_mul]
  have hcard : 0 < (Fintype.card A : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg hcard.le, show |(-2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ (2 / (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / e * totalVariation p q) :=
      mul_le_mul_of_nonneg_left (abs_expectation_le_oscillation p q k hmass _ hosc) (by positivity)
    _ = _ := by field_simp

private noncomputable def twoPointMass (q : ℝ) (x : Bool) : ℝ :=
  if x then (1 - q) / 2 else (1 + q) / 2

/-- For each positive moment floor below one, any constant smaller than two
fails for a pair of admissible one-bit bias factors. -/
theorem log_bernoulli_bias_sharp (e c : ℝ) (he : 0 < e) (he₁ : e < 1) (hc : c < 2) :
    ∃ q : ℝ, e < q ∧ q < 1 ∧
      c * totalVariation (twoPointMass q) (twoPointMass e) / e <
        Real.log q - Real.log e := by
  let M : ℝ := max 1 c
  have hM₀ : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM₂ : M < 2 := max_lt (by norm_num) hc
  let gap := min (1 - e) (e * (2 - M) / M) / 2
  have hgap : 0 < gap := by
    dsimp [gap]
    exact half_pos (lt_min (sub_pos.mpr he₁) (div_pos (mul_pos he (sub_pos.mpr hM₂)) hM₀))
  have hgap₁ : gap < 1 - e := by
    have h := min_le_left (1 - e) (e * (2 - M) / M)
    dsimp [gap]
    linarith
  have hgapM : gap * M < e * (2 - M) := by
    apply (lt_div_iff₀ hM₀).mp
    have h := min_le_right (1 - e) (e * (2 - M) / M)
    dsimp [gap] at hgap ⊢
    linarith
  let q := e + gap
  refine ⟨q, by dsimp [q]; linarith, by dsimp [q]; linarith, ?_⟩
  have hq₀ : 0 < q := by dsimp [q]; positivity
  have htv : totalVariation (twoPointMass q) (twoPointMass e) = gap / 2 := by
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    unfold totalVariation
    rw [hu]
    have hminus : (1 - q) / 2 - (1 - e) / 2 = -(gap / 2) := by dsimp [q]; ring
    have hplus : (1 + q) / 2 - (1 + e) / 2 = gap / 2 := by dsimp [q]; ring
    have hhalf : 0 ≤ gap / 2 := by positivity
    simp [twoPointMass, hminus, hplus, abs_of_nonneg hhalf]
    ring
  have hlower : gap / q ≤ Real.log q - Real.log e := by
    have h := Real.log_le_sub_one_of_pos (div_pos he hq₀)
    rw [Real.log_div he.ne' hq₀.ne'] at h
    have hd : e / q - 1 = - (gap / q) := by
      rw [← div_self hq₀.ne', ← sub_div]
      dsimp [q]
      ring
    rw [hd] at h
    linarith
  rw [htv]
  apply lt_of_lt_of_le _ hlower
  have hcross : c * q < 2 * e := by
    have hh : c * q ≤ M * q := mul_le_mul_of_nonneg_right (le_max_right _ _) hq₀.le
    dsimp [q] at hh ⊢
    nlinarith [hgapM]
  rw [div_lt_iff₀ he, div_mul_eq_mul_div, lt_div_iff₀ hq₀]
  nlinarith [mul_pos hgap (sub_pos.mpr hcross)]

end D5.S3.TotalVariation.ParityLogStability
