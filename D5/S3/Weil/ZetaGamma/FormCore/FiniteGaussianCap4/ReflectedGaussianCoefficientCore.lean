/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual reflected three-point Gaussian sources generate the weighted charge kernel. -/
/-
SPDX-License-Identifier: Apache-2.0
Actual reflected Gaussian coefficient core, 2026-10-26.

The generic weighted-charge core is imported from its analytic domain.
The existing site_q_neg and site_amplitude_neg proofs in
FiniteGaussianEvenExpansion have only been made public for this consumer.

The physical Gaussian source is literally [1,1,-2] at [a,-a,0]. Its actual
finiteGaussianNormalizedCoefficient and finite_gaussian_central_mass_zero
are reused. Positive even coordinates and actual charge identify coordinate
zero by the companion's uniqueness argument. No beta/binomial identity,
assumed expansion, coefficient membership, density, or Laguerre completeness
occurs as a premise. The conclusion is precisely the X4 coefficient core;
it is not density in originalPhysicalH6 or the original Suzuki M domain.
-/

import D5.S3.Analytic.PowerSeries.WeightedChargeKernelCore
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianCentralMass
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! The weighted coefficient core of the actual reflected three-point Gaussian source. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RHGaussianDilationCore

open FiniteGaussianCap4 FiniteGaussianCap4.LaguerreSevenHalf

def actualCentralZ (n : ℕ) : ℝ :=
  normalizedCentralMellin (2 * n) / normalizedCentralMellin 0

def actualEvenInverseNormalization (n : ℕ) : ℝ :=
  1 / centralNormalization (2 * n)

private theorem actualCentralZ_zero : actualCentralZ 0 = 1 := by
  have h0 : normalizedCentralMellin 0 ≠ 0 := by
    simpa only [Nat.mul_zero] using (normalizedCentralMellin_even_pos 0).ne'
  simp [actualCentralZ, h0]

private theorem actualCentralZ_abs_le_one (n : ℕ) : |actualCentralZ n| ≤ 1 := by
  have hweight : ∀ n : ℕ, FiniteGaussianCap4.weight n ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num [FiniteGaussianCap4.weight]
    | succ k hk =>
      rw [central_weight_step]
      have hr : (((k : ℝ) + 9 / 4) * ((k : ℝ) + 1 / 2)) /
          (((k : ℝ) + 11 / 4) * ((k : ℝ) + 1)) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ FiniteGaussianCap4.weight k * 1 :=
          mul_le_mul_of_nonneg_left hr (central_weight_pos k).le
        _ ≤ 1 := by simpa using hk
  have hzpos : 0 < actualCentralZ n :=
    div_pos (normalizedCentralMellin_even_pos n) (normalizedCentralMellin_even_pos 0)
  have hzsq : actualCentralZ n ^ 2 ≤ 1 :=
    (normalizedCentralMellin_weight n).2.trans_le (hweight n)
  rw [abs_of_pos hzpos]
  exact (sq_le_sq₀ hzpos.le (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using hzsq)

/-- The actual continuous central-charge covector in the weighted coordinates. -/
def actualCentralChargeVector : GaussianCoeffSpace :=
  gaussianChargeVector actualCentralZ actualCentralZ_abs_le_one

private theorem inverse_normalization_even_growth (n : ℕ) :
    |actualEvenInverseNormalization n| ≤
      (1 / centralNormalization 0) * (9 / 2 : ℝ) ^ n := by
  have hstep : ∀ m : ℕ, centralNormalization m ^ 2 ≤
      (9 / 2 : ℝ) * centralNormalization (m + 1) ^ 2 := by
    intro m
    rw [centralNormalization_sq_step]
    have hr : 1 ≤ (9 / 2 : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) + 9 / 2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h := mul_le_mul_of_nonneg_right hr (sq_nonneg (centralNormalization m))
    nlinarith
  have htwo : ∀ k : ℕ, centralNormalization (2 * k) ≤
      (9 / 2 : ℝ) * centralNormalization (2 * (k + 1)) := by
    intro k
    have h1 := hstep (2 * k)
    have h2 := hstep (2 * k + 1)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at h2
    apply (sq_le_sq₀ (centralNormalization_pos _).le
      (mul_nonneg (by norm_num) (centralNormalization_pos _).le)).mp
    nlinarith
  have hinv : ∀ k : ℕ, 1 / centralNormalization (2 * (k + 1)) ≤
      (9 / 2 : ℝ) * (1 / centralNormalization (2 * k)) := by
    intro k
    calc
      _ ≤ (9 / 2 : ℝ) / centralNormalization (2 * k) :=
        (div_le_div_iff₀ (centralNormalization_pos _) (centralNormalization_pos _)).2
          (by simpa only [one_mul] using htwo k)
      _ = _ := by ring
  rw [actualEvenInverseNormalization, abs_of_pos (one_div_pos.mpr (centralNormalization_pos _))]
  induction n with
  | zero => simp
  | succ n hn =>
      calc
        _ ≤ (9 / 2 : ℝ) * (1 / centralNormalization (2 * n)) := hinv n
        _ ≤ (9 / 2 : ℝ) * ((1 / centralNormalization 0) * (9 / 2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hn (by norm_num)
        _ = _ := by rw [pow_succ]; ring

def reflectedSourceCoefficient : Fin 3 → ℝ := ![1, 1, -2]

def reflectedSourceSite (a : ℝ) : Fin 3 → ℝ := ![a, -a, 0]

private theorem reflectedSource_mass_zero : ∑ i, reflectedSourceCoefficient i = 0 := by
  norm_num [reflectedSourceCoefficient, Fin.sum_univ_succ]

private theorem gaussianSiteAmplitude_pos (a : ℝ) : 0 < gaussianSiteAmplitude a := by
  unfold gaussianSiteAmplitude
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (gaussianSiteQ_one_sub_pos a) _)

/-- The literal three-point source has the claimed positive even coordinates;
the constant coefficient is deliberately not guessed here. -/
private theorem reflectedSource_even_coefficient (a : ℝ) (n : ℕ) (hn : n ≠ 0) :
    finiteGaussianCoefficient reflectedSourceCoefficient (reflectedSourceSite a) (2 * n) =
      2 * gaussianSiteAmplitude a * gaussianSiteQ a ^ (2 * n) := by
  have hpower : 2 * n ≠ 0 := Nat.mul_ne_zero (by decide) hn
  have hq0 : gaussianSiteQ 0 = 0 := by norm_num [gaussianSiteQ]
  have hA0 : gaussianSiteAmplitude 0 = 1 := by norm_num [gaussianSiteAmplitude, hq0]
  simp only [finiteGaussianCoefficient, Fin.sum_univ_succ, reflectedSourceCoefficient,
    reflectedSourceSite, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    mul_one, one_mul, add_zero]
  rw [FiniteGaussianCap4.site_q_neg, FiniteGaussianCap4.site_amplitude_neg, hq0, hA0,
    zero_pow hpower]
  simp only [pow_mul, neg_sq, mul_zero, add_zero]
  ring

def positiveGaussianSite (t : ℝ) : ℝ :=
  Real.log ((1 + Real.sqrt t) / (1 - Real.sqrt t)) / 2

private theorem positiveGaussianSite_q (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    gaussianSiteQ (positiveGaussianSite t) = Real.sqrt t := by
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t < 1 := (Real.sqrt_lt ht.le (by norm_num)).2 (by simpa using ht1)
  have hminus : 0 < 1 - Real.sqrt t := by linarith
  have hplus : 0 < 1 + Real.sqrt t := by linarith
  have he : Real.exp (2 * positiveGaussianSite t) =
      (1 + Real.sqrt t) / (1 - Real.sqrt t) := by
    rw [show 2 * positiveGaussianSite t =
      Real.log ((1 + Real.sqrt t) / (1 - Real.sqrt t)) by unfold positiveGaussianSite; ring]
    exact Real.exp_log (div_pos hplus hminus)
  unfold gaussianSiteQ
  rw [he]
  field_simp [hminus.ne']
  <;> ring

/-- Actual normalized even coefficients of B_a/(2*Amplitude(a)). -/
def actualReflectedCurveCoefficient (t : ℝ) (n : ℕ) : ℝ :=
  finiteGaussianNormalizedCoefficient reflectedSourceCoefficient
      (reflectedSourceSite (positiveGaussianSite t)) (2 * n) /
    (2 * gaussianSiteAmplitude (positiveGaussianSite t))

private theorem actualReflectedCurve_tail (t : ℝ) (ht : 0 < t) (htsmall : t < 1 / 36)
    (n : ℕ) (hn : n ≠ 0) :
    actualReflectedCurveCoefficient t n = actualEvenInverseNormalization n * t ^ n := by
  have hq : gaussianSiteQ (positiveGaussianSite t) ^ 2 = t := by
    rw [positiveGaussianSite_q t ht (by linarith)]
    exact Real.sq_sqrt ht.le
  unfold actualReflectedCurveCoefficient finiteGaussianNormalizedCoefficient
    actualEvenInverseNormalization
  rw [reflectedSource_even_coefficient _ n hn, pow_mul, hq]
  field_simp [(centralNormalization_pos (2 * n)).ne',
    (gaussianSiteAmplitude_pos (positiveGaussianSite t)).ne']
  <;> ring

private theorem actualReflectedCurve_charge (t : ℝ) :
    HasSum (fun n => actualCentralZ n * actualReflectedCurveCoefficient t n) 0 := by
  have h := (finite_gaussian_central_mass_zero reflectedSourceCoefficient
    (reflectedSourceSite (positiveGaussianSite t)) reflectedSource_mass_zero).1
  have hdiv := h.div_const (2 * gaussianSiteAmplitude (positiveGaussianSite t))
  convert hdiv using 1
  · funext n
    unfold actualCentralZ actualReflectedCurveCoefficient
    ring
  · simp

/-- The exact finite reflected Gaussian coefficient vectors exist in X4 and
their closed span equals the continuous actual-charge kernel. The original
physical synthesis and energy-form extension remain separate obligations. -/
theorem actual_reflected_gaussian_coefficient_core :
    ∃ f : ℝ → GaussianCoeffSpace,
      (∀ t : ℝ, 0 < t → t < 1 / 36 → ∀ n : ℕ,
        f t n = coeffWeight n * actualReflectedCurveCoefficient t n) ∧
      positiveCurveSpan f (1 / 36) =
        (coeffCharge actualCentralChargeVector).ker := by
  apply weighted_charge_kernel_core_of_scalar_curve (r := 1 / 36)
    actualCentralZ actualEvenInverseNormalization
    actualCentralZ_zero actualCentralZ_abs_le_one
    (fun n => one_div_ne_zero (centralNormalization_pos _).ne')
    (one_div_pos.mpr (centralNormalization_pos 0)).le inverse_normalization_even_growth
    actualReflectedCurveCoefficient (by norm_num) le_rfl
  · intro t _ _
    exact actualReflectedCurve_charge t
  · exact actualReflectedCurve_tail

end RHGaussianDilationCore
