/- GID: D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilGammaScaleModulus
   mirror-E: none(waiver:Gamma-Plancherel-and-common-form-domain-bridges)
   anchors: []
   utility: none
   digest: Bound actual cosine-translation changes by the finite positive Gamma resolvent sum with an explicit harmonic cutoff. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Gamma-weighted modulus across arithmetic scale thresholds

For the actual Weil Gamma multiplier, the classical digamma expansion is

  gamma(xi) - gamma(0) = sum_j 2*xi^2 / (b_j*(b_j^2+xi^2)), b_j=2*j+1/2.

This source treats its *actual finite positive partial sums*. It proves a
harmonic high-frequency floor and then bounds the cosine multiplier of the
symmetric prime-translation difference at arbitrary real shifts. Neither a
translation modulus nor an estimate on the completed Gamma sum is an input.

The passage to gamma, Plancherel, dilation onto the common interval, and the
closed-form/norm-resolvent perturbation theorem are proved on paper in the
existing RH theory volume. They are not asserted as kernel conclusions here.
The sharp ordinary-operator-norm jump at prime activation is retained; the
new estimate concerns the Gamma form norm. No global simple-even theorem,
unbounded-scale error decay or Xi limit is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilGammaScaleModulus

open scoped BigOperators

/-- One plus the finite positive resolvent sum of the original Gamma factor.
This is a partial sum, not a replacement definition of the digamma function. -/
def gammaShiftPartial (J : ℕ) (xi : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range J,
    2 * xi ^ 2 /
      ((2 * (j : ℝ) + 1 / 2) * ((2 * (j : ℝ) + 1 / 2) ^ 2 + xi ^ 2))

/-- The partial Gamma weight dominates the unweighted Fourier energy. -/
theorem gamma_shift_partial_one_le (J : ℕ) (xi : ℝ) :
    1 ≤ gammaShiftPartial J xi := by
  unfold gammaShiftPartial
  have h : 0 ≤ ∑ j ∈ Finset.range J,
      2 * xi ^ 2 /
        ((2 * (j : ℝ) + 1 / 2) * ((2 * (j : ℝ) + 1 / 2) ^ 2 + xi ^ 2)) := by
    apply Finset.sum_nonneg
    intro j _
    positivity
  linarith

private theorem harmonic_half (J : ℕ) :
    (harmonic J : ℝ) / 2 =
      ∑ j ∈ Finset.range J, 1 / (2 * ((j : ℝ) + 1)) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_div, mul_inv_rev]
  ring

private theorem harmonic_nonneg (J : ℕ) : 0 ≤ (harmonic J : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv,
    Nat.cast_add, Nat.cast_one]
  positivity

/-- Above the independently chosen cutoff 2J, the actual finite Gamma sum
already sees at least half the Jth harmonic number. In particular its floor
can grow without assuming a lower bound on an unspecified symbol. -/
theorem gamma_shift_partial_high_frequency (J : ℕ) (xi : ℝ)
    (hcut : 2 * (J : ℝ) ≤ |xi|) :
    1 + (harmonic J : ℝ) / 2 ≤ gammaShiftPartial J xi := by
  unfold gammaShiftPartial
  apply add_le_add_right
  rw [harmonic_half]
  apply Finset.sum_le_sum
  intro j hj
  let b : ℝ := 2 * (j : ℝ) + 1 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hjJ : (j : ℝ) + 1 ≤ (J : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
  have hbcut : b ≤ |xi| := by dsimp [b]; linarith
  have hbsmall : b ≤ 2 * ((j : ℝ) + 1) := by dsimp [b]; linarith
  have hsquare : b ^ 2 ≤ xi ^ 2 := by
    calc
      b ^ 2 ≤ |xi| ^ 2 := (sq_le_sq₀ hb.le (abs_nonneg xi)).mpr hbcut
      _ = xi ^ 2 := sq_abs xi
  change 1 / (2 * ((j : ℝ) + 1)) ≤ 2 * xi ^ 2 / (b * (b ^ 2 + xi ^ 2))
  have hd : 0 < b * (b ^ 2 + xi ^ 2) := by positivity
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ((j : ℝ) + 1)) hd).mpr
  calc
    1 * (b * (b ^ 2 + xi ^ 2)) ≤ b * (2 * xi ^ 2) := by
      simp only [one_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) hb.le
    _ ≤ (2 * ((j : ℝ) + 1)) * (2 * xi ^ 2) :=
      mul_le_mul_of_nonneg_right hbsmall (by positivity)
    _ = 2 * xi ^ 2 * (2 * ((j : ℝ) + 1)) := by ring

/-- The actual symmetric translation multiplier has a quantitative Gamma
form modulus. It is linear in the low-frequency displacement and inverse
harmonic in the high-frequency cutoff, including both signs of all inputs. -/
theorem gamma_controlled_cosine_difference (J : ℕ) (s t xi : ℝ) :
    |Real.cos (s * xi) - Real.cos (t * xi)| ≤
      (2 * (J : ℝ) * |s - t| + 2 / (1 + (harmonic J : ℝ) / 2)) *
        gammaShiftPartial J xi := by
  let D : ℝ := 1 + (harmonic J : ℝ) / 2
  have hD : 0 < D := by dsimp [D]; linarith [harmonic_nonneg J]
  have hw := gamma_shift_partial_one_le J xi
  have hw0 : 0 ≤ gammaShiftPartial J xi := by linarith
  have hlow : 0 ≤ 2 * (J : ℝ) * |s - t| := by positivity
  have htail : 0 ≤ 2 / D := by positivity
  have hphase : |Real.cos (s * xi) - Real.cos (t * xi)| ≤ |s - t| * |xi| := by
    simpa only [← sub_mul, abs_mul] using Real.abs_cos_sub_cos_le (s * xi) (t * xi)
  have htwo : |Real.cos (s * xi) - Real.cos (t * xi)| ≤ 2 := by
    calc
      _ ≤ |Real.cos (s * xi)| + |Real.cos (t * xi)| := abs_sub _ _
      _ ≤ 2 := by linarith [Real.abs_cos_le_one (s * xi), Real.abs_cos_le_one (t * xi)]
  change _ ≤ (2 * (J : ℝ) * |s - t| + 2 / D) * gammaShiftPartial J xi
  by_cases hnear : |xi| ≤ 2 * (J : ℝ)
  · calc
      _ ≤ |s - t| * |xi| := hphase
      _ ≤ |s - t| * (2 * (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hnear (abs_nonneg _)
      _ ≤ 2 * (J : ℝ) * |s - t| + 2 / D := by nlinarith
      _ ≤ (2 * (J : ℝ) * |s - t| + 2 / D) * gammaShiftPartial J xi :=
        le_mul_of_one_le_right (add_nonneg hlow htail) hw
  · have hhigh : D ≤ gammaShiftPartial J xi :=
      gamma_shift_partial_high_frequency J xi (le_of_lt (lt_of_not_ge hnear))
    calc
      _ ≤ 2 := htwo
      _ = (2 / D) * D := (div_mul_cancel₀ 2 hD.ne').symm
      _ ≤ (2 / D) * gammaShiftPartial J xi :=
        mul_le_mul_of_nonneg_left hhigh htail
      _ ≤ (2 * (J : ℝ) * |s - t| + 2 / D) * gammaShiftPartial J xi :=
        mul_le_mul_of_nonneg_right (by linarith) hw0

/-- A disjoint unit interval controls each noninitial term of the derivative
of the actual Gamma increment with respect to log-frequency. Integrating and
summing these intervals gives a uniform scaling bound; neither monotonicity
of the whole digamma function nor a fitted numerical constant is assumed. -/
theorem gamma_log_scale_derivative_term (j : ℕ) (t u : ℝ)
    (hlo : 2 * (j : ℝ) + 3 / 2 ≤ u)
    (hhi : u ≤ 2 * (j : ℝ) + 5 / 2) :
    4 * (2 * (j : ℝ) + 5 / 2) * t ^ 2 /
        (((2 * (j : ℝ) + 5 / 2) ^ 2 + t ^ 2) ^ 2) ≤
      (5 / 3 : ℝ) * (4 * u * t ^ 2 / ((u ^ 2 + t ^ 2) ^ 2)) := by
  let b : ℝ := 2 * (j : ℝ) + 5 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hu : 0 < u := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hub : u ≤ b := hhi
  have hratio : 4 * b ≤ (5 / 3 : ℝ) * 4 * u := by
    dsimp [b]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hs : u ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hu.le hb.le).mpr hub
  have hdu : 0 < (u ^ 2 + t ^ 2) ^ 2 := by positivity
  have hdb : 0 ≤ (b ^ 2 + t ^ 2) ^ 2 := sq_nonneg _
  have hden : (u ^ 2 + t ^ 2) ^ 2 ≤ (b ^ 2 + t ^ 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  change 4 * b * t ^ 2 / ((b ^ 2 + t ^ 2) ^ 2) ≤ _
  calc
    _ ≤ ((5 / 3 : ℝ) * 4 * u * t ^ 2) / ((b ^ 2 + t ^ 2) ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio (sq_nonneg t)) hdb
    _ ≤ ((5 / 3 : ℝ) * 4 * u * t ^ 2) / ((u ^ 2 + t ^ 2) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hdu hden
    _ = _ := by ring

#print axioms gamma_shift_partial_one_le
#print axioms gamma_shift_partial_high_frequency
#print axioms gamma_controlled_cosine_difference
#print axioms gamma_log_scale_derivative_term

end D5.S3.Weil.ZetaBridge.WeilGammaScaleModulus
