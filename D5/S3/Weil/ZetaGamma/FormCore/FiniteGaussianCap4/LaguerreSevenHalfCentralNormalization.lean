/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfCentralNormalization
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual central Mellin modes and normalized finite Gaussian charge. -/
/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No Lean/kernel or acceptance claim.

Positive normalization of the ACTUAL phi modes and identification with the
existing Cap4TailCharge.weight. No alternative weight definition is introduced.
The normalization is exactly sqrt(2^(9/2) n! / Gamma(n+9/2)).
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfCentralMellin
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4TailCharge
import Mathlib.Analysis.Real.Sqrt

/-! Actual central Mellin modes and normalized finite Gaussian charge. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- Positive square root of the specified norm reciprocal. -/
def centralNormalization (n : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ (9 / 2 : ℝ) * (n.factorial : ℝ) /
    Real.Gamma ((n : ℝ) + 9 / 2))

/-- psi_n = N_n phi_n, using the supplied actual mode. -/
def centralPsi (x : ℝ) (n : ℕ) : ℝ := centralNormalization n * phi x n

theorem centralNormalization_pos (n : ℕ) : 0 < centralNormalization n := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity))
    (Real.Gamma_pos_of_pos (by positivity))

theorem centralNormalization_sq (n : ℕ) :
    centralNormalization n ^ 2 = (2 : ℝ) ^ (9 / 2 : ℝ) * (n.factorial : ℝ) /
      Real.Gamma ((n : ℝ) + 9 / 2) := by
  apply Real.sq_sqrt
  exact (div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity))
    (Real.Gamma_pos_of_pos (by positivity))).le

/-- Normalization recurrence uses Gamma_add_one only; no duplication formula. -/
theorem centralNormalization_sq_step (n : ℕ) :
    centralNormalization (n + 1) ^ 2 =
      (((n : ℝ) + 1) / ((n : ℝ) + 9 / 2)) * centralNormalization n ^ 2 := by
  rw [centralNormalization_sq, centralNormalization_sq, Nat.factorial_succ]
  have he : ((n + 1 : ℕ) : ℝ) + 9 / 2 = ((n : ℝ) + 9 / 2) + 1 := by
    push_cast
    ring
  rw [he, Real.Gamma_add_one (by positivity)]
  push_cast
  field_simp [(Real.Gamma_pos_of_pos (show 0 < (n : ℝ) + 9 / 2 by positivity)).ne',
    show (n : ℝ) + 9 / 2 ≠ 0 by positivity]
  <;> ring

/-- Literal m_n = integral x^(5/4) psi_n. -/
def normalizedCentralMellin (n : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * centralPsi x n

theorem integrable_centralPsi (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * centralPsi x n) (Ioi 0) := by
  change Integrable _ (volume.restrict (Ioi 0))
  convert (integrable_central_phi n).const_mul (centralNormalization n) using 1
  funext x
  simp only [centralPsi]
  ring

theorem normalizedCentralMellin_eq (n : ℕ) :
    normalizedCentralMellin n = centralNormalization n * centralMellinIntegral n := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), centralNormalization n *
        (x ^ (5 / 4 : ℝ) * phi x n) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [centralPsi]
      ring
    _ = _ := integral_const_mul _ _

theorem normalizedCentralMellin_even (k : ℕ) :
    normalizedCentralMellin (2 * k) = centralNormalization (2 * k) *
      (Real.Gamma (9 / 4) * centralPochhammer k / (k.factorial : ℝ)) := by
  rw [normalizedCentralMellin_eq, centralMellinIntegral_even]

theorem normalizedCentralMellin_odd (k : ℕ) :
    normalizedCentralMellin (2 * k + 1) = 0 := by
  rw [normalizedCentralMellin_eq, centralMellinIntegral_odd, mul_zero]

theorem normalizedCentralMellin_even_pos (k : ℕ) :
    0 < normalizedCentralMellin (2 * k) := by
  rw [normalizedCentralMellin_eq]
  exact mul_pos (centralNormalization_pos _) (centralMellinIntegral_even_pos k)

/-- Squared m_n recurrence. All m's are actual integrals and the J recurrence
is the previously proved actual polynomial integral recurrence. -/
theorem normalizedCentralMellin_sq_step (n : ℕ) :
    normalizedCentralMellin (n + 2) ^ 2 =
      (((n : ℝ) + 1) * ((n : ℝ) + 9 / 2) /
        (((n : ℝ) + 2) * ((n : ℝ) + 11 / 2))) * normalizedCentralMellin n ^ 2 := by
  have hJ : centralMellinIntegral (n + 2) =
      (((n : ℝ) + 9 / 2) / ((n : ℝ) + 2)) * centralMellinIntegral n := by
    rw [div_mul_eq_mul_div₀]
    apply (eq_div_iff (show (n : ℝ) + 2 ≠ 0 by positivity)).2
    linear_combination centralMellinIntegral_step n
  rw [normalizedCentralMellin_eq, normalizedCentralMellin_eq, mul_pow, mul_pow,
    hJ, mul_pow]
  rw [show n + 2 = (n + 1) + 1 by omega,
    centralNormalization_sq_step, centralNormalization_sq_step]
  push_cast
  field_simp [show (n : ℝ) + 2 ≠ 0 by positivity,
    show (n : ℝ) + 9 / 2 ≠ 0 by positivity,
    show (n : ℝ) + 11 / 2 ≠ 0 by positivity,
    show (n : ℝ) + 1 + 9 / 2 ≠ 0 by positivity,
    show (n : ℝ) + 1 + 1 ≠ 0 by positivity]
  <;> ring

/-- The public recurrence of the EXISTING weight; its private ratio unfolds
by definitional equality, so no competing sequence is defined here. -/
theorem central_weight_step (k : ℕ) :
    FiniteGaussianCap4.weight (k + 1) = FiniteGaussianCap4.weight k *
      ((((k : ℝ) + 9 / 4) * ((k : ℝ) + 1 / 2)) /
        (((k : ℝ) + 11 / 4) * ((k : ℝ) + 1))) := by
  rfl

theorem central_weight_pos (k : ℕ) : 0 < FiniteGaussianCap4.weight k := by
  induction k with
  | zero => norm_num [FiniteGaussianCap4.weight]
  | succ k ih =>
      rw [central_weight_step]
      exact mul_pos ih (by positivity)

theorem normalizedCentralMellin_even_sq_step (k : ℕ) :
    normalizedCentralMellin (2 * (k + 1)) ^ 2 =
      normalizedCentralMellin (2 * k) ^ 2 *
        ((((k : ℝ) + 9 / 4) * ((k : ℝ) + 1 / 2)) /
          (((k : ℝ) + 11 / 4) * ((k : ℝ) + 1))) := by
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, normalizedCentralMellin_sq_step]
  push_cast
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity,
    show (k : ℝ) + 11 / 4 ≠ 0 by positivity,
    show 2 * (k : ℝ) + 2 ≠ 0 by positivity,
    show 2 * (k : ℝ) + 11 / 2 ≠ 0 by positivity]
  <;> ring

/-- Identification of the existing tail weights with squared actual integrals. -/
theorem normalizedCentralMellin_even_sq (k : ℕ) :
    normalizedCentralMellin (2 * k) ^ 2 =
      normalizedCentralMellin 0 ^ 2 * FiniteGaussianCap4.weight k := by
  induction k with
  | zero => simp [FiniteGaussianCap4.weight]
  | succ k ih =>
      rw [normalizedCentralMellin_even_sq_step, ih, central_weight_step]
      ring

/-- The requested normalized identity, including the positive sign choice. -/
theorem normalizedCentralMellin_weight (k : ℕ) :
    0 < normalizedCentralMellin (2 * k) ∧
      (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) ^ 2 =
        FiniteGaussianCap4.weight k := by
  have h0 : normalizedCentralMellin 0 ≠ 0 :=
    (normalizedCentralMellin_even_pos 0).ne'
  refine ⟨normalizedCentralMellin_even_pos k, ?_⟩
  rw [div_pow, normalizedCentralMellin_even_sq]
  field_simp [h0]
  <;> ring

/-- w_0=1 and the exact requested rational quotient, for the same weights. -/
theorem central_weight_zero_and_ratio :
    FiniteGaussianCap4.weight 0 = 1 ∧
      ∀ k : ℕ, FiniteGaussianCap4.weight (k + 1) / FiniteGaussianCap4.weight k =
        (((k : ℝ) + 9 / 4) * ((k : ℝ) + 1 / 2)) /
          (((k : ℝ) + 11 / 4) * ((k : ℝ) + 1)) := by
  refine ⟨rfl, fun k => ?_⟩
  rw [central_weight_step]
  field_simp [(central_weight_pos k).ne']
  <;> ring

end FiniteGaussianCap4.LaguerreSevenHalf
