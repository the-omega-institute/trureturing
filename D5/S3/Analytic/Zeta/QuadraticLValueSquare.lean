/- GID: D5/S3/Analytic/Zeta/QuadraticLValueSquare
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/QuadraticLValueSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Squared zero and one values for primitive self-dual odd Dirichlet characters. -/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.Analytic.Zeta.QuadraticLValueSquare

open DirichletCharacter

/-- Two applications of the functional equation eliminate the root number without
choosing its sign. This is an equality for the actual completed L-functions. -/
theorem completed_zero_sq (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive) (hself : χ⁻¹ = χ) (hne : χ ≠ 1) :
    completedLFunction χ 0 ^ 2 = (N : ℂ) * completedLFunction χ 1 ^ 2 := by
  let q : ℂ := (N : ℂ) ^ (1 / 2 : ℂ)
  let r : ℂ := rootNumber χ
  let a : ℂ := completedLFunction χ 0
  let b : ℂ := completedLFunction χ 1
  have hq : q ^ 2 = (N : ℂ) := by
    simpa [q] using
      (Complex.cpow_nat_inv_pow (N : ℂ) (by norm_num : (2 : ℕ) ≠ 0))
  have hqne : q ≠ 0 := by
    intro h
    have := hq
    rw [h, zero_pow two_ne_zero] at this
    exact (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0) this.symm
  have h0 : b = q⁻¹ * r * a := by
    simpa only [sub_zero, zero_sub, hself, Complex.cpow_neg] using
      hprim.completedLFunction_one_sub (0 : ℂ)
  have h1 : a = q * r * b := by
    simpa only [sub_self, hself, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] using
      hprim.completedLFunction_one_sub (1 : ℂ)
  have hb : b ≠ 0 := by
    intro h
    apply LFunction_apply_one_ne_zero hne
    rw [LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero)]
    exact div_eq_zero_iff.mpr (Or.inl h)
  have hr : r ≠ 0 := by
    intro h
    apply hb
    simpa only [h, mul_zero, zero_mul] using h0
  have h0q : q * b = r * a := by
    rw [h0]
    field_simp [hqne]
  have hmul : r * (a ^ 2 - q ^ 2 * b ^ 2) = 0 := by
    calc
      _ = a * (r * a) - q * b * (q * r * b) := by ring
      _ = a * (q * b) - q * b * a := by rw [← h0q, ← h1]
      _ = 0 := by ring
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hr)
  rw [hq] at heq
  exact heq

/-- For odd characters the two Gamma factors are 1 and the reciprocal of pi.
No root-number evaluation is used in this uncompleted L-value identity. -/
theorem zero_sq (N : ℕ) [NeZero N] (hN : N ≠ 1)
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hself : χ⁻¹ = χ) (hne : χ ≠ 1) (hodd : χ.Odd) :
    LFunction χ 0 ^ 2 = (N : ℂ) * (LFunction χ 1 / (Real.pi : ℂ)) ^ 2 := by
  have hgamma : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    norm_num [Complex.Gammaℝ_def, Complex.cpow_neg_one]
  have hzero : LFunction χ 0 = completedLFunction χ 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN),
      hodd.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one]
  have hone : LFunction χ 1 / (Real.pi : ℂ) = completedLFunction χ 1 := by
    rw [LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero),
      hodd.gammaFactor_def, show (1 : ℂ) + 1 = 2 by norm_num, hgamma]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hzero, hone]
  exact completed_zero_sq N χ hprim hself hne

end D5.S3.Analytic.Zeta.QuadraticLValueSquare
