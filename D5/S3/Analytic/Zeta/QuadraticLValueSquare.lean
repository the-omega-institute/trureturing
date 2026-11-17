/- GID: D5/S3/Analytic/Zeta/QuadraticLValueSquare
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/QuadraticLValueSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-character zero and one products, with self-dual square specializations. -/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.Analytic.Zeta.QuadraticLValueSquare

open DirichletCharacter

/-- The primitive functional equation relates inverse-character products without
choosing a Gauss-sum sign. Nonvanishing at one justifies the cancellation. -/
theorem completed_zero_mul_inverse (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    completedLFunction χ 0 * completedLFunction χ⁻¹ 0 =
      (N : ℂ) * (completedLFunction χ 1 * completedLFunction χ⁻¹ 1) := by
  let q : ℂ := (N : ℂ) ^ (1 / 2 : ℂ)
  let ε : ℂ := rootNumber χ
  let a : ℂ := completedLFunction χ 0
  let a' : ℂ := completedLFunction χ⁻¹ 0
  let b : ℂ := completedLFunction χ 1
  let b' : ℂ := completedLFunction χ⁻¹ 1
  have hq : q ^ 2 = (N : ℂ) := by
    simpa [q] using
      (Complex.cpow_nat_inv_pow (N : ℂ) (by norm_num : (2 : ℕ) ≠ 0))
  have hqne : q ≠ 0 := by
    intro h
    have := hq
    rw [h, zero_pow two_ne_zero] at this
    exact (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0) this.symm
  have h0 : b = q⁻¹ * ε * a' := by
    simpa only [sub_zero, zero_sub, Complex.cpow_neg] using
      hprim.completedLFunction_one_sub (0 : ℂ)
  have h1 : a = q * ε * b' := by
    simpa only [sub_self, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] using
      hprim.completedLFunction_one_sub (1 : ℂ)
  have hb : b ≠ 0 := by
    intro h
    apply LFunction_apply_one_ne_zero hne
    rw [LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero)]
    exact div_eq_zero_iff.mpr (Or.inl h)
  have hε : ε ≠ 0 := by
    intro h
    apply hb
    simpa only [h, mul_zero, zero_mul] using h0
  have h0q : q * b = ε * a' := by
    rw [h0]
    field_simp [hqne]
  have hmul : ε * (a * a' - q ^ 2 * (b * b')) = 0 := by
    calc
      _ = a * (ε * a') - q * b * (q * ε * b') := by ring
      _ = a * (q * b) - q * b * a := by rw [← h0q, ← h1]
      _ = 0 := by ring
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hε)
  rw [hq] at heq
  exact heq

/-- For every nonprincipal primitive odd character the actual zero-side inverse
product is N/pi squared times the actual one-side inverse product. -/
theorem zero_mul_inverse (N : ℕ) [NeZero N] (hN : N ≠ 1)
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (hodd : χ.Odd) :
    LFunction χ 0 * LFunction χ⁻¹ 0 =
      (N : ℂ) * ((LFunction χ 1 / (Real.pi : ℂ)) *
        (LFunction χ⁻¹ 1 / (Real.pi : ℂ))) := by
  have hinv : χ⁻¹.Odd := by
    change χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv, hodd]
    norm_num
  have hgamma : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    norm_num [Complex.Gammaℝ_def, Complex.cpow_neg_one]
  have hzero (ψ : DirichletCharacter ℂ N) (hψ : ψ.Odd) :
      LFunction ψ 0 = completedLFunction ψ 0 := by
    rw [LFunction_eq_completed_div_gammaFactor ψ 0 (Or.inr hN),
      hψ.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one]
  have hone (ψ : DirichletCharacter ℂ N) (hψ : ψ.Odd) :
      LFunction ψ 1 / (Real.pi : ℂ) = completedLFunction ψ 1 := by
    rw [LFunction_eq_completed_div_gammaFactor ψ 1 (Or.inl one_ne_zero),
      hψ.gammaFactor_def, show (1 : ℂ) + 1 = 2 by norm_num, hgamma]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hzero χ hodd, hzero χ⁻¹ hinv, hone χ hodd, hone χ⁻¹ hinv]
  exact completed_zero_mul_inverse N χ hprim hne

/-- Two applications of the functional equation eliminate the root number without
choosing its sign. This is an equality for the actual completed L-functions. -/
theorem completed_zero_sq (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive) (hself : χ⁻¹ = χ) (hne : χ ≠ 1) :
    completedLFunction χ 0 ^ 2 = (N : ℂ) * completedLFunction χ 1 ^ 2 := by
  simpa only [hself, ← pow_two] using completed_zero_mul_inverse N χ hprim hne

/-- For odd characters the two Gamma factors are 1 and the reciprocal of pi.
No root-number evaluation is used in this uncompleted L-value identity. -/
theorem zero_sq (N : ℕ) [NeZero N] (hN : N ≠ 1)
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hself : χ⁻¹ = χ) (hne : χ ≠ 1) (hodd : χ.Odd) :
    LFunction χ 0 ^ 2 = (N : ℂ) * (LFunction χ 1 / (Real.pi : ℂ)) ^ 2 := by
  simpa only [hself, ← pow_two] using zero_mul_inverse N hN χ hprim hne hodd

end D5.S3.Analytic.Zeta.QuadraticLValueSquare
