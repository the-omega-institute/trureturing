/- GID: D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteTieGeneratingFunction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The ordinary generating function of the complete Hermite absolute-tie enumeration. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Analytic.Polynomial.HermiteTieGeneratingFunction

open PowerSeries

noncomputable def P : ℚ⟦X⟧ := 8 * X + 5 * X^2 + 5 * X^3 - X^4 - X^5

noncomputable def D : ℚ⟦X⟧ := (1 - X)^3 * (1 + X)^2

def claim : Prop :=
  ∃ a : ℕ → ℕ,
    (∀ n, 1 ≤ n → 0 < a n) ∧
    (∀ n m, 1 ≤ n → n < m → a n < a m) ∧
    (∀ k, D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.HasExactlyTwo k ↔
      ∃! n, 1 ≤ n ∧ a n = k) ∧
    ∃ S : ℚ⟦X⟧, coeff 0 S = 0 ∧
      (∀ n, 1 ≤ n → coeff n S = (a n : ℚ)) ∧
      constantCoeff D = 1 ∧ S = P * D⁻¹

private noncomputable def T0 : ℚ⟦X⟧ := mk 1

private noncomputable def T1 : ℚ⟦X⟧ := mk fun n => ((1 + n).choose 1 : ℚ)

private noncomputable def T2 : ℚ⟦X⟧ := mk fun n => ((2 + n).choose 2 : ℚ)

private noncomputable def U : ℚ⟦X⟧ := rescale (-1) T1

private noncomputable def F : ℚ⟦X⟧ :=
  T2 + T2 + T2 + T2 - (T1 + T1) - (T0 + T0) - U + 1

private theorem quotient : F = P * D⁻¹ := by
  have h0 : T0 * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℚ
  have h1 : T1 * (1 - X)^2 = 1 := mk_add_choose_mul_one_sub_pow_eq_one ℚ 1
  have h2 : T2 * (1 - X)^3 = 1 := mk_add_choose_mul_one_sub_pow_eq_one ℚ 2
  have hu : U * (1 + X)^2 = 1 := by
    have h := congrArg (rescale (-1 : ℚ)) h1
    simpa [U, map_mul, map_pow, map_sub, rescale_neg_one_X, sub_neg_eq_add] using h
  apply (eq_mul_inv_iff_mul_eq (show constantCoeff D ≠ 0 by simp [D])).mpr
  dsimp [F, D, P]
  linear_combination 4 * (1 + X)^2 * h2 - 2 * (1 - X) * (1 + X)^2 * h1 -
    2 * (1 - X)^2 * (1 + X)^2 * h0 - (1 - X)^3 * hu

private theorem coeff_zero : coeff 0 F = 0 := by
  have hu : constantCoeff U = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    change coeff 0 (rescale (-1 : ℚ) T1) = 1
    rw [coeff_rescale]
    norm_num [T1]
  norm_num [F, T0, T1, T2, hu]

private theorem coeff_positive (n : ℕ) (hn : 1 ≤ n) :
    coeff n F = (D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a n : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  simp [F, T0, T1, T2, U, coeff_rescale,
    Nat.choose_one_right, Nat.cast_choose_two, hn0,
    D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a, pow_succ]
  ring

private noncomputable def actual (n : ℕ) : ℕ :=
  (D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a n).toNat

/-- The complete ordinary generating function assertion for OEIS A381737 Conjecture 3. -/
theorem result : claim := by
  have hc := D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.result
  have ha (n : ℕ) (hn : 1 ≤ n) :
      (actual n : ℤ) = D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a n := by
    exact Int.toNat_of_nonneg (le_of_lt (hc.1 n hn))
  refine ⟨actual, ?_, ?_, ?_, F, coeff_zero, ?_, by simp [D], quotient⟩
  · intro n hn
    have h := hc.1 n hn
    have h' := ha n hn
    omega
  · intro n m hn hnm
    exact (Int.toNat_lt_toNat (hc.1 m (by omega))).mpr (hc.2.1 n m hn hnm)
  · intro k
    rw [hc.2.2 k]
    have he (n : ℕ) :
        (1 ≤ n ∧ (k : ℤ) = D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.a n) ↔
          (1 ≤ n ∧ actual n = k) := by
      constructor
      · rintro ⟨hn, he⟩
        refine ⟨hn, ?_⟩
        have h := ha n hn
        omega
      · rintro ⟨hn, he⟩
        refine ⟨hn, ?_⟩
        rw [← ha n hn, he]
    simp only [he]
  · intro n hn
    rw [coeff_positive n hn]
    exact_mod_cast (ha n hn).symm

end D5.S3.Analytic.Polynomial.HermiteTieGeneratingFunction
