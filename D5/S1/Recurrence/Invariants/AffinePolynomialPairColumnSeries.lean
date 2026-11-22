/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairColumnSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: The affine pair and its coefficient columns have rational generating functions. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! Generating functions of the affine polynomial pair and of its coefficient columns. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairColumnSeries

open PowerSeries D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients

/-- `A_d = ∑ C(n, d) z^n` satisfies `A_d (1 - z)^(d+1) = z^d`. -/
private theorem A_mul (d : ℕ) :
    (mk fun n => (Nat.choose n d : ℤ)) * (1 - X) ^ (d + 1) = X ^ d := by
  have h : (mk fun n => (Nat.choose n d : ℤ)) = X ^ d * mk fun n => (Nat.choose (d + n) d : ℤ) := by
    ext n
    rw [coeff_mk, coeff_X_pow_mul', coeff_mk]
    split_ifs with h
    · rw [show d + (n - d) = n by omega]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h, mul_assoc, mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

/-- Column series `∑ (C(n, d) + C(n+1, d)) z^n` for `d ≥ 1`. -/
private theorem col (d : ℕ) (hd : 1 ≤ d) :
    (mk fun n => (Nat.choose n d : ℤ) + Nat.choose (n + 1) d) * (1 - X) ^ (d + 1) =
      X ^ (d - 1) * (1 + X) := by
  have hz : (mk fun n => (Nat.choose (n + 1) d : ℤ)) * X = mk fun n => (Nat.choose n d : ℤ) := by
    ext n
    rcases n with _ | n
    · rw [coeff_zero_mul_X, coeff_mk, Nat.choose_eq_zero_of_lt (by omega)]; simp
    · rw [coeff_succ_mul_X, coeff_mk, coeff_mk]
  have hsplit : (mk fun n => (Nat.choose n d : ℤ) + Nat.choose (n + 1) d) =
      (mk fun n => (Nat.choose n d : ℤ)) + mk fun n => (Nat.choose (n + 1) d : ℤ) := by
    ext n; simp
  apply (mul_left_injective₀ (X_ne_zero (R := ℤ))).eq_iff.mp
  rw [hsplit, add_mul, add_mul, mul_right_comm (mk fun n => (Nat.choose (n + 1) d : ℤ)) _ X, hz,
    A_mul]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem v_col (k : ℕ) : (mk fun n => ((pair n).2).coeff k) * (1 - X) ^ (2 * k + 2) =
    X ^ (2 * k) * (1 + X) := by
  have h := col (2 * k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  congr 2
  ext n
  exact (pair_coeff n k).2

private theorem u_col (k : ℕ) (hk : 1 ≤ k) :
    (mk fun n => ((pair n).1).coeff k) * (1 - X) ^ (2 * k + 1) =
    X ^ (2 * k - 1) * (1 + X) := by
  rw [← col (2 * k) (by omega)]
  congr 2
  ext n
  rw [(pair_coeff n k).1]
  simp [show k ≠ 0 by omega]

private theorem u_col0 : (mk fun n => ((pair n).1).coeff 0) * (1 - X) = 1 := by
  have : (mk fun n => ((pair n).1).coeff 0) = mk 1 := by
    ext n; rw [coeff_mk, coeff_mk, (pair_coeff n 0).1]; simp
  rw [this]
  exact mk_one_mul_one_sub_eq_one ℤ

private theorem v_rec (n : ℕ) :
    (pair (n + 2)).2 = 2 * (pair (n + 1)).2 - (1 - Polynomial.X) * (pair n).2 := by
  have h1 : (pair (n + 2)).2 = (pair (n + 1)).1 + (pair (n + 1)).2 + 1 := rfl
  have h2 : (pair (n + 1)).1 = (pair n).1 + Polynomial.X * (pair n).2 := rfl
  have h3 : (pair (n + 1)).2 = (pair n).1 + (pair n).2 + 1 := rfl
  rw [h1, h2]
  linear_combination -h3

private theorem v_gf : (mk fun n => (pair n).2) *
    (1 - 2 * X + C (1 - Polynomial.X) * X ^ 2) = 1 + X := by
  have h2 : (2 : (Polynomial ℤ)⟦X⟧) = C 2 := (map_ofNat C 2).symm
  obtain ⟨c, hc⟩ : ∃ c : Polynomial ℤ, c = 1 - Polynomial.X := ⟨_, rfl⟩
  rw [← hc, h2, mul_add, mul_sub, mul_one, mul_left_comm,
    mul_left_comm (mk fun n => (pair n).2) (C c),
    show (mk fun n => (pair n).2) * X = (mk fun n => (pair n).2) * X ^ 1 by rw [pow_one]]
  refine PowerSeries.ext fun n => ?_
  rw [map_add, map_sub, map_add, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow', coeff_mul_X_pow',
    coeff_mk, coeff_one, coeff_X]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num [pair]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, ↓reduceIte, coeff_mk,
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, v_rec, hc]
    simp

/-- Corollary 4 of the Ma–Zhang note on A208509, in `ℤ[x]⟦z⟧` and `ℤ⟦z⟧` with `v_n` and `u_n`
at stage `n - 1`: `∑_{n ≥ 1} v_n z^(n-1) = (1 + z)/(1 - 2z + (1 - x) z^2)`; for every `k`,
the `k`-th v-column series is `z^(2k)(1 + z)/(1 - z)^(2k+2)`; for `k ≥ 1` the `k`-th
u-column series is `z^(2k-1)(1 + z)/(1 - z)^(2k+1)`; the constant u-column is `1/(1 - z)`. -/
theorem result :
    (mk fun n => (pair n).2) * (1 - 2 * X + C (1 - Polynomial.X) * X ^ 2) = 1 + X ∧
    (∀ k : ℕ, (mk fun n => ((pair n).2).coeff k) * (1 - X) ^ (2 * k + 2) =
      X ^ (2 * k) * (1 + X)) ∧
    (∀ k : ℕ, 1 ≤ k → (mk fun n => ((pair n).1).coeff k) * (1 - X) ^ (2 * k + 1) =
      X ^ (2 * k - 1) * (1 + X)) ∧
    (mk fun n => ((pair n).1).coeff 0) * (1 - X) = 1 :=
  ⟨v_gf, v_col, u_col, u_col0⟩

end D5.S1.Recurrence.Invariants.AffinePolynomialPairColumnSeries
