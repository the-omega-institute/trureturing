/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairRowSums
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Row sums 3·2^(n-2) and alternating row sums of the affine polynomial pair. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! Row sums and alternating row sums of the affine polynomial pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairRowSums

open D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
noncomputable section
section
open Polynomial

private theorem eval_at_one (m : ℕ) :
    ((pair (m + 1)).2).eval 1 = 3 * 2 ^ m ∧ ((pair (m + 1)).1).eval 1 = 3 * 2 ^ m - 1 := by
  induction m with
  | zero => simp [pair]
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl]
    simp only [pair, eval_add, eval_mul, eval_X, eval_one] at ih ⊢
    obtain ⟨h1, h2⟩ := ih
    constructor <;> rw [pow_succ] <;> linear_combination h1 + h2

/-- `w0 n = v_{n+1}(-1)`, the zero-based alternating row sums. -/
private def w0 (n : ℕ) : ℤ := ((pair n).2).eval (-1)

private theorem w_rec (n : ℕ) : w0 (n + 2) = 2 * w0 (n + 1) - 2 * w0 n := by
  simp only [w0, pair, eval_add, eval_mul, eval_X, eval_one]
  ring

private theorem w_init : w0 0 = 1 ∧ w0 1 = 3 := by
  constructor <;> simp [w0, pair]

end

section
open PowerSeries

private theorem w_gf : PowerSeries.mk w0 * (1 - 2 * X + 2 * X ^ 2) = 1 + X := by
  have h2 : (2 : ℤ⟦X⟧) = C 2 := (map_ofNat C 2).symm
  rw [h2, mul_add, mul_sub, mul_one, mul_left_comm, mul_left_comm (PowerSeries.mk w0) (C 2)]
  ext n
  obtain ⟨h0, h1⟩ := w_init
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_one, coeff_X]
  rw [show PowerSeries.mk w0 * X = PowerSeries.mk w0 * X ^ 1 by rw [pow_one], coeff_mul_X_pow',
    coeff_mul_X_pow']
  simp only [coeff_mk]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [h0, h1]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, ↓reduceIte]
    rw [show k + 2 - 1 = k + 1 by omega,
      show k + 2 - 2 = k by omega, w_rec]
    simp

/-- The alternating row sums `w_n = v_n(-1)` with the source index `n ≥ 1`. -/
def w (n : ℕ) : ℤ := ((pair (n - 1)).2).eval (-1)

/-- Corollary 5 of the Ma–Zhang note on A208509: for `n ≥ 2`, `v_n(1) = 3 · 2^(n-2)` and
`u_n(1) = 3 · 2^(n-2) - 1`, while `v_1(1) = u_1(1) = 1`; the alternating row sums `w_n = v_n(-1)`
have generating function `∑_{n ≥ 1} w_n z^(n-1) = (1 + z)/(1 - 2z + 2z^2)`, satisfy
`w_(n+2) = 2 w_(n+1) - 2 w_n`, and start `w_1 = 1`, `w_2 = 3`. -/
theorem result :
    (∀ n : ℕ, 2 ≤ n → ((pair (n - 1)).2).eval 1 = 3 * 2 ^ (n - 2) ∧
      ((pair (n - 1)).1).eval 1 = 3 * 2 ^ (n - 2) - 1) ∧
    ((pair 0).2.eval 1 = 1 ∧ (pair 0).1.eval 1 = 1) ∧
    PowerSeries.mk (fun i => w (i + 1)) *
      (1 - 2 * PowerSeries.X + 2 * PowerSeries.X ^ 2) = 1 + PowerSeries.X ∧
    (∀ n : ℕ, 1 ≤ n → w (n + 2) = 2 * w (n + 1) - 2 * w n) ∧
    w 1 = 1 ∧ w 2 = 3 := by
  have hw : ∀ i, w (i + 1) = w0 i := fun i => rfl
  refine ⟨fun n hn => ?_, by simp [pair], ?_, fun n hn => ?_, (w_init).1, (w_init).2⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simpa [show m + 2 - 1 = m + 1 by omega] using eval_at_one m
  · simp only [hw]
    exact w_gf
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hw, show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 1 = (m + 1) + 1 by omega]
    exact w_rec m

end
end
end D5.S1.Recurrence.Invariants.AffinePolynomialPairRowSums
