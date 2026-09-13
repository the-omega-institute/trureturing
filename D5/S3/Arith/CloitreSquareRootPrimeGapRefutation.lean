/- GID: D5/S3/Arith/CloitreSquareRootPrimeGapRefutation
   generality: G
   mirror-B: D5/B/S3/Arith/CloitreSquareRootPrimeGapRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev, mathlib/module/Mathlib.Analysis.Real.Sqrt, mathlib/module/Mathlib.Tactic.Linarith]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/CloitreSquareRootPrimeGapRefutation.claim; result=D5/S3/Arith/CloitreSquareRootPrimeGapRefutation.result; claim=D5/S3/Arith/CloitreSquareRootPrimeGapRefutation.claim
   digest: The OEIS A079063 eventual square-root lower bound contradicts prime counting. -/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.CloitreSquareRootPrimeGapRefutation

open Real

noncomputable section

/-- OEIS A079063 (Cloitre, 2003), with the first prime indexed by `1`.
The `sInf` convention assigns zero to an empty set; the witness set is nonempty
for every positive index. -/
def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧
    1 < sqrt (Nat.nth Nat.Prime (n + k - 1)) - sqrt (Nat.nth Nat.Prime (n - 1))}

/-- The weakest quantified reading of OEIS A079063's asserted eventual lower
bound. Its refutation also rules out the proposed `c = 0.4` and a positive
liminf; it does not assert the existence of either proposed limit. -/
def claim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * sqrt n < a n

private theorem sqrt_nth_prime_add_le_of_lt_a (t k : ℕ)
    (hk : 0 < k) (hka : k < a (t + 1)) :
    sqrt (Nat.nth Nat.Prime (t + k)) ≤ sqrt (Nat.nth Nat.Prime t) + 1 := by
  by_contra h
  have hdiff : 1 < sqrt (Nat.nth Nat.Prime (t + k)) -
      sqrt (Nat.nth Nat.Prime t) := by
    push Not at h
    linarith
  have hmem : k ∈ {j : ℕ | 0 < j ∧
      1 < sqrt (Nat.nth Nat.Prime (t + 1 + j - 1)) -
        sqrt (Nat.nth Nat.Prime (t + 1 - 1))} := by
    simp only [Set.mem_ofPred_eq]
    constructor
    · exact hk
    · simpa only [show t + 1 + k - 1 = t + k by omega,
        show t + 1 - 1 = t by omega] using hdiff
  exact (not_lt_of_ge (Nat.sInf_le hmem)) hka

private theorem sqrt_nth_prime_step_of_claim
    (c : ℝ) (N r m t : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * sqrt n < (a n : ℝ))
    (hr : 1 < c * r) (hm : 0 < m) (hN : N ≤ t)
    (ht : (r * m) ^ 2 ≤ t) :
    sqrt (Nat.nth Nat.Prime (t + m)) ≤ sqrt (Nat.nth Nat.Prime t) + 1 := by
  have hroot : (↑(r * m) : ℝ) ≤ sqrt (↑(t + 1) : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (ht.trans (Nat.le_succ t))
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmc : (m : ℝ) < c * (↑(r * m) : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hr hmreal
    simpa only [one_mul, Nat.cast_mul, mul_assoc] using hmul
  have hca : (m : ℝ) < (a (t + 1) : ℝ) :=
    (hmc.trans_le (mul_le_mul_of_nonneg_left hroot hc.le)).trans
      (hclaim (t + 1) (by omega))
  exact sqrt_nth_prime_add_le_of_lt_a t m hm (by exact_mod_cast hca)

end

end D5.S3.Arith.CloitreSquareRootPrimeGapRefutation
