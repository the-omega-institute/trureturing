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

private theorem sqrt_prime_quadratic_step
    (c : ℝ) (N r m : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * sqrt n < (a n : ℝ))
    (hr : 1 < c * r) (hm : 1 ≤ m) (hN : N ≤ (r * m) ^ 2) :
    sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (3 * r * r : ℕ) := by
  let t0 := (r * m) ^ 2
  let L := 3 * r * r
  have hchain (i : ℕ) :
      sqrt (Nat.nth Nat.Prime (t0 + i * m)) ≤
        sqrt (Nat.nth Nat.Prime t0) + i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := sqrt_nth_prime_step_of_claim c N r m (t0 + i * m) hc
        hclaim hr (by omega : 0 < m)
        (by
          calc
            N ≤ t0 := by simpa only [t0] using hN
            _ ≤ t0 + i * m := Nat.le_add_right _ _)
        (by dsimp [t0]; omega)
      calc
        sqrt (Nat.nth Nat.Prime (t0 + (i + 1) * m)) =
            sqrt (Nat.nth Nat.Prime ((t0 + i * m) + m)) := by
              exact congrArg (fun j : ℕ => sqrt (Nat.nth Nat.Prime j))
                (by simp only [Nat.add_mul, one_mul]; omega :
                  t0 + (i + 1) * m = (t0 + i * m) + m)
        _ ≤ sqrt (Nat.nth Nat.Prime (t0 + i * m)) + 1 := hstep
        _ ≤ sqrt (Nat.nth Nat.Prime t0) + (↑(i + 1) : ℝ) := by
          push_cast
          linarith [ih]
  have hR : r * r ≤ (r * r) * m := by
    calc
      r * r = (r * r) * 1 := by omega
      _ ≤ (r * r) * m := Nat.mul_le_mul_left _ hm
  have hindex : (r * (m + 1)) ^ 2 ≤ t0 + L * m := by
    dsimp [t0, L]
    nlinarith [hR]
  have hp := (Nat.nth_monotone Nat.infinite_setOfPred_prime) hindex
  have hs : sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      sqrt (Nat.nth Nat.Prime (t0 + L * m)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hp)
  exact hs.trans (by simpa only [t0, L] using hchain L)

private theorem sqrt_prime_quadratic_linear
    (c : ℝ) (N r : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * sqrt n < (a n : ℝ))
    (hr : 1 < c * r) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, N + 1 ≤ m →
      sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) ≤ B * m := by
  have hr1 : 1 ≤ r := by
    by_contra h
    have hzero : r = 0 := by omega
    simp [hzero] at hr
    linarith
  let m0 := N + 1
  let L := 3 * r * r
  let B : ℝ := sqrt (Nat.nth Nat.Prime ((r * m0) ^ 2)) + L
  have hL : (0 : ℝ) < L := by
    dsimp [L]
    have hrpos : 0 < r := by omega
    positivity
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos (sqrt_nonneg _) hL
  refine ⟨B, hB, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hm0 : (1 : ℝ) ≤ m0 := by
      change (1 : ℝ) ≤ (N + 1 : ℕ)
      exact_mod_cast (by omega : 1 ≤ N + 1)
    have hB0 : 0 ≤ B := hB.le
    dsimp [B]
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hm0)]
  | succ m hm ih =>
    have hN : N ≤ (r * m) ^ 2 := by
      have hNm : N ≤ m := by omega
      have hrm : m ≤ r * m := by
        calc
          m = 1 * m := by omega
          _ ≤ r * m := Nat.mul_le_mul_right m hr1
      have hx : 1 ≤ r * m := by omega
      have hpow : r * m ≤ (r * m) ^ 2 := by
        nlinarith [Nat.mul_le_mul_left (r * m) hx]
      exact hNm.trans (hrm.trans hpow)
    have hstep := sqrt_prime_quadratic_step c N r m hc hclaim hr (by omega) hN
    have hLB : (L : ℝ) ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_left (sqrt_nonneg _)
    calc
      sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
          sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (L : ℝ) := by
            simpa only [L] using hstep
      _ ≤ B * (↑(m + 1) : ℝ) := by push_cast; nlinarith [ih, hLB]

end

end D5.S3.Arith.CloitreSquareRootPrimeGapRefutation
