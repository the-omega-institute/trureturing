/- GID: D5/S1/Recurrence/GoldenPartition
   generality: I
   mirror-B: D5/B/S1/Recurrence/GoldenPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci-weighted inverse golden powers partition one exactly. -/

import D5.S1.Scale.Fibonacci
import D5.S1.Scale.Embedding

namespace D5.S1.Recurrence.GoldenPartition

open D5.S1.Scale

/-- The two consecutive inverse golden powers, weighted by consecutive
Fibonacci numbers, form an exact partition of one. -/
theorem fibonacci_golden_partition (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) * Real.goldenRatio ^ (-n : ℤ) +
      (Nat.fib n : ℝ) * Real.goldenRatio ^ (-(n + 1 : ℕ) : ℤ) = 1 := by
  have hpow : Real.goldenRatio ^ (n + 1) =
      (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) * Real.goldenRatio := by
    have h := congrArg embedding (golden_phi_pow_eq_fib_pair n)
    rw [map_pow, embedding_phi] at h
    simpa using h
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  generalize hx : Real.goldenRatio = x at hpow ⊢
  have hx0 : x ≠ 0 := by
    rw [← hx]
    exact Real.goldenRatio_ne_zero
  field_simp [hx0]
  calc
    (Nat.fib (n + 1) : ℝ) * x ^ (n + 1) + x ^ n * (Nat.fib n : ℝ) =
        x ^ n * ((Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) * x) := by
          rw [pow_succ]
          ring
    _ = x ^ n * x ^ (n + 1) := by rw [← hpow]

end D5.S1.Recurrence.GoldenPartition
