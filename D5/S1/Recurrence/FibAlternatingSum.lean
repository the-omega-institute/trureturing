/- GID: D5/S1/Recurrence/FibAlternatingSum
   generality: G
   mirror-B: D5/B/S1/Recurrence/FibAlternatingSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The parity-descending Fibonacci sum equals the next source-indexed Fibonacci number minus one. -/

import Mathlib

namespace D5.S1.Recurrence.FibAlternatingSum

/-- The source convention `F₀ = F₁ = 1`, so `F k = fib (k + 1)`. -/
def srcFib (k : Nat) : Int := Nat.fib (k + 1)

/-- `F_k + F_{k-2} + ...`; the zero case is empty because the source lemma starts at `k = 1`. -/
def alternatingFibSum : Nat -> Int
  | 0 => 0
  | 1 => srcFib 1
  | k + 2 => srcFib (k + 2) + alternatingFibSum k

theorem alternating_fibonacci_sum (k : Nat) :
    alternatingFibSum k = srcFib (k + 1) - 1 := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [alternatingFibSum, srcFib, Nat.fib]
  | one => norm_num [alternatingFibSum, srcFib, Nat.fib]
  | more k ih0 ih1 =>
      rw [alternatingFibSum, ih0]
      change (Nat.fib (k + 3) : Int) + ((Nat.fib (k + 2) : Int) - 1) =
        (Nat.fib (k + 4) : Int) - 1
      have hFib : (Nat.fib (k + 4) : Int) =
          (Nat.fib (k + 2) : Int) + Nat.fib (k + 3) := by
        exact_mod_cast Nat.fib_add_two (n := k + 2)
      rw [hFib]
      ring

end D5.S1.Recurrence.FibAlternatingSum
