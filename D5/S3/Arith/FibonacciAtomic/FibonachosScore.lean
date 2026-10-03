/- GID: D5/S3/Arith/FibonacciAtomic/FibonachosScore
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FibonachosScore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Fibonachos ties occur at four heaps and large-heap majority follows Fibonacci block parity. -/

import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FibonachosScore

/-- Scores of the player to move and the other player. Each positive heap
uses the next Fibonacci number, resetting its index to one when it exceeds
the heap. The scores swap at every move, exactly as in OEIS A382814's
program. Index zero is treated as a reset; reachable indices are positive.
The remaining heap decreases by at least one at each move. -/
def play (n i : ℕ) : ℕ × ℕ :=
  if hn : n = 0 then (0, 0) else
    let j := if 0 < Nat.fib i ∧ Nat.fib i ≤ n then i else 1
    let q := play (n - Nat.fib j) (j + 1)
    (Nat.fib j + q.2, q.1)
termination_by n
 decreasing_by
  have hp : 0 < Nat.fib (if 0 < Nat.fib i ∧ Nat.fib i ≤ n then i else 1) := by
    split
    · assumption
    · simp
  exact Nat.sub_lt (Nat.pos_of_ne_zero hn) hp

/-- Number collected by the first player, with the initial index one. -/
def a (n : ℕ) : ℕ := (play n 1).1

/-- Signed advantage of the player to move. -/
def advantage (n i : ℕ) : ℤ := (play n i).1 - (play n i).2

/-- Kagey's tie and large-heap majority conjectures. The interval endpoints
use additive inequalities to express the original natural-number endpoints
without truncated subtraction. -/
theorem result :
    (∀ n : ℕ, 1 ≤ n → (2 * a n = n ↔ n ∈ ({2, 8, 10, 32} : Finset ℕ))) ∧
    (∀ n : ℕ, 32 < n → (n < 2 * a n ↔
      ∃ m : ℕ, Odd m ∧ Nat.fib m ≤ n + 1 ∧ n + 2 ≤ Nat.fib (m + 1))) := by
  sorry

end D5.S3.Arith.FibonacciAtomic.FibonachosScore
