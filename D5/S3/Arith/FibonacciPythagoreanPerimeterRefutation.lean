/- GID: D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciPythagoreanPerimeterRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.claim; result=D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result; claim=D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.claim
   digest: The Fibonacci number at index forty-five is the perimeter of a Pythagorean triangle, which breaks the conjectured characterisation by the multiples of six. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciPythagoreanPerimeterRefutation

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (preregistered before the probe)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- `N` is the sum of the three numbers of a Pythagorean triple, that is, the perimeter of a
Pythagorean triangle. -/
def IsPythPerimeter (N : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a + b + c = N

/-- The conjecture recorded on the sequence of Fibonacci numbers at indices divisible by six:
for every `n ≥ 2` the terms of that sequence are exactly the Fibonacci numbers which are the
sum of the three numbers of a Pythagorean triple. -/
def claim : Prop :=
  ∀ N : ℕ, (∃ k : ℕ, Nat.fib k = N) →
    (IsPythPerimeter N ↔ ∃ n : ℕ, 2 ≤ n ∧ Nat.fib (6 * n) = N)

/-- The conjecture is false. The Fibonacci number at index forty-five is `1134903170`, and
`344191945 ^ 2 + 320443248 ^ 2 = 470267977 ^ 2` with
`344191945 + 320443248 + 470267977 = 1134903170`, so it is the perimeter of a Pythagorean
triangle. It is not a term of the sequence: the Fibonacci numbers at indices divisible by six
skip from `267914296` at index forty-two to `4807526976` at index forty-eight, and `Nat.fib`
is monotone. -/
theorem result : ¬ claim := by
  intro h
  have hfib : Nat.fib 45 = 1134903170 := by decide
  have hperim : IsPythPerimeter 1134903170 :=
    ⟨344191945, 320443248, 470267977, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩
  obtain ⟨n, hn2, hn⟩ := (h 1134903170 ⟨45, hfib⟩).mp hperim
  rcases lt_or_ge n 8 with h8 | h8
  · interval_cases n <;> revert hn <;> decide
  · have hmono : Nat.fib 48 ≤ Nat.fib (6 * n) := Nat.fib_mono (by omega)
    rw [hn] at hmono
    have h48 : Nat.fib 48 = 4807526976 := by decide
    omega

end D5.S3.Arith.FibonacciPythagoreanPerimeterRefutation
