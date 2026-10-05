/- GID: D5/S1/Words/Palindromes/FridPrefix/FridNumerals
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/FridNumerals
   mirror-E: none(waiver:exact-fibonacci-recurrence)
   anchors: []
   utility: none
   digest: The Frid prefix lengths are half of a specified Fibonacci weight. -/

/-
proof_shape: content (frid_numeral_twice).
escape_witness: induction on repeated 100 blocks in the actual Fibonacci evaluator.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Words/Powers/WordPower.length_wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower_succ
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Digit.GoldenBase4IntervalMachine
import D5.S1.Words.Powers.WordPower

namespace D5.S1.Words.FridPrefix

open D5.S1.Digit.GoldenBase4IntervalMachine D5.S1.Words.Powers

/-- The Fibonacci-weighted value of the most-significant-first numeral `(100)^(2k-1)101`. -/
def N (k : ℕ) : ℕ :=
  (fibPair (wordPower (2*k-1) [1,0,0] ++ [1,0,1])).1

/-- Each repeated `100` block advances the half-Fibonacci identity by three indices. -/
theorem frid_numeral_twice (m : ℕ) :
    2 * (fibPair (wordPower m [1,0,0] ++ [1,0,1])).1 = Nat.fib (3*m+6) := by
  have hs (m : ℕ) :
      (fibPair (wordPower (m+1) [1,0,0] ++ [1,0,1])).1 =
        Nat.fib (3*m+7) + (fibPair (wordPower m [1,0,0] ++ [1,0,1])).1 := by
    rw [wordPower_succ]
    simp only [List.cons_append, List.nil_append, fibPair,
      List.length_cons, List.length_append, length_wordPower]
    norm_num
    congr 1
    omega
  induction m with
  | zero => norm_num [wordPower, fibPair, Nat.fib]
  | succ m ih =>
    rw [hs]
    have h1 := Nat.fib_add_two (n := 3*m+6)
    have h2 := Nat.fib_add_two (n := 3*m+7)
    norm_num only [Nat.add_assoc] at h1 h2
    rw [show 3*(m+1)+6=3*m+9 by omega]
    omega

end D5.S1.Words.FridPrefix
