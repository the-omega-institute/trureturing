/- GID: D5/S1/Words/Palindromes/PalindromeBalance
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PalindromeBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An even-length integer palindrome has zero alternating sum. -/

import Mathlib.Data.Nat.Digits.Div

/- Library-search audit trail (2026-08-17):
   * Pinned mathlib supplies `List.alternatingSum_reverse`, the exact reversal law used below.
   * `Nat.eleven_dvd_of_palindrome` uses the same argument for decimal digits, but mathlib has no
     reusable theorem stating the general integer-list conclusion.
-/

namespace D5.S1.Words

/-- Every even-length palindromic integer list has vanishing alternating sum. -/
theorem even_palindrome_alternating_sum_eq_zero {word : List ℤ}
    (hpal : List.Palindrome word) (heven : Even word.length) :
    word.alternatingSum = 0 := by
  have hreverse := word.alternatingSum_reverse
  have hodd : Odd (word.length + 1) := heven.add_one
  have hsign : (-1 : ℤ) ^ (word.length + 1) = -1 :=
    Odd.neg_one_pow (α := ℤ) hodd
  rw [hpal.reverse_eq, hsign, neg_one_zsmul] at hreverse
  exact eq_zero_of_neg_eq hreverse.symm

#print axioms even_palindrome_alternating_sum_eq_zero

end D5.S1.Words
