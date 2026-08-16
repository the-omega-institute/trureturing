/- GID: D5/S1/Words/Palindromes/PalindromeMiddleParity
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PalindromeMiddleParity
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: An odd-length palindrome has the same sum parity as its middle entry. -/

import Mathlib.Data.List.Palindrome
import Mathlib.Tactic

namespace D5.S1.Words

private theorem odd_palindrome_decomposition {alpha : Type*} {word : List alpha}
    (hpal : List.Palindrome word) (hodd : Odd word.length) :
    exists left middle, word = left ++ [middle] ++ left.reverse := by
  revert hodd
  induction hpal with
  | nil =>
      intro hodd
      simp at hodd
  | singleton x =>
      intro _
      exact ⟨[], x, by simp⟩
  | @cons_concat x inner hinner ih =>
      intro hodd
      have hinnerOdd : Odd inner.length := by
        have houterOdd : Odd (inner.length + 2) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hodd
        exact (Nat.odd_add.mp houterOdd).mpr even_two
      obtain ⟨left, middle, hdecomp⟩ := ih hinnerOdd
      refine ⟨x :: left, middle, ?_⟩
      rw [hdecomp]
      simp [List.append_assoc]

/-- The sum of an odd-length palindrome has the parity of its middle entry. -/
theorem odd_palindrome_sum_mod_two_eq_middle {word : List Nat}
    (hpal : List.Palindrome word) (hodd : Odd word.length) :
    exists left middle,
      word = left ++ [middle] ++ left.reverse ∧ word.sum % 2 = middle % 2 := by
  obtain ⟨left, middle, hdecomp⟩ := odd_palindrome_decomposition hpal hodd
  refine ⟨left, middle, hdecomp, ?_⟩
  rw [hdecomp]
  simp only [List.sum_append, List.sum_cons, List.sum_nil, List.sum_reverse]
  omega

end D5.S1.Words
