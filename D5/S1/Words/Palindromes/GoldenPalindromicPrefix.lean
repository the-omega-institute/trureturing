/- GID: D5/S1/Words/Palindromes/GoldenPalindromicPrefix
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:qualitative-palindrome-decomposition-is-formal-only)
   anchors: []
   digest: Fibonacci words split into a palindromic core and a parity-exact two-letter tail. -/

import D5.S1.Words.GoldenWord
import Mathlib.Data.List.Palindrome

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

/-- The final two letters of a positive-level Fibonacci word, selected exactly by parity. -/
def fibTail (Q : Nat) : List Bool :=
  if Even Q then [false, true] else [true, false]

/-- The Fibonacci word with its final two letters removed. -/
def fibPalCore (Q : Nat) : List Bool :=
  (fibWord Q).take ((fibWord Q).length - 2)

private theorem fibTail_length (Q : Nat) : (fibTail Q).length = 2 := by
  unfold fibTail
  split <;> rfl

private theorem fibTail_add_two (Q : Nat) : fibTail (Q + 2) = fibTail Q := by
  by_cases hQ : Even Q <;> simp [fibTail, Nat.even_add, hQ]

private theorem fibTail_succ_reverse (Q : Nat) : (fibTail (Q + 1)).reverse = fibTail Q := by
  by_cases hQ : Even Q <;> simp [fibTail, Nat.even_add_one, hQ]

private theorem take_prefix_of_tail_two {word pre tail : List Bool}
    (hword : word = pre ++ tail) (htail : tail.length = 2) :
    word.take (word.length - 2) = pre := by
  subst word
  simp [htail]

private theorem fibWord_decompose_add_two (Q : Nat)
    (hQ : fibWord Q = fibPalCore Q ++ fibTail Q)
    (hQ1 : fibWord (Q + 1) = fibPalCore (Q + 1) ++ fibTail (Q + 1)) :
    fibWord (Q + 2) = fibPalCore (Q + 2) ++ fibTail (Q + 2) := by
  have hword : fibWord (Q + 2) =
      (fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q) ++ fibTail Q := by
    rw [fibWord_append_rec, hQ1, hQ]
    simp only [List.append_assoc]
  have hcore : fibPalCore (Q + 2) =
      fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q := by
    unfold fibPalCore
    exact take_prefix_of_tail_two hword (fibTail_length Q)
  calc
    fibWord (Q + 2) =
        (fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q) ++ fibTail Q := hword
    _ = fibPalCore (Q + 2) ++ fibTail (Q + 2) := by rw [hcore, fibTail_add_two]

/-- Every positive-level Fibonacci word is its palindromic candidate core plus its exact tail. -/
theorem fibWord_eq_fibPalCore_append_fibTail (Q : Nat) (hQ : 1 <= Q) :
    fibWord Q = fibPalCore Q ++ fibTail Q := by
  have hpairs : forall R, 1 <= R ->
      fibWord R = fibPalCore R ++ fibTail R ∧
        fibWord (R + 1) = fibPalCore (R + 1) ++ fibTail (R + 1) := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base => exact ⟨by decide, by decide⟩
    | succ R hR ih => exact ⟨ih.2, fibWord_decompose_add_two R ih.1 ih.2⟩
  exact (hpairs Q hQ).1

private theorem fibPalCore_add_two (Q : Nat) (hQ : 1 <= Q) :
    fibPalCore (Q + 2) = fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q := by
  have hword : fibWord (Q + 2) =
      (fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q) ++ fibTail Q := by
    rw [fibWord_append_rec, fibWord_eq_fibPalCore_append_fibTail Q hQ,
      fibWord_eq_fibPalCore_append_fibTail (Q + 1) (by omega)]
    simp only [List.append_assoc]
  unfold fibPalCore
  exact take_prefix_of_tail_two hword (fibTail_length Q)

private theorem fibPalCore_central_commute (Q : Nat) (hQ : 1 <= Q) :
    fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q =
      fibPalCore Q ++ fibTail Q ++ fibPalCore (Q + 1) := by
  induction Q, hQ using Nat.le_induction with
  | base => decide
  | succ Q hQ ih =>
      have hnext : fibPalCore (Q + 2) ++ fibTail (Q + 2) ++ fibPalCore (Q + 1) =
          fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore (Q + 2) := by
        calc
          fibPalCore (Q + 2) ++ fibTail (Q + 2) ++ fibPalCore (Q + 1) =
              (fibPalCore (Q + 1) ++ fibTail (Q + 1)) ++
                (fibPalCore Q ++ fibTail Q ++ fibPalCore (Q + 1)) := by
            rw [fibPalCore_add_two Q hQ, fibTail_add_two]
            simp only [List.append_assoc]
          _ = (fibPalCore (Q + 1) ++ fibTail (Q + 1)) ++
                (fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore Q) := by
            rw [ih.symm]
          _ = fibPalCore (Q + 1) ++ fibTail (Q + 1) ++ fibPalCore (Q + 2) := by
            rw [fibPalCore_add_two Q hQ]
      simpa [Nat.add_assoc] using hnext

private theorem fibPalCore_palindrome_add_two (Q : Nat) (hQ : 1 <= Q)
    (hpalQ : List.Palindrome (fibPalCore Q))
    (hpalQ1 : List.Palindrome (fibPalCore (Q + 1))) :
    List.Palindrome (fibPalCore (Q + 2)) := by
  apply List.Palindrome.of_reverse_eq
  rw [fibPalCore_add_two Q hQ]
  simp only [List.reverse_append, hpalQ.reverse_eq, hpalQ1.reverse_eq,
    fibTail_succ_reverse]
  simpa only [List.append_assoc] using (fibPalCore_central_commute Q hQ).symm

/-- The core left after deleting the exact two-letter tail is a palindrome. -/
theorem fibPalCore_palindrome (Q : Nat) (hQ : 1 <= Q) : List.Palindrome (fibPalCore Q) := by
  have hpairs : forall R, 1 <= R ->
      List.Palindrome (fibPalCore R) ∧ List.Palindrome (fibPalCore (R + 1)) := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base => exact ⟨by decide, by decide⟩
    | succ R hR ih => exact ⟨ih.2, fibPalCore_palindrome_add_two R hR ih.1 ih.2⟩
  exact (hpairs Q hQ).1

/-- The palindromic core has the Fibonacci-word length minus its exact two-letter tail. -/
theorem fibPalCore_length (Q : Nat) (hQ : 1 <= Q) :
    (fibPalCore Q).length = Nat.fib (Q + 2) - 2 := by
  have hlength := congrArg List.length (fibWord_eq_fibPalCore_append_fibTail Q hQ)
  simp only [fibWord_length, List.length_append, fibTail_length] at hlength
  omega

/-- The golden-word prefix whose length is two below a Fibonacci length is palindromic. -/
theorem goldenWord_palindromic_prefix (Q : Nat) (hQ : 1 <= Q) :
    List.Palindrome
      (List.ofFn (fun i : Fin (Nat.fib (Q + 2) - 2) => goldenWord i)) := by
  rw [← fibPalCore_length Q hQ]
  have hprefix :
      List.ofFn (fun i : Fin (fibPalCore Q).length => goldenWord i) = fibPalCore Q := by
    apply List.ext_get (by simp)
    intro i _ hi
    have hcore_le : (fibPalCore Q).length <= (fibWord Q).length := by
      simp [fibPalCore]
    have hword : i < (fibWord Q).length := by omega
    simpa [fibPalCore] using goldenWord_eq_fibWord_get Q i hword
  rw [hprefix]
  exact fibPalCore_palindrome Q hQ

example : fibWord 1 = fibPalCore 1 ++ fibTail 1 ∧ List.Palindrome (fibPalCore 1) := by decide
example : fibWord 2 = fibPalCore 2 ++ fibTail 2 ∧ List.Palindrome (fibPalCore 2) := by decide
example : fibWord 3 = fibPalCore 3 ++ fibTail 3 ∧ List.Palindrome (fibPalCore 3) := by decide
example : fibWord 4 = fibPalCore 4 ++ fibTail 4 ∧ List.Palindrome (fibPalCore 4) := by decide
example : fibWord 5 = fibPalCore 5 ++ fibTail 5 ∧ List.Palindrome (fibPalCore 5) := by decide

#print axioms fibWord_eq_fibPalCore_append_fibTail
#print axioms fibPalCore_palindrome
#print axioms fibPalCore_length
#print axioms goldenWord_palindromic_prefix

end D5.S1.Words
