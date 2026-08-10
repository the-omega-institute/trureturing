/- GID: D5/S1/Words/GoldenWord
   generality: I
   mirror-B: D5/B/S1/Words/GoldenWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The infinite golden word is the coherent diagonal limit of finite tower words. -/

import D5.S0.Tower.GoldenGapZeckendorf
import D5.S1.Words.GoldenGapPrefix

namespace D5.S1.Words

open D5.S0.Conventions
open D5.S0.Tower.GoldenGapWord
open D5.S0.Tower.GoldenGapZeckendorf

/-- The Fibonacci word at level `Q` has the expected Fibonacci length. -/
theorem fibWord_length (Q : Nat) : (fibWord Q).length = Nat.fib (Q + 2) := by
  rw [fibWord_eq_zeckendorf_word, List.length_ofFn]

/-- The diagonal index `i` occurs in the finite Fibonacci word at level `i`. -/
theorem index_lt_diagonal_level (i : Nat) : i < (fibWord i).length := by
  rw [fibWord_length]
  have h := Nat.le_fib_add_one (i + 2)
  omega

/-- The infinite golden word, read at each index from its canonical diagonal tower level. -/
def goldenWord (i : Nat) : Bool :=
  (fibWord i).get ⟨i, index_lt_diagonal_level i⟩

private theorem fibWord_prefix_of_le {Q R : Nat} (hQR : Q ≤ R) : fibWord Q <+: fibWord R := by
  induction R, hQR using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ R _ ih => exact ih.trans (fibWord_prefix_succ R)

/-- Any finite tower level containing `i` gives the same letter as the diagonal definition. -/
theorem goldenWord_eq_fibWord_get (Q i : Nat) (h : i < (fibWord Q).length) :
    goldenWord i = (fibWord Q).get ⟨i, h⟩ := by
  let R := max i Q
  have hiR : fibWord i <+: fibWord R := fibWord_prefix_of_le (Nat.le_max_left i Q)
  have hQR : fibWord Q <+: fibWord R := fibWord_prefix_of_le (Nat.le_max_right i Q)
  unfold goldenWord
  exact (hiR.getElem (index_lt_diagonal_level i)).trans (hQR.getElem h).symm

/-- The infinite word is the least-Zeckendorf-digit criterion pointwise. -/
theorem goldenWord_eq_zeckendorf_criterion (i : Nat) :
    goldenWord i = if 2 ∈ wdigits i then false else true := by
  simp [goldenWord, fibWord_eq_zeckendorf_word]

/-- A golden word letter is large exactly when the least Zeckendorf digit is absent. -/
theorem goldenWord_char_zeckendorf (i : Nat) : goldenWord i = true ↔ 2 ∉ wdigits i := by
  rw [goldenWord_eq_zeckendorf_criterion]
  simp

/-- The finite Fibonacci word is exactly the corresponding prefix of the infinite word. -/
theorem goldenWord_prefix_eq_fibWord (Q : Nat) :
    List.ofFn (fun i : Fin (fibWord Q).length => goldenWord i) = fibWord Q := by
  apply List.ext_get (by simp)
  intro i _ h
  simpa using goldenWord_eq_fibWord_get Q i h

/-- Every frozen golden gap level containing `i` agrees with the infinite word. -/
theorem goldenWord_eq_goldenGapWord_get (Q i : Nat) (hQ : 2 ≤ Q)
    (h : i < (goldenGapWord Q).length) :
    goldenWord i = (goldenGapWord Q).get ⟨i, h⟩ := by
  have hprefix : goldenGapWord Q <+: fibWord Q := by
    rw [golden_full_gap_word Q hQ]
  have h' : i < (fibWord Q).length := by
    simpa [golden_full_gap_word Q hQ] using h
  exact (goldenWord_eq_fibWord_get Q i h').trans (hprefix.getElem h).symm

/-- The frozen golden gap word is the full finite prefix of the infinite word. -/
theorem goldenWord_prefix_eq_goldenGapWord (Q : Nat) (hQ : 2 ≤ Q) :
    List.ofFn (fun i : Fin (goldenGapWord Q).length => goldenWord i) = goldenGapWord Q := by
  apply List.ext_get (by simp)
  intro i _ h
  simpa using goldenWord_eq_goldenGapWord_get Q i hQ h

example : List.ofFn (fun i : Fin 13 => goldenWord i) = fibWord 5 := by decide

example : List.ofFn (fun i : Fin 13 => goldenWord i) =
    [true, false, true, true, false, true, false, true, true, false, true, true, false] := by
  decide

end D5.S1.Words
