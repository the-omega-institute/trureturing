/- GID: D5/S0/Tower/GoldenGapZeckendorf
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenGapZeckendorf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Fibonacci gap word is read directly from the least Zeckendorf digit. -/

import D5.S0.Conventions.WDigits
import D5.S0.Tower.GoldenGapWord

namespace D5.S0.Tower.GoldenGapZeckendorf

open D5.S0.Conventions
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGapWord

private def zeckendorfCriterion (Q : Nat) : List Bool :=
  List.ofFn fun i : Fin (Nat.fib (Q + 2)) =>
    if 2 ∈ wdigits i.1 then false else true

private theorem wdigits_fib_add (Q : Nat) (j : Fin (Nat.fib (Q + 2))) :
    wdigits (Nat.fib (Q + 3) + j.1) = (Q + 3) :: wdigits j.1 := by
  symm
  apply wdigits_unique
  · rw [List.IsZeckendorfRep, List.cons_append]
    apply (wdigits_isCanonical j.1).cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := (goldenNameEquiv Q j).2 k hk_digits
      omega
    · omega
  · change Nat.fib (Q + 3) + ((wdigits j.1).map Nat.fib).sum =
      Nat.fib (Q + 3) + j.1
    rw [decode_wdigits]

private theorem zeckendorfCriterion_add_two (Q : Nat) :
    zeckendorfCriterion (Q + 2) =
      zeckendorfCriterion (Q + 1) ++ zeckendorfCriterion Q := by
  have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
    rw [Nat.fib_add_two (n := Q + 2), add_comm]
  unfold zeckendorfCriterion
  rw [List.ofFn_congr hrec]
  rw [← List.ofFn_fin_append]
  rw [List.ofFn_inj]
  funext i
  refine Fin.addCases (m := Nat.fib (Q + 3)) (n := Nat.fib (Q + 2)) ?_ ?_ i
  · intro j
    rw [Fin.append_left]
    have hvalue :
        (Fin.cast hrec.symm (Fin.castAdd (Nat.fib (Q + 2)) j)).1 = j.1 := rfl
    rw [hvalue]
  · intro j
    rw [Fin.append_right]
    have hvalue :
        (Fin.cast hrec.symm (Fin.natAdd (Nat.fib (Q + 3)) j)).1 =
          Nat.fib (Q + 3) + j.1 := rfl
    rw [hvalue, wdigits_fib_add]
    simp

private theorem zeckendorfCriterion_zero : zeckendorfCriterion 0 = [true] := by
  have hzero : wdigits 0 = [] := by
    symm
    apply wdigits_unique
    · exact List.IsZeckendorfRep_nil
    · rfl
  rw [zeckendorfCriterion]
  change [if 2 ∈ wdigits 0 then false else true] = [true]
  rw [hzero]
  simp

private theorem zeckendorfCriterion_one : zeckendorfCriterion 1 = [true, false] := by
  have hzero : wdigits 0 = [] := by
    symm
    apply wdigits_unique
    · exact List.IsZeckendorfRep_nil
    · rfl
  have hone : wdigits 1 = [2] := by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  rw [zeckendorfCriterion]
  change
    [if 2 ∈ wdigits 0 then false else true,
      if 2 ∈ wdigits 1 then false else true] = [true, false]
  rw [hzero, hone]
  simp

private theorem fibWord_add_two (Q : Nat) :
    fibWord (Q + 2) = fibWord (Q + 1) ++ fibWord Q := by
  induction Q with
  | zero => decide
  | succ Q ih =>
      change
        (fibWord (Q + 2)).flatMap subst =
          (fibWord (Q + 1)).flatMap subst ++ (fibWord Q).flatMap subst
      rw [ih, List.flatMap_append]

private theorem fibWord_eq_zeckendorfCriterion : ∀ Q : Nat,
    fibWord Q = zeckendorfCriterion Q := by
  apply Nat.twoStepInduction
  · simpa [fibWord] using zeckendorfCriterion_zero.symm
  · simpa [fibWord, subst] using zeckendorfCriterion_one.symm
  · intro Q hQ hQ1
    rw [fibWord_add_two, zeckendorfCriterion_add_two, hQ1, hQ]

/-- The Fibonacci word's large letter is exactly absence of the least Zeckendorf digit. -/
theorem fibWord_eq_zeckendorf_word (Q : Nat) :
    fibWord Q = List.ofFn (fun i : Fin (Nat.fib (Q + 2)) =>
      if 2 ∈ wdigits i.1 then false else true) := by
  simpa [zeckendorfCriterion] using fibWord_eq_zeckendorfCriterion Q

/-- The frozen tower gap word has the same least-Zeckendorf-digit criterion. -/
theorem goldenGapWord_eq_zeckendorf_word (Q : Nat) (hQ : 2 ≤ Q) :
    goldenGapWord Q = List.ofFn (fun i : Fin (Nat.fib (Q + 2)) =>
      if 2 ∈ wdigits i.1 then false else true) := by
  rw [golden_full_gap_word Q hQ, fibWord_eq_zeckendorf_word]

end D5.S0.Tower.GoldenGapZeckendorf
