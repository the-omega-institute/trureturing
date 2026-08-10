/- GID: D5/S1/Words/GoldenGapPrefix
   generality: I
   mirror-B: D5/B/S1/Words/GoldenGapPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Consecutive finite Fibonacci words form a prefix chain, including golden gap words. -/

import D5.S0.Tower.GoldenGapWord

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

/-- A Fibonacci word two levels later appends the word from two levels earlier. -/
theorem fibWord_append_rec (Q : Nat) :
    fibWord (Q + 2) = fibWord (Q + 1) ++ fibWord Q := by
  induction Q with
  | zero => decide
  | succ Q ih =>
      change
        (fibWord (Q + 2)).flatMap subst =
          (fibWord (Q + 1)).flatMap subst ++ (fibWord Q).flatMap subst
      rw [ih, List.flatMap_append]

/-- Every finite Fibonacci word is a prefix of the next one. -/
theorem fibWord_prefix_succ (Q : Nat) : fibWord Q <+: fibWord (Q + 1) := by
  cases Q with
  | zero => decide
  | succ Q =>
      rw [fibWord_append_rec]
      exact List.prefix_append _ _

/-- Every golden tower gap word from level two onward is a prefix of the next level. -/
theorem goldenGapWord_prefix_succ (Q : Nat) (hQ : 2 <= Q) :
    goldenGapWord Q <+: goldenGapWord (Q + 1) := by
  rw [golden_full_gap_word Q hQ, golden_full_gap_word (Q + 1) (by omega)]
  exact fibWord_prefix_succ Q

example : fibWord 2 = [true, false, true] := by decide
example : fibWord 3 = [true, false, true, true, false] := by decide
example : fibWord 4 = [true, false, true, true, false, true, false, true] := by decide
example : fibWord 5 =
    [true, false, true, true, false, true, false, true, true, false, true, true, false] := by
  decide

example : fibWord 2 <+: fibWord 3 := by decide
example : fibWord 3 <+: fibWord 4 := by decide
example : fibWord 4 <+: fibWord 5 := by decide
example : fibWord 5 <+: fibWord 6 := by decide

end D5.S1.Words
