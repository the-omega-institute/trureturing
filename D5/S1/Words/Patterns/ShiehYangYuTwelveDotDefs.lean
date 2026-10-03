/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDotDefs
   mirror-E: none(waiver:fixed-twelve-dot-machine-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: The 12-dot machine of Shieh, Yang and Yu and their central binomial conjecture. -/

import D5.S1.Words.Patterns.ShiehYangYuMachineConvergence
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs

open D5.S1.Words.Patterns

/-! Fixed public statement: Shieh, Yang and Yu, *Stack-Sorting with Dotted-Pattern-Avoiding
    Stacks*, arXiv:2411.11914v2, §6, Conjecture 6.1.  The source proves (Proposition 3.1) that
    the stack avoiding the dotted pattern `12̇` reverses each peak run; that closed form is
    used here as the definition of `s₁₂`.  West's map is `ShiehYangYuMachineConvergence.s`. -/

/-- Peak runs: each run starts at a left-to-right maximum and continues until the next one. -/
def peakRuns : List ℕ → List (List ℕ)
  | [] => []
  | v :: tail =>
      (v :: tail.takeWhile (fun x => decide (x ≤ v))) ::
        peakRuns (tail.dropWhile (fun x => decide (x ≤ v)))
termination_by w => w.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- `s₁₂̇`: reverse each peak run (Proposition 3.1 of the source). -/
def s12 (w : List ℕ) : List ℕ := (peakRuns w).map List.reverse |>.flatten

/-- Machine-sortable permutations of `[n]`: `s (s₁₂̇ π)` is the identity. -/
def sortable (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ShiehYangYuMachineConvergence.s (s12 p) = List.range' 1 n}

/-- Conjecture 6.1: the `12̇`-machine sorts exactly `binom(2n-2, n-1)` permutations of `[n]`. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → (sortable n).ncard = (2 * n - 2).choose (n - 1)

end D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
