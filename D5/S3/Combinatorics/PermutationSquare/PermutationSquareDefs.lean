/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareDefs
   mirror-E: none(waiver:fixed-permutation-square-avoidance-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Archer–Bourne's recurrence for 312- and 54321-avoiders whose squares avoid 132. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs

open D5.S3.Combinatorics

/-! Fixed public statement: Archer and Bourne, *Pattern avoidance in compositions and powers of
    permutations*, arXiv:2505.05218v3, §5: for `a_n = a_n(312, 54321 : 132)`,
    `a_n = a_{n-1} + a_{n-2} + a_{n-3} + a_{n-4} + n - 1` for `n ≥ 6`.  Permutations of `[n]`
    are lists in one-line notation; classical containment is `NonnestingDefs.Occurs`. -/

/-- The square `π ∘ π` in one-line notation: its `i`-th entry is `π_{π_i}`. -/
def square (p : List ℕ) : List ℕ := p.map fun x => p.getD (x - 1) 0

/-- Permutations of `[n]` avoiding `312` and `54321` whose square avoids `132`. -/
def avoiders (n : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ Nonnesting.NonnestingDefs.Occurs [3, 1, 2] p ∧
    ¬ Nonnesting.NonnestingDefs.Occurs [5, 4, 3, 2, 1] p ∧
    ¬ Nonnesting.NonnestingDefs.Occurs [1, 3, 2] (square p)}

/-- `a_n(312, 54321 : 132)`. -/
noncomputable def a (n : ℕ) : ℕ := (avoiders n).ncard

/-- The conjectured recurrence `a_n = a_{n-1} + a_{n-2} + a_{n-3} + a_{n-4} + n - 1`, `n ≥ 6`. -/
def claim : Prop :=
  ∀ n : ℕ, 6 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + (n - 1)

end D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs
