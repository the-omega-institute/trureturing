/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs
   mirror-E: none(waiver:fixed-skew-merged-rook-count-statement-definition)
   anchors: []
   utility: none
   digest: Lewis and Won's conjecture that skew-merged permutations have one or two placements. -/

import D5.S3.Combinatorics.CrosswordPermutationGridRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs

open D5.S3.Combinatorics.CrosswordRookCounts (rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)

/-! Fixed public statement: Lewis and Won, *Non-attacking rook placements on crossword grids*,
    arXiv:2609.03081v1, §3.3, Conjecture 3.9: a permutation `w ∈ S_n` is skew-merged if and only
    if `Grid(w)` admits exactly one or two rook placements.  `Grid(w)` is `permGrid w` (black cells
    `(i, w i)`), and its number of complete rook placements is `rookCount`. -/

/-- `w` is skew-merged: its entries split into an increasing and a decreasing subsequence. -/
def SkewMerged {n : ℕ} (w : Equiv.Perm (Fin n)) : Prop :=
  ∃ S : Finset (Fin n),
    (∀ i ∈ S, ∀ j ∈ S, i < j → w i < w j) ∧ (∀ i ∉ S, ∀ j ∉ S, i < j → w j < w i)

/-- Conjecture 3.9. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ w : Equiv.Perm (Fin n),
    (rookCount (permGrid w) = 1 ∨ rookCount (permGrid w) = 2) ↔ SkewMerged w

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs
