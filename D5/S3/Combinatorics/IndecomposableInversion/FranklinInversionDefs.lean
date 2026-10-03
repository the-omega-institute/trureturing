/- GID: D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs
   mirror-E: none(waiver:fixed-indecomposable-inversion-count-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Franklín's printed count of indecomposable 321- and 1342-avoiders by inversions. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionDefs

open D5.S3.Combinatorics

/-! Fixed public statement: Franklín, *Pattern avoiding permutations enumerated by inversions*,
    arXiv:2410.07467v4, §1 (pp. 2–3): `I_k(321, 1342)` is conjectured to have `k(k+1)/2 + 1`
    elements, where `I_k` is the set of direct-sum indecomposable permutations, of any length,
    with exactly `k` inversions.  Permutations of `[n]` are lists in one-line notation; classical
    containment is `NonnestingDefs.Occurs`. -/

/-- The number of inversions: index pairs `i < j` with `p_i > p_j`. -/
def inv (p : List ℕ) : ℕ :=
  ((List.range p.length).map fun i =>
    ((List.range p.length).filter fun j => decide (i < j ∧ p.getD j 0 < p.getD i 0)).length).sum

/-- A permutation of `[n]` is indecomposable when no proper nonempty prefix is a permutation of
    an initial segment `[i]`. -/
def Indecomposable (p : List ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < p.length → ¬ (p.take i).Perm (List.range' 1 i)

/-- `I_k(321, 1342)`: nonempty indecomposable permutations with `k` inversions avoiding `321`
    and `1342`. -/
def avoiders (k : ℕ) : Set (List ℕ) :=
  {p | ∃ n, 1 ≤ n ∧ p.Perm (List.range' 1 n) ∧ Indecomposable p ∧ inv p = k ∧
    ¬ Nonnesting.NonnestingDefs.Occurs [3, 2, 1] p ∧
    ¬ Nonnesting.NonnestingDefs.Occurs [1, 3, 4, 2] p}

/-- The printed conjecture: `|I_k(321, 1342)| = k(k+1)/2 + 1` for every `k`. -/
def claim : Prop := ∀ k : ℕ, (avoiders k).ncard = k * (k + 1) / 2 + 1

end D5.S3.Combinatorics.IndecomposableInversion.FranklinInversionDefs
