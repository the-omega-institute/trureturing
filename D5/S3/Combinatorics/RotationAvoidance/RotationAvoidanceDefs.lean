/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs
   mirror-E: none(waiver:fixed-rotation-avoidance-wilf-class-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Eğecioğlu, Gaiser and Yin's question on Wilf classes of rotation avoidance in S_4. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDefs

open D5.S3.Combinatorics

/-! Fixed public statement: Eğecioğlu, Gaiser and Yin, *Pattern avoidance in permutations and their
    rotations*, arXiv:2607.20750v1, §6, Open Question 6.1: for every `k ≥ 4`, are there eight
    Wilf-equivalence classes for `S_n^{(k)}(q)` with `q ∈ S_4`?  The `i`-th rotation of
    `p = p_1 ⋯ p_n` is `p_i ⋯ p_n p_1 ⋯ p_{i-1}`, that is `p.rotate (i - 1)`.  Permutations of
    `[n]` are lists in one-line notation; classical containment is `NonnestingDefs.Occurs`. -/

/-- `S_n^{(k)}(q)`: permutations of `[n]` whose first `k` rotations all avoid `q`. -/
def rotationAvoiders (n k : ℕ) (q : List ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ∀ i < k, ¬ Nonnesting.NonnestingDefs.Occurs q (p.rotate i)}

/-- `q` and `s` are Wilf-equivalent for the first `k` rotations: equal counts for every `n ≥ k`. -/
def WilfEquivalent (k : ℕ) (q s : List ℕ) : Prop :=
  ∀ n, k ≤ n → (rotationAvoiders n k q).ncard = (rotationAvoiders n k s).ncard

/-- The complement `x ↦ 5 - x` of a pattern of length four. -/
def complement (q : List ℕ) : List ℕ := q.map fun x => 5 - x

/-- The orbit of a pattern under complement and reverse. -/
def orbit (q : List ℕ) : Set (List ℕ) :=
  {q, complement q, q.reverse, complement q.reverse}

/-- Open Question 6.1, answered affirmatively: for every `k ≥ 4`, two patterns of length four are
    Wilf-equivalent exactly when they lie in the same complement–reverse orbit, so there are eight
    classes. -/
def claim : Prop :=
  ∀ k, 4 ≤ k → ∀ q s : List ℕ, q.Perm [1, 2, 3, 4] → s.Perm [1, 2, 3, 4] →
    (WilfEquivalent k q s ↔ s ∈ orbit q)

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDefs
