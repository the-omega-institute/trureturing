/- GID: D5/S3/Combinatorics/ArrowWilfDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfDefs
   mirror-E: none(waiver:fixed-public-definitions-for-arrow-pattern-avoidance)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Arrow-pattern containment and avoidance are defined for one-line natural-number permutations. -/

import Mathlib.Data.Set.Card
import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfDefs

/-! Fixed public statement: Zhou–Yu, arXiv:2609.29392v1, §7 open problem:
    the arrow patterns (12; 3 → 3) and (23; 1 → 1) are arrow-Wilf-equivalent.
    Permutations of `[n]` are lists in one-line notation, positions numbered from 0 in Lean. -/

/-- `p.getD i 0` is a left-to-right maximum: it exceeds every earlier entry. -/
def IsLtrMax (p : List ℕ) (i : ℕ) : Prop := ∀ j < i, p.getD j 0 < p.getD i 0

instance (p : List ℕ) (i : ℕ) : Decidable (IsLtrMax p i) := by
  unfold IsLtrMax; infer_instance

/-- `π̂ = θ⁻¹(π)` (Foata's first fundamental transformation, inverted): cut `π` before each
    left-to-right maximum; each block is a cycle, every entry maps to the next entry of its block and the
    last entry of a block maps to the block's first entry. -/
def hat (p : List ℕ) (x : ℕ) : ℕ :=
  let i := p.idxOf x
  if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1) then p.getD (i + 1) 0
  else p.getD (Nat.findGreatest (IsLtrMax p) i) 0

/-- Containment of the arrow pattern `(ν; H)` of size `k` (§1): selected values `x 1 < ⋯ < x k` of `π`
    such that `x_{ν_1} ⋯ x_{ν_m}` occurs as a subsequence of `π` and `π̂(x_b) = x_c` for every arrow
    `b → c` in `H`. -/
def Contains (ν : List ℕ) (H : List (ℕ × ℕ)) (k : ℕ) (p : List ℕ) : Prop :=
  ∃ x : ℕ → ℕ,
    (∀ i, 1 ≤ i → i < k → x i < x (i + 1)) ∧
    (∀ i, 1 ≤ i → i ≤ k → x i ∈ p) ∧
    (ν.map x).Sublist p ∧
    ∀ bc ∈ H, hat p (x bc.1) = x bc.2

/-- `S_n(α)`: permutations of `[n]` avoiding the arrow pattern `α = (ν; H)` of size `k`. -/
def avoiders (n : ℕ) (ν : List ℕ) (H : List (ℕ × ℕ)) (k : ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ Contains ν H k p}

/-- The §7 open problem: `(12; 3 → 3) ∼ (23; 1 → 1)`, i.e. `|S_n(12; 3 → 3)| = |S_n(23; 1 → 1)|`
    for all `n ≥ 1`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (avoiders n [1, 2] [(3, 3)] 3).ncard = (avoiders n [2, 3] [(1, 1)] 3).ncard

end D5.S3.Combinatorics.ArrowWilfDefs
