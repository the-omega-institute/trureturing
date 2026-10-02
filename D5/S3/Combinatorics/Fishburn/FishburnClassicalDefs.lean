/- GID: D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnClassicalDefs
   mirror-E: none(waiver:fixed-fishburn-versus-classical-wilf-statement-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Classical pattern classes and three of Egge's Fishburn-versus-classical equalities. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs

open D5.S3.Combinatorics

/-! Fixed public statements: Egge, *Pattern-Avoiding Fishburn Permutations and Ascent
    Sequences*, arXiv:2208.01484v1, §10, Conjectures 10.9, 10.11 and 10.12.  `F_n(B)` is
    `FishburnDefs.avoiders`; `S_n(B)` below drops the Fishburn condition. -/

/-- `S_n(B)`: permutations of `[n]` avoiding every classical pattern of `B`. -/
def classicalAvoiders (n : ℕ) (B : List (List ℕ)) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ∀ σ ∈ B, ¬ Nonnesting.NonnestingDefs.Occurs σ p}

/-- Conjecture 10.9: `|F_n(2143, 3124)| = |S_n(231, 4123)|` for `n ≥ 1`. -/
def claim109 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (FishburnDefs.avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
    (classicalAvoiders n [[2, 3, 1], [4, 1, 2, 3]]).ncard

/-- Conjecture 10.11: `|F_n(1243, 2134)| = |S_n(123, 3241)|` for `n ≥ 0`. -/
def claim1011 : Prop :=
  ∀ n : ℕ, (FishburnDefs.avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]]).ncard =
    (classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]]).ncard

/-- Conjecture 10.12: `|F_n(1243, 3124)| = |S_n(231, 4123)|` for `n ≥ 0`. -/
def claim1012 : Prop :=
  ∀ n : ℕ, (FishburnDefs.avoiders n [[1, 2, 4, 3], [3, 1, 2, 4]]).ncard =
    (classicalAvoiders n [[2, 3, 1], [4, 1, 2, 3]]).ncard

end D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs
