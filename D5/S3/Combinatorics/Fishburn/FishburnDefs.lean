/- GID: D5/S3/Combinatorics/Fishburn/FishburnDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnDefs
   mirror-E: none(waiver:fixed-pattern-avoiding-fishburn-permutation-definitions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Fishburn permutations avoiding pairs of classical patterns and two of Egge's counts. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnDefs

open D5.S3.Combinatorics

/-! Fixed public statements: Egge, *Pattern-Avoiding Fishburn Permutations and Ascent
    Sequences*, arXiv:2208.01484v1, §10, Conjectures 10.4 and 10.5.  Permutations of `[n]` are
    lists in one-line notation; positions are numbered from 0 in Lean.  Classical containment
    is `NonnestingDefs.Occurs`, which for a permutation pattern is order-isomorphic
    containment. -/

/-- `p` is Fishburn: no `i` and `j > i + 1` with `p_i = p_j + 1 < p_{i+1}`. -/
def IsFishburn (p : List ℕ) : Prop :=
  ∀ i j, i + 1 < j → j < p.length →
    ¬ (p.getD i 0 = p.getD j 0 + 1 ∧ p.getD j 0 + 1 < p.getD (i + 1) 0)

/-- `F_n(B)`: Fishburn permutations of `[n]` avoiding every pattern of `B`. -/
def avoiders (n : ℕ) (B : List (List ℕ)) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ IsFishburn p ∧
    ∀ σ ∈ B, ¬ Nonnesting.NonnestingDefs.Occurs σ p}

/-- Conjecture 10.4: `|F_n(1324,2143)| = |F_n(1423,2143)| = |F_n(1423,3124)| = (n-1)2^{n-2}+1`
    for `n ≥ 1` (natural-number subtraction gives the value `1` at `n = 1`). -/
def claim104 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (avoiders n [[1, 3, 2, 4], [2, 1, 4, 3]]).ncard = (n - 1) * 2 ^ (n - 2) + 1 ∧
    (avoiders n [[1, 4, 2, 3], [2, 1, 4, 3]]).ncard = (n - 1) * 2 ^ (n - 2) + 1 ∧
    (avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]).ncard = (n - 1) * 2 ^ (n - 2) + 1

/-- Conjecture 10.5: `|F_n(1324,1423)| = |F_n(1324,3124)| = F_{2n-2}` for `n ≥ 1`, where the
    source indexes the Fibonacci numbers by `F_0 = F_1 = 1`; in Mathlib's indexing this is
    `Nat.fib (2 * n - 1)`. -/
def claim105 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]]).ncard = Nat.fib (2 * n - 1) ∧
    (avoiders n [[1, 3, 2, 4], [3, 1, 2, 4]]).ncard = Nat.fib (2 * n - 1)

end D5.S3.Combinatorics.Fishburn.FishburnDefs
