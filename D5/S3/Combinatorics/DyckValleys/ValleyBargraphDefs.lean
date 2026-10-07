/- GID: D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DyckValleys/ValleyBargraphDefs
   mirror-E: none(waiver:mu-welker-conjecture-three-nine-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Mu and Welker's Conjecture 3.9 identifying valley-maximal Dyck paths with bargraphs (OEIS A271942). -/

import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraphDefs

/-! Fixed public statement: L. Mu and V. Welker, *Simplicial Complexes of Antichains in Root Posets
    and Related Combinatorics of Dyck Paths*, arXiv:2609.14054v1, "Conjecture 3.9. The number f_ii
    of Dyck paths in Dyck_n^max with i valleys coincides with A271942." By Lemma 3.4, Dyck_n^max
    is the set of Dyck paths of semilength n avoiding the factor UUDD; a valley is a factor DU.
    OEIS A271942: T(n, k) is the number of bargraphs of semiperimeter n having width k (n ≥ 2,
    k ≥ 1). A bargraph of width k is a sequence of k positive column heights on a common base
    line; its semiperimeter, half its perimeter, is k + h_1 + Σ_j max(h_{j+1} − h_j, 0). -/

open DyckStep

/-- The Dyck word contains no factor `UUDD`. -/
def AvoidsUUDD (p : DyckWord) : Prop := ¬ [U, U, D, D] <:+: p.toList

/-- The number of valleys (factors `DU`) of a Dyck word. -/
def valleys (p : DyckWord) : ℕ := (p.toList.zip p.toList.tail).count (D, U)

/-- The total ascent `Σ max(h_{j+1} − h_j, 0)` of a list of column heights. -/
def ascent : List ℕ → ℕ
  | a :: b :: t => (b - a) + ascent (b :: t)
  | _ => 0

/-- The semiperimeter of the bargraph with column heights `H`. -/
def semiperimeter (H : List ℕ) : ℕ := H.length + H.headD 0 + ascent H

/-- `H` is a bargraph: a nonempty list of positive column heights. -/
def IsBargraph (H : List ℕ) : Prop := H ≠ [] ∧ ∀ h ∈ H, 0 < h

/-- Conjecture 3.9. -/
def claim : Prop :=
  ∀ n i : ℕ, 2 ≤ n → 1 ≤ i → i ≤ n - 1 →
    {p : DyckWord | p.semilength = n ∧ AvoidsUUDD p ∧ valleys p = i}.ncard =
      {H : List ℕ | IsBargraph H ∧ H.length = i ∧ semiperimeter H = n}.ncard

end D5.S3.Combinatorics.DyckValleys.ValleyBargraphDefs
