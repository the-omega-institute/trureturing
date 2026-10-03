/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Model
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Model
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Noncrossing upper matching and source winding and connectivity predicates. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

/-- Noncrossing upper arches as a fixed-point-free endpoint involution. -/
structure UpperMatching (n : ℕ) where
  mate : Fin (2 * n) → Fin (2 * n)
  mate_mate : ∀ x, mate (mate x) = x
  mate_ne : ∀ x, mate x ≠ x
  noncrossing : ∀ a b : Fin (2 * n), a.val < b.val →
    b.val < (mate a).val → (mate a).val < (mate b).val → False

/-- Number of upper arches crossing the midpoint. -/
def UpperMatching.winding {n : ℕ} (M : UpperMatching n) : ℕ :=
  (Finset.univ.filter fun x : Fin n =>
    n ≤ (M.mate ⟨x.val, by have := x.isLt; omega⟩).val).card

/-- Connectivity through upper arches and the fixed lower rainbow. -/
def UpperMatching.oneLoop {n : ℕ} (M : UpperMatching n) : Prop :=
  ∀ x y : Fin (2 * n),
    Relation.ReflTransGen (fun x y => M.mate x = y ∨ x.rev = y) x y


end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
