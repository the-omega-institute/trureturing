/- GID: D5/S3/Combinatorics/BoseTriplingBurningRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BoseTriplingBurningRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Ordinary burning of a cyclic Steiner triple system and its Bose tripling. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import OmegaBuild.Commands

/-! The cyclic system of order 13 and its cited Bose tripling of order 39. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Combinatorics.BoseTriplingBurningRefutation

/-- Pair completion of a Steiner triple system, with the diagonal extended idempotently. -/
structure Steiner (α : Type) where
  complete : α → α → α
  comm : ∀ x y, complete x y = complete y x
  idem : ∀ x, complete x x = x
  cancel : ∀ x y, complete x (complete x y) = y

variable {α : Type} [LinearOrder α]

private def pairs (s : Finset α) : Finset (α × α) :=
  (s.product s).filter fun p => p.1 < p.2

/-- Simultaneously add the completions of all pairs in the preceding burned set. -/
def spread (H : Steiner α) (s : Finset α) : Finset α :=
  s ∪ (pairs s).image fun p => H.complete p.1 p.2

/-- A round propagates from the preceding burned set and adds its chosen source. -/
def step (H : Steiner α) (s : Finset α) (u : α) : Finset α :=
  insert u (spread H s)

/-- Burned set after the given sources, starting from an arbitrary initial set. -/
def burned (H : Steiner α) (s : Finset α) (sources : List α) : Finset α :=
  sources.foldl (step H) s

/-- A legal source can be reached by same-round propagation, but cannot already be burned. -/
def legal (H : Steiner α) (s : Finset α) : List α → Bool
  | [] => true
  | u :: rest => decide (u ∉ s) && legal H (step H s u) rest

/-- A complete ordinary burning run from the empty set. -/
def Run [Fintype α] (H : Steiner α) (sources : List α) : Prop :=
  legal H ∅ sources = true ∧ burned H ∅ sources = Finset.univ

-- Offsets of the third point from the first, indexed by the signed difference y - x.
private def offsets : Array (Fin 13) := #[0, 4, 7, 12, 1, 11, 8, 2, 6, 10, 9, 5, 3]

private def complete13 (x y : Fin 13) : Fin 13 :=
  x + offsets[(y - x).val]!

private theorem complete13_comm : ∀ x y, complete13 x y = complete13 y x := by decide
private theorem complete13_idem : ∀ x, complete13 x x = x := by decide
private theorem complete13_cancel : ∀ x y, complete13 x (complete13 x y) = y := by decide

private def cyclic13 : Steiner (Fin 13) :=
  ⟨complete13, complete13_comm, complete13_idem, complete13_cancel⟩

private def tiltedLayer (i j : Fin 3) : Fin 3 :=
  if i = j then i + 1 else if j = i + 1 then i else j

private def verticalLayer (i j : Fin 3) : Fin 3 := 0 - i - j

private theorem tilted_comm : ∀ i j, tiltedLayer i j = tiltedLayer j i := by decide
private theorem tilted_cancel : ∀ i j, tiltedLayer i (tiltedLayer i j) = j := by decide
private theorem vertical_comm : ∀ i j, verticalLayer i j = verticalLayer j i := by decide
private theorem vertical_idem : ∀ i, verticalLayer i i = i := by decide
private theorem vertical_cancel : ∀ i j, verticalLayer i (verticalLayer i j) = j := by decide

omit [LinearOrder α] in
private theorem complete_ne_left (H : Steiner α) {x y : α} (h : x ≠ y) :
    H.complete x y ≠ x := by
  intro e
  apply h
  calc
    x = H.complete x x := (H.idem x).symm
    _ = H.complete x (H.complete x y) := congrArg (H.complete x) e.symm
    _ = y := H.cancel x y

private def boseComplete (H : Steiner α) (x y : α × Fin 3) : α × Fin 3 :=
  if x.1 = y.1 then (x.1, verticalLayer x.2 y.2)
  else (H.complete x.1 y.1, tiltedLayer x.2 y.2)

/-- Bose tripling has the vertical triples and the triples
`{(x,i), (y,i), (H.complete x y,i+1)}` with `x ≠ y`. -/
private def boseOnProduct (H : Steiner α) : Steiner (α × Fin 3) where
  complete := boseComplete H
  comm x y := by
    by_cases h : x.1 = y.1
    · simp [boseComplete, h, vertical_comm]
    · simp [boseComplete, h, Ne.symm h, H.comm x.1 y.1, tilted_comm]
  idem x := by simp [boseComplete, vertical_idem]
  cancel x y := by
    by_cases h : x.1 = y.1
    · simp [boseComplete, h, vertical_cancel]
    · simp [boseComplete, h, Ne.symm (complete_ne_left H h), H.cancel, tilted_cancel]

/-- Encode Bose points by `(x,i) ↦ 3*x+i`. -/
def bose {n : ℕ} (H : Steiner (Fin n)) : Steiner (Fin (n * 3)) where
  complete x y :=
    finProdFinEquiv ((boseOnProduct H).complete (finProdFinEquiv.symm x) (finProdFinEquiv.symm y))
  comm x y := by rw [(boseOnProduct H).comm]
  idem x := by simp only [(boseOnProduct H).idem, Equiv.apply_symm_apply]
  cancel x y := by simp only [Equiv.symm_apply_apply, (boseOnProduct H).cancel, Equiv.apply_symm_apply]

private theorem cyclic_translates :
    ∀ t : Fin 13, complete13 t (t + 1) = t + 4 ∧ complete13 t (t + 2) = t + 7 := by decide

private def schedule13 : List (Fin 13) := [0, 1, 2, 3, 6]

-- Encoded by (x,i) ↦ 3*x+i, the sources are 0, 1, 3, 6, 4, 7.
private def schedule39 : List (Fin 39) := [0, 1, 3, 6, 4, 7]

private theorem run13 : Run cyclic13 schedule13 := by
  unfold Run
  exact ⟨by decide, by decide⟩

set_option maxRecDepth 4096 in
private theorem run39 : Run (bose cyclic13) schedule39 := by
  unfold Run
  exact ⟨by decide, by decide⟩

end D5.S3.Combinatorics.BoseTriplingBurningRefutation
