/- GID: D5/S0/Conventions/SingleEyeInvariant
   generality: G
   mirror-B: D5/B/S0/Conventions/SingleEyeInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Single-eyed observers admit invariants depending only on one coordinate. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace D5.S0.Conventions.SingleEyeInvariant

open Set

universe u v

/-- An observer admits only invariants whose dependency sets lie in one coordinate. -/
def IsSingleEyed {Coordinate : Type u} {Invariant : Type v}
    (coordinate : Coordinate)
    (admitted : Set Invariant)
    (dependency : Invariant -> Set Coordinate) : Prop :=
  ∀ invariant ∈ admitted, dependency invariant ⊆ {coordinate}

/-- A singleton family is single-eyed at its sole coordinate. -/
example :
    IsSingleEyed (coordinate := (0 : Nat)) ({()} : Set Unit)
      (fun _ : Unit => ({0} : Set Nat)) := by
  intro invariant hinvariant
  cases invariant
  simp

/-- An admitted invariant depending on two coordinates is not single-eyed at zero. -/
example :
    ¬ IsSingleEyed (coordinate := (0 : Nat)) ({()} : Set Unit)
      (fun _ : Unit => ({0, 1} : Set Nat)) := by
  intro h
  have hsubset := h () (Set.mem_singleton ())
  have hmem : (1 : Nat) ∈ ({0, 1} : Set Nat) :=
    Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton 1))
  have : (1 : Nat) ∈ ({0} : Set Nat) := hsubset hmem
  exact Nat.noConfusion (Set.mem_singleton_iff.mp this)

end D5.S0.Conventions.SingleEyeInvariant
