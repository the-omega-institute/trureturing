/- GID: D5/S1/Dynamics/KnasterTarski
   generality: G
   mirror-B: D5/B/S1/Dynamics/KnasterTarski
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Monotone endomorphisms have extremal fixed points, separated by a three-state cycle. -/

import Mathlib.Order.FixedPoints

namespace D5.S1.Dynamics.KnasterTarski

open Function (fixedPoints)

/-- A monotone endomorphism of a complete lattice has a least fixed point and
a greatest fixed point. This is the repository-facing Knaster-Tarski wrapper
around Mathlib's `OrderHom.lfp` and `OrderHom.gfp`. -/
theorem knaster_tarski_extremal_fixed_points
    {α : Type*} [CompleteLattice α] (f : α →o α) :
    IsLeast (fixedPoints f) f.lfp ∧ IsGreatest (fixedPoints f) f.gfp :=
  ⟨f.isLeast_lfp, f.isGreatest_gfp⟩

/-- The three states used by the successor-cycle example. -/
inductive ThreeState
  | first
  | second
  | third
  deriving DecidableEq

/-- Successor on the directed three-state cycle. -/
def threeCycleSuccessor : ThreeState → ThreeState
  | .first => .second
  | .second => .third
  | .third => .first

/-- A set contains a state after one backward step exactly when it contains
that state's successor. -/
def threeCycleOperator : Set ThreeState →o Set ThreeState where
  toFun X := {state | threeCycleSuccessor state ∈ X}
  monotone' := by
    intro X Y hXY state hState
    exact hXY hState

/-- For the successor cycle, the least fixed point is empty while the greatest
fixed point is the whole three-state carrier. -/
theorem three_cycle_extremal_fixed_points :
    threeCycleOperator.lfp = ∅ ∧ threeCycleOperator.gfp = Set.univ := by
  constructor
  · exact le_antisymm
      (threeCycleOperator.lfp_le (by
        intro state h
        exact h)) bot_le
  · exact le_antisymm le_top
      (threeCycleOperator.le_gfp (by
        intro state h
        trivial))

end D5.S1.Dynamics.KnasterTarski
