/- GID: D5/S3/Observer/CompletionPoints/CompletionPointPullback
   generality: G
   mirror-B: D5/B/S3/Observer/CompletionPoints/CompletionPointPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion points pull back exactly along a change of state representation. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.CompletionPoints.CompletionPointPullback

universe u v w

def ZeroAt {State : Type u} {Defect : Type v}
    (defect : State -> Defect) (zero : Defect) (state : State) : Prop :=
  defect state = zero

def zeroSet {State : Type u} {Defect : Type v}
    (defect : State -> Defect) (zero : Defect) : Set State :=
  {state | ZeroAt defect zero state}

/-- Pointwise completion for a pulled-back defect is completion after mapping
to the original state space. -/
theorem zero_at_pullback
    {Source : Type u} {Target : Type v} {Defect : Type w}
    (mapState : Source -> Target) (defect : Target -> Defect)
    (zero : Defect) (source : Source) :
    ZeroAt (defect ∘ mapState) zero source ↔
      ZeroAt defect zero (mapState source) :=
  Iff.rfl

/-- The zero set of a pulled-back defect is the preimage of the original zero
set. -/
theorem zero_set_pullback
    {Source : Type u} {Target : Type v} {Defect : Type w}
    (mapState : Source -> Target) (defect : Target -> Defect)
    (zero : Defect) :
    zeroSet (defect ∘ mapState) zero =
      mapState ⁻¹' zeroSet defect zero := by
  rfl

#print axioms zero_at_pullback
#print axioms zero_set_pullback

end D5.S3.Observer.CompletionPoints.CompletionPointPullback
