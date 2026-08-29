/- GID: D5/S3/Observer/CompletionPoints/CompletionPointIntersection
   generality: G
   mirror-B: D5/B/S3/Observer/CompletionPoints/CompletionPointIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Paired zero-defect completion equals intersection of component completion conditions. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.CompletionPoints.CompletionPointIntersection

universe u v w

def ZeroAt {State : Type u} {Defect : Type v}
    (defect : State -> Defect) (zero : Defect) (state : State) : Prop :=
  defect state = zero

def zeroSet {State : Type u} {Defect : Type v}
    (defect : State -> Defect) (zero : Defect) : Set State :=
  {state | ZeroAt defect zero state}

/-- Vanishing of a paired defect is equivalent to simultaneous vanishing of
its two components. -/
theorem paired_zero_iff_component_zeros
    {State : Type u} {First : Type v} {Second : Type w}
    (first : State -> First) (second : State -> Second)
    (firstZero : First) (secondZero : Second) (state : State) :
    ZeroAt (fun s => (first s, second s)) (firstZero, secondZero) state ↔
      ZeroAt first firstZero state ∧ ZeroAt second secondZero state := by
  simp [ZeroAt]

/-- The completion set of a paired defect is the intersection of the two
component completion sets. -/
theorem paired_zero_set_eq_intersection
    {State : Type u} {First : Type v} {Second : Type w}
    (first : State -> First) (second : State -> Second)
    (firstZero : First) (secondZero : Second) :
    zeroSet (fun s => (first s, second s)) (firstZero, secondZero) =
      zeroSet first firstZero ∩ zeroSet second secondZero := by
  ext state
  simp [zeroSet, ZeroAt]

#print axioms paired_zero_iff_component_zeros
#print axioms paired_zero_set_eq_intersection

end D5.S3.Observer.CompletionPoints.CompletionPointIntersection
