/- GID: D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect
   generality: G
   mirror-B: D5/B/S3/Observer/CompletionPoints/GaugeStableZeroDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gauge-invariant normalization and defect data preserve completion status. -/

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

namespace D5.S3.Observer.CompletionPoints.GaugeStableZeroDefect

universe u v w

def CompletedAt {State : Type u} {Normal : Type v} {Defect : Type w}
    (normalize : State -> Normal) (target : Normal)
    (defect : State -> Defect) (zero : Defect) (state : State) : Prop :=
  normalize state = target ∧ defect state = zero

/-- A transformation preserving both normalization and defect values preserves
the completed locus in both directions. -/
theorem gauge_preserves_completion
    {State : Type u} {Normal : Type v} {Defect : Type w}
    (normalize : State -> Normal) (target : Normal)
    (defect : State -> Defect) (zero : Defect)
    (gauge : State -> State)
    (normalizeInvariant : forall state,
      normalize (gauge state) = normalize state)
    (defectInvariant : forall state,
      defect (gauge state) = defect state)
    (state : State) :
    CompletedAt normalize target defect zero state ↔
      CompletedAt normalize target defect zero (gauge state) := by
  constructor
  · intro completed
    exact ⟨(normalizeInvariant state).trans completed.1,
      (defectInvariant state).trans completed.2⟩
  · intro completed
    exact ⟨(normalizeInvariant state).symm.trans completed.1,
      (defectInvariant state).symm.trans completed.2⟩

/-- In particular, gauge transport preserves zero defect. -/
theorem gauge_preserves_zero_defect
    {State : Type u} {Defect : Type w}
    (defect : State -> Defect) (zero : Defect)
    (gauge : State -> State)
    (defectInvariant : forall state,
      defect (gauge state) = defect state)
    (state : State) :
    defect state = zero ↔ defect (gauge state) = zero := by
  constructor
  · intro zeroDefect
    exact (defectInvariant state).trans zeroDefect
  · intro zeroDefect
    exact (defectInvariant state).symm.trans zeroDefect

#print axioms gauge_preserves_completion
#print axioms gauge_preserves_zero_defect

end D5.S3.Observer.CompletionPoints.GaugeStableZeroDefect
