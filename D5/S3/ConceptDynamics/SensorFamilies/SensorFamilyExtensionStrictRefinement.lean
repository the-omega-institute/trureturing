/- GID: D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SensorFamilies/SensorFamilyExtensionStrictRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adding a separating sensor strictly refines a sensor-family kernel. -/

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

namespace D5.S3.ConceptDynamics.SensorFamilies.SensorFamilyExtensionStrictRefinement

universe u v w

def FamilyKernel {Index : Type u} {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output) (x y : State) : Prop :=
  forall index, sensor index x = sensor index y

def extendedSensor {Index : Type u} {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output) (extra : State -> Output) :
    Sum Index PUnit -> State -> Output
  | Sum.inl index => sensor index
  | Sum.inr _ => extra

/-- Equality under the extended family implies equality under the original
family. -/
theorem extension_kernel_refines_original
    {Index : Type u} {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output) (extra : State -> Output)
    {x y : State}
    (sameExtended : FamilyKernel (extendedSensor sensor extra) x y) :
    FamilyKernel sensor x y := by
  intro index
  exact sameExtended (Sum.inl index)

/-- A new coordinate that separates an old collision makes the refinement
strict at that witness pair. -/
theorem separating_extension_witnesses_strict_refinement
    {Index : Type u} {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output) (extra : State -> Output)
    {x y : State}
    (sameOld : FamilyKernel sensor x y)
    (extraSeparates : extra x ≠ extra y) :
    FamilyKernel sensor x y ∧
      ¬ FamilyKernel (extendedSensor sensor extra) x y := by
  refine ⟨sameOld, ?_⟩
  intro sameExtended
  exact extraSeparates (sameExtended (Sum.inr PUnit.unit))

#print axioms extension_kernel_refines_original
#print axioms separating_extension_witnesses_strict_refinement

end D5.S3.ConceptDynamics.SensorFamilies.SensorFamilyExtensionStrictRefinement
