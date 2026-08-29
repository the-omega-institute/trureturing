/- GID: D5/S3/ConceptDynamics/SensorFamilies/SurjectiveSensorReindexKernelEquality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SensorFamilies/SurjectiveSensorReindexKernelEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Surjective reindexing preserves the joint sensor kernel. -/

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

namespace D5.S3.ConceptDynamics.SensorFamilies.SurjectiveSensorReindexKernelEquality

universe u v w z

def FamilyKernel {Index : Type u} {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output) (x y : State) : Prop :=
  forall index, sensor index x = sensor index y

/-- A surjective change of sensor indices preserves exactly the family kernel. -/
theorem surjective_reindex_preserves_family_kernel
    {Index : Type u} {NewIndex : Type z}
    {State : Type v} {Output : Type w}
    (sensor : Index -> State -> Output)
    (select : NewIndex -> Index)
    (selectSurjective : Function.Surjective select)
    (x y : State) :
    FamilyKernel sensor x y ↔
      FamilyKernel (fun j => sensor (select j)) x y := by
  constructor
  · intro same index
    exact same (select index)
  · intro same index
    rcases selectSurjective index with ⟨newIndex, selected⟩
    rw [← selected]
    exact same newIndex

#print axioms surjective_reindex_preserves_family_kernel

end D5.S3.ConceptDynamics.SensorFamilies.SurjectiveSensorReindexKernelEquality
