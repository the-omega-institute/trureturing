/- GID: D5/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/InjectiveSensorFamilyFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One injective sensor makes the complete sensor family faithful. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches for jointly faithful sensor families found finite
     quotient and tomography specializations, but no theorem at the level of an
     arbitrary indexed family of functions.
   * Pinned Mathlib supplies `Function.Injective` and function extensionality.
     The proof evaluates equality of the joint readout at the injective sensor.
   * No finiteness, decidable equality, topology, or algebraic structure is
     required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.InjectiveSensorFamilyFaithfulness

universe u v w

/-- If one member of a sensor family is injective, then the joint readout into
all sensor coordinates is injective. -/
theorem injective_member_makes_joint_readout_injective
    {Index : Type u} {X : Type v} {O : Type w}
    (sensor : Index -> X -> O) (index : Index)
    (injective : Function.Injective (sensor index)) :
    Function.Injective (fun x i => sensor i x) := by
  intro x y sameJointReadout
  apply injective
  exact congrFun sameJointReadout index

/-- Satisfiability probe: a one-sensor family containing the Boolean identity
readout is jointly faithful. -/
example :
    Function.Injective (fun x : Bool => fun _ : PUnit => x) := by
  intro x y sameJointReadout
  exact congrFun sameJointReadout PUnit.unit

/-- Consequence probe: equality of all sensor coordinates forces equality of
states as soon as one selected coordinate is injective. -/
example {Index : Type u} {X : Type v} {O : Type w}
    (sensor : Index -> X -> O) (index : Index)
    (injective : Function.Injective (sensor index))
    (x y : X) (same : forall i, sensor i x = sensor i y) :
    x = y := by
  apply injective
  exact same index

#print axioms injective_member_makes_joint_readout_injective

end D5.S3.ConceptDynamics.Faithfulness.InjectiveSensorFamilyFaithfulness
