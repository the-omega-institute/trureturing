/- GID: D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyRestrictionMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SensorFamilies/SensorFamilyRestrictionMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Restricting a sensor family can only enlarge its equality kernel. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches found finite schedule monotonicity and coordinate
     deletion results under additional structure, but no arbitrary reindexing
     theorem for function-valued readouts.
   * Pinned Mathlib supplies `Setoid.ker` and function extensionality. Equality
     at all original coordinates implies equality at every selected coordinate.
   * The selector need not be injective or surjective, and both index types may
     be empty or infinite.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SensorFamilies.SensorFamilyRestrictionMonotonicity

universe u v w z

/-- Any reindexed subfamily has an equality kernel containing the kernel of the
complete family. Repetition and deletion of sensors cannot create distinctions. -/
theorem restricting_sensor_family_enlarges_kernel
    {Index : Type u} {Selected : Type v} {X : Type w} {O : Type z}
    (sensor : Index -> X -> O) (select : Selected -> Index) :
    Setoid.ker (fun x index => sensor index x) <=
      Setoid.ker (fun x selected => sensor (select selected) x) := by
  intro x y sameAll
  funext selected
  exact congrFun sameAll (select selected)

/-- Satisfiability probe: identity reindexing preserves every coordinate of a
one-sensor Boolean family. -/
example :
    Setoid.ker (fun x : Bool => fun _ : Unit => x) <=
      Setoid.ker (fun x : Bool => fun _ : Unit => x) := by
  exact restricting_sensor_family_enlarges_kernel
    (Index := Unit) (Selected := Unit) (X := Bool) (O := Bool)
    (sensor := fun _ : Unit => fun x : Bool => x)
    (select := fun index : Unit => index)

#print axioms restricting_sensor_family_enlarges_kernel

end D5.S3.ConceptDynamics.SensorFamilies.SensorFamilyRestrictionMonotonicity
