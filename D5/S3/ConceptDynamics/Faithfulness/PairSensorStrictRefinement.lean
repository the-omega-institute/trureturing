/- GID: D5/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/PairSensorStrictRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A second sensor strictly refines the first kernel when it resolves a collision. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * D5 searches found specialized multi-axis and finite-quotient separation
     theorems, but no arbitrary two-readout strictness criterion with an
     explicit collision witness.
   * Pinned Mathlib supplies `Setoid.ker` and the order on setoids. The forward
     inclusion is projection of pair equality; strictness is certified by the
     supplied pair separated only by the second readout.
   * The theorem is independent of cardinality, decidability, and structure on
     either output type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.PairSensorStrictRefinement

universe u v w

/-- Adding a second readout strictly shrinks indistinguishability whenever the
first readout has a collision that the second readout separates. -/
theorem pair_sensor_strictly_refines_first_kernel
    {X : Type u} {Y : Type v} {Z : Type w}
    (first : X -> Y) (second : X -> Z)
    (x y : X) (firstCollision : first x = first y)
    (secondSeparates : second x ≠ second y) :
    Setoid.ker (fun state => (first state, second state)) <
      Setoid.ker first := by
  constructor
  · intro left right samePair
    exact congrArg Prod.fst samePair
  · intro reverseInclusion
    have samePair :
        (first x, second x) = (first y, second y) :=
      reverseInclusion firstCollision
    exact secondSeparates (congrArg Prod.snd samePair)

/-- Satisfiability probe: a constant first sensor is strictly refined by a
Boolean identity second sensor. -/
example :
    Setoid.ker (fun x : Bool => ((), x)) <
      Setoid.ker (fun _ : Bool => ()) := by
  exact pair_sensor_strictly_refines_first_kernel
    (X := Bool) (Y := Unit) (Z := Bool)
    (first := fun _ : Bool => ())
    (second := fun x : Bool => x)
    false true rfl Bool.false_ne_true

#print axioms pair_sensor_strictly_refines_first_kernel

end D5.S3.ConceptDynamics.Faithfulness.PairSensorStrictRefinement
