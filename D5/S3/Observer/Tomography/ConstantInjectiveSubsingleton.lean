/- GID: D5/S3/Observer/Tomography/ConstantInjectiveSubsingleton
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/ConstantInjectiveSubsingleton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective constant readout forces its state carrier to be a subsingleton. -/

/- Library-search audit trail (2026-08-29):
   * Repository searches for injective constant maps and subsingleton readouts
     found special-case countermodels but no exact general theorem.
   * Pinned Mathlib's `Function.Injective.subsingleton` assumes that the whole
     codomain is a subsingleton, which is stronger than constantness of the
     supplied map. No exact theorem with both source premises was found.
-/

import Mathlib.Logic.Unique

namespace D5.S3.Observer.Tomography.ConstantInjectiveSubsingleton

/-- A map cannot be both injective and constant unless its domain has at most
one element. -/
theorem constant_injective_subsingleton {X Y : Type*} (q : X → Y)
    (injective : Function.Injective q) (constant : ∀ x y, q x = q y) :
    Subsingleton X :=
  ⟨fun x y => injective (constant x y)⟩

end D5.S3.Observer.Tomography.ConstantInjectiveSubsingleton
