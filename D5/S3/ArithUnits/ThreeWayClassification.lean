/- GID: D5/S3/ArithUnits/ThreeWayClassification
   generality: G
   mirror-B: D5/B/S3/ArithUnits/ThreeWayClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A three-element classification is not equivalent to a two-element residue grading. -/

import Mathlib.Data.ZMod.Basic

namespace D5.S3.ArithUnits.ThreeWayClassification

/-- No equivalence can identify a three-element classification with residues modulo two.

This is an honest partial closure of the source's non-binary clause. The source's
self-description, copying, fixed-point-count, and parity-interpretation claims remain unresolved.
-/
theorem three_way_classification_not_binary :
    ¬ Nonempty (Fin 3 ≃ ZMod 2) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp [ZMod.card] at h

/-- Both finite domains in the classification obstruction are inhabited. -/
example : Nonempty (Fin 3) ∧ Nonempty (ZMod 2) :=
  ⟨⟨0⟩, ⟨0⟩⟩

end D5.S3.ArithUnits.ThreeWayClassification
