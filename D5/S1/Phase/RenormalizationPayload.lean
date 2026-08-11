/- GID: D5/S1/Phase/RenormalizationPayload
   generality: I
   mirror-B: D5/B/S1/Phase/RenormalizationPayload
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Both golden face readings determine the renormalization map. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Phase.RenormalizationPayload

/-- The two coordinates carrying the expansion and contraction readings. -/
abbrev Face := Fin 2

/-- The canonical map scales the expansion face by the golden ratio and the
contraction face by its conjugate. -/
noncomputable def faceRenormalization (z : Face -> Real) : Face -> Real :=
  ![Real.goldenRatio * z 0, Real.goldenConj * z 1]

/-- The complete pair of coordinate laws for a proposed two-face map. -/
structure RenormalizationReadings
    (R : (Face -> Real) -> Face -> Real) : Prop where
  expansion : forall z, R z 0 = Real.goldenRatio * z 0
  contraction : forall z, R z 1 = Real.goldenConj * z 1

/-- A map with both face readings is the canonical renormalization map.  Thus
the operator is recoverable from the two laws it carries. -/
theorem renormalization_payload {R : (Face -> Real) -> Face -> Real}
    (hR : RenormalizationReadings R) : R = faceRenormalization := by
  funext z i
  fin_cases i
  · exact hR.expansion z
  · exact hR.contraction z

end D5.S1.Phase.RenormalizationPayload
