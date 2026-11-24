/- GID: D5/S3/Quantum/Measurement/Auric/UnequalGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical gain range equals the scaled feasible spectral range in either working dimension. -/

import D5.S3.Quantum.Measurement.Auric.UnequalGeometryFrames
import D5.S3.Quantum.Measurement.Auric.UnequalGeometryEntropy

/-! Exact range equality from the frame correspondence and the separate entropy calculation. -/

namespace D5.S3.Quantum.Measurement.Auric

open GeometryFrames

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unequal_geometry_statement (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) :
    GeometryStatement c r q := by
  apply geometryStatement_of_frame_gain c r q
  intro hr flip ρ V hFrame _
  obtain ⟨hP, hP₂⟩ := frameProjection_isProjection flip hFrame.1
  exact gain_eq_unequal_rowEffects c flip hr ρ hP hP₂ hFrame.2 V rfl

end D5.S3.Quantum.Measurement.Auric
