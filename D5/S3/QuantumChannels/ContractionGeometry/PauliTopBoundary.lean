/- GID: D5/S3/QuantumChannels/ContractionGeometry/PauliTopBoundary
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ContractionGeometry/PauliTopBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The squared sup-norm top boundary of three Pauli parameters has zero Haar volume. -/

import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.RCLike.Real

open MeasureTheory Metric Set

namespace D5.S3.QuantumChannels.ContractionGeometry.PauliTopBoundary

/- Mathlib provides `Convex.addHaar_frontier`; the proof identifies the top boundary with the
unit sup-norm sphere and applies that theorem to the closed unit ball. -/

/-- The parameter locus where the squared sup norm of three Pauli contraction coefficients is one
has zero volume. -/
theorem pauli_top_boundary_volume_zero :
    volume {t : Fin 3 → ℝ | ‖t‖ ^ 2 = 1} = 0 := by
  have hsphere : {t : Fin 3 → ℝ | ‖t‖ ^ 2 = 1} = sphere 0 1 := by
    apply Set.ext
    intro t
    simp only [Set.mem_setOf_eq, mem_sphere_zero_iff_norm]
    constructor
    · intro h
      nlinarith [norm_nonneg t]
    · intro h
      rw [h]
      norm_num
  rw [hsphere, ← frontier_closedBall (0 : Fin 3 → ℝ) one_ne_zero]
  exact (convex_closedBall (0 : Fin 3 → ℝ) 1).addHaar_frontier volume

#print axioms pauli_top_boundary_volume_zero

end D5.S3.QuantumChannels.ContractionGeometry.PauliTopBoundary
