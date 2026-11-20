/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripStep0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
steps: proof_shape=bind-only; consumers=HardinA229457StripPowers.steps
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData

/-! Coordinates of the square-strip forward powers. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep0
open HardinA229457StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem steps (i : Fin 13) (s : Fin 32) :
    W ⟨0 + i.val + 1, by omega⟩ (s.natAdd 10) =
      Matrix.vecMul (W ⟨0 + i.val, by omega⟩) T (s.natAdd 10) := by
  decide +kernel +revert

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep0
