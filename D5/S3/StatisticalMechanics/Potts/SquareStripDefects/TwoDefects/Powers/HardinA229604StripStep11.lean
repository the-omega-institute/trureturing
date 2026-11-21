/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep11
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/TwoDefects/Powers/HardinA229604StripStep11
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
steps: proof_shape=bind-only; consumers=HardinA229604StripPowers.steps
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData

/-! New terminal-sector coordinates of the forward powers. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep11
open HardinA229604StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem steps (i : Fin 6) (s : Fin 18) :
    W ⟨18 + i.val + 1, by omega⟩ ⟨78 + s.val, by omega⟩ =
      Matrix.vecMul (W ⟨18 + i.val, by omega⟩) T ⟨78 + s.val, by omega⟩ := by
  decide +kernel +revert

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep11
