/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck2
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseCheck2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: Exact transpose check for sparse predecessor lists. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseData

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck2

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635SparseData

theorem exact_transpose :
    ∀ j : Fin 32, let k : State := ⟨64 + j.val, by omega⟩
      incomingClasses k = transposeLists k := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck2
