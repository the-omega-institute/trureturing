/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sample
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Sample
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: Labelled successor checks across all three new residual budgets. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

/-- Row 000101 with residual budget 0. -/
theorem row_0 : outgoing (rep 0) (budget 0) = weights 0 := by
  decide +kernel

/-- Row 001010 with residual budget 1. -/
theorem row_40 : outgoing (rep 40) (budget 40) = weights 40 := by
  decide +kernel

/-- Row 010101 with residual budget 2. -/
theorem row_80 : outgoing (rep 80) (budget 80) = weights 80 := by
  decide +kernel

#print axioms row_0
#print axioms row_40
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
