/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows1
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Exact labelled successor checks for row patterns 12 through 23. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_12 : outgoing (rep 12) (budget 12) = weights 12 := by
  decide +kernel

private theorem row_13 : outgoing (rep 13) (budget 13) = weights 13 := by
  decide +kernel

private theorem row_14 : outgoing (rep 14) (budget 14) = weights 14 := by
  decide +kernel

private theorem row_15 : outgoing (rep 15) (budget 15) = weights 15 := by
  decide +kernel

private theorem row_16 : outgoing (rep 16) (budget 16) = weights 16 := by
  decide +kernel

private theorem row_17 : outgoing (rep 17) (budget 17) = weights 17 := by
  decide +kernel

private theorem row_18 : outgoing (rep 18) (budget 18) = weights 18 := by
  decide +kernel

private theorem row_19 : outgoing (rep 19) (budget 19) = weights 19 := by
  decide +kernel

private theorem row_20 : outgoing (rep 20) (budget 20) = weights 20 := by
  decide +kernel

private theorem row_21 : outgoing (rep 21) (budget 21) = weights 21 := by
  decide +kernel

private theorem row_22 : outgoing (rep 22) (budget 22) = weights 22 := by
  decide +kernel

private theorem row_23 : outgoing (rep 23) (budget 23) = weights 23 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨12 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
