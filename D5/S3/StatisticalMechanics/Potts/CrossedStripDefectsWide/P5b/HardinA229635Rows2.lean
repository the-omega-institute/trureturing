/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows2
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Exact labelled successor checks for row patterns 24 through 35. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows2

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_24 : outgoing (rep 24) (budget 24) = weights 24 := by
  decide +kernel

private theorem row_25 : outgoing (rep 25) (budget 25) = weights 25 := by
  decide +kernel

private theorem row_26 : outgoing (rep 26) (budget 26) = weights 26 := by
  decide +kernel

private theorem row_27 : outgoing (rep 27) (budget 27) = weights 27 := by
  decide +kernel

private theorem row_28 : outgoing (rep 28) (budget 28) = weights 28 := by
  decide +kernel

private theorem row_29 : outgoing (rep 29) (budget 29) = weights 29 := by
  decide +kernel

private theorem row_30 : outgoing (rep 30) (budget 30) = weights 30 := by
  decide +kernel

private theorem row_31 : outgoing (rep 31) (budget 31) = weights 31 := by
  decide +kernel

private theorem row_32 : outgoing (rep 32) (budget 32) = weights 32 := by
  decide +kernel

private theorem row_33 : outgoing (rep 33) (budget 33) = weights 33 := by
  decide +kernel

private theorem row_34 : outgoing (rep 34) (budget 34) = weights 34 := by
  decide +kernel

private theorem row_35 : outgoing (rep 35) (budget 35) = weights 35 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨24 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows2
