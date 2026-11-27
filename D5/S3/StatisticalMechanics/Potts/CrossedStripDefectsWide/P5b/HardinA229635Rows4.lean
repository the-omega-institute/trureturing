/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows4
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows4
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Exact labelled successor checks for row patterns 48 through 59. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows4

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_48 : outgoing (rep 48) (budget 48) = weights 48 := by
  decide +kernel

private theorem row_49 : outgoing (rep 49) (budget 49) = weights 49 := by
  decide +kernel

private theorem row_50 : outgoing (rep 50) (budget 50) = weights 50 := by
  decide +kernel

private theorem row_51 : outgoing (rep 51) (budget 51) = weights 51 := by
  decide +kernel

private theorem row_52 : outgoing (rep 52) (budget 52) = weights 52 := by
  decide +kernel

private theorem row_53 : outgoing (rep 53) (budget 53) = weights 53 := by
  decide +kernel

private theorem row_54 : outgoing (rep 54) (budget 54) = weights 54 := by
  decide +kernel

private theorem row_55 : outgoing (rep 55) (budget 55) = weights 55 := by
  decide +kernel

private theorem row_56 : outgoing (rep 56) (budget 56) = weights 56 := by
  decide +kernel

private theorem row_57 : outgoing (rep 57) (budget 57) = weights 57 := by
  decide +kernel

private theorem row_58 : outgoing (rep 58) (budget 58) = weights 58 := by
  decide +kernel

private theorem row_59 : outgoing (rep 59) (budget 59) = weights 59 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨48 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows4
