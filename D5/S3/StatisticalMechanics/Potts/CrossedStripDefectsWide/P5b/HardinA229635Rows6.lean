/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows6
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows6
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: Exact labelled successor checks for row patterns 72 through 83. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows6

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_72 : outgoing (rep 72) (budget 72) = weights 72 := by
  decide +kernel

private theorem row_73 : outgoing (rep 73) (budget 73) = weights 73 := by
  decide +kernel

private theorem row_74 : outgoing (rep 74) (budget 74) = weights 74 := by
  decide +kernel

private theorem row_75 : outgoing (rep 75) (budget 75) = weights 75 := by
  decide +kernel

private theorem row_76 : outgoing (rep 76) (budget 76) = weights 76 := by
  decide +kernel

private theorem row_77 : outgoing (rep 77) (budget 77) = weights 77 := by
  decide +kernel

private theorem row_78 : outgoing (rep 78) (budget 78) = weights 78 := by
  decide +kernel

private theorem row_79 : outgoing (rep 79) (budget 79) = weights 79 := by
  decide +kernel

private theorem row_81 : outgoing (rep 81) (budget 81) = weights 81 := by
  decide +kernel

private theorem row_82 : outgoing (rep 82) (budget 82) = weights 82 := by
  decide +kernel

private theorem row_83 : outgoing (rep 83) (budget 83) = weights 83 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨72 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_72
  · exact row_73
  · exact row_74
  · exact row_75
  · exact row_76
  · exact row_77
  · exact row_78
  · exact row_79
  · exact HardinA229635Sample.row_80
  · exact row_81
  · exact row_82
  · exact row_83

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows6
