/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows7
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Exact labelled successor checks for row patterns 84 through 95. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows7

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_84 : outgoing (rep 84) (budget 84) = weights 84 := by
  decide +kernel

private theorem row_85 : outgoing (rep 85) (budget 85) = weights 85 := by
  decide +kernel

private theorem row_86 : outgoing (rep 86) (budget 86) = weights 86 := by
  decide +kernel

private theorem row_87 : outgoing (rep 87) (budget 87) = weights 87 := by
  decide +kernel

private theorem row_88 : outgoing (rep 88) (budget 88) = weights 88 := by
  decide +kernel

private theorem row_89 : outgoing (rep 89) (budget 89) = weights 89 := by
  decide +kernel

private theorem row_90 : outgoing (rep 90) (budget 90) = weights 90 := by
  decide +kernel

private theorem row_91 : outgoing (rep 91) (budget 91) = weights 91 := by
  decide +kernel

private theorem row_92 : outgoing (rep 92) (budget 92) = weights 92 := by
  decide +kernel

private theorem row_93 : outgoing (rep 93) (budget 93) = weights 93 := by
  decide +kernel

private theorem row_94 : outgoing (rep 94) (budget 94) = weights 94 := by
  decide +kernel

private theorem row_95 : outgoing (rep 95) (budget 95) = weights 95 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨84 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_84
  · exact row_85
  · exact row_86
  · exact row_87
  · exact row_88
  · exact row_89
  · exact row_90
  · exact row_91
  · exact row_92
  · exact row_93
  · exact row_94
  · exact row_95

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows7
