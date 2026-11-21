/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows5
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Exact labelled successor checks for row patterns 60 through 71. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows5

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_60 : outgoing (rep 60) (budget 60) = weights 60 := by
  decide +kernel

private theorem row_61 : outgoing (rep 61) (budget 61) = weights 61 := by
  decide +kernel

private theorem row_62 : outgoing (rep 62) (budget 62) = weights 62 := by
  decide +kernel

private theorem row_63 : outgoing (rep 63) (budget 63) = weights 63 := by
  decide +kernel

private theorem row_64 : outgoing (rep 64) (budget 64) = weights 64 := by
  decide +kernel

private theorem row_65 : outgoing (rep 65) (budget 65) = weights 65 := by
  decide +kernel

private theorem row_66 : outgoing (rep 66) (budget 66) = weights 66 := by
  decide +kernel

private theorem row_67 : outgoing (rep 67) (budget 67) = weights 67 := by
  decide +kernel

private theorem row_68 : outgoing (rep 68) (budget 68) = weights 68 := by
  decide +kernel

private theorem row_69 : outgoing (rep 69) (budget 69) = weights 69 := by
  decide +kernel

private theorem row_70 : outgoing (rep 70) (budget 70) = weights 70 := by
  decide +kernel

private theorem row_71 : outgoing (rep 71) (budget 71) = weights 71 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨60 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63
  · exact row_64
  · exact row_65
  · exact row_66
  · exact row_67
  · exact row_68
  · exact row_69
  · exact row_70
  · exact row_71

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows5
