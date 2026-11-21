/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Exact labelled successor checks for row patterns 0 through 11. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows0

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_1 : outgoing (rep 1) (budget 1) = weights 1 := by
  decide +kernel

private theorem row_2 : outgoing (rep 2) (budget 2) = weights 2 := by
  decide +kernel

private theorem row_3 : outgoing (rep 3) (budget 3) = weights 3 := by
  decide +kernel

private theorem row_4 : outgoing (rep 4) (budget 4) = weights 4 := by
  decide +kernel

private theorem row_5 : outgoing (rep 5) (budget 5) = weights 5 := by
  decide +kernel

private theorem row_6 : outgoing (rep 6) (budget 6) = weights 6 := by
  decide +kernel

private theorem row_7 : outgoing (rep 7) (budget 7) = weights 7 := by
  decide +kernel

private theorem row_8 : outgoing (rep 8) (budget 8) = weights 8 := by
  decide +kernel

private theorem row_9 : outgoing (rep 9) (budget 9) = weights 9 := by
  decide +kernel

private theorem row_10 : outgoing (rep 10) (budget 10) = weights 10 := by
  decide +kernel

private theorem row_11 : outgoing (rep 11) (budget 11) = weights 11 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨0 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact HardinA229635Sample.row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows0
