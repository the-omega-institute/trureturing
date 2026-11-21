/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows3
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Rows3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Exact labelled successor checks for row patterns 36 through 47. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows3

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

private theorem row_36 : outgoing (rep 36) (budget 36) = weights 36 := by
  decide +kernel

private theorem row_37 : outgoing (rep 37) (budget 37) = weights 37 := by
  decide +kernel

private theorem row_38 : outgoing (rep 38) (budget 38) = weights 38 := by
  decide +kernel

private theorem row_39 : outgoing (rep 39) (budget 39) = weights 39 := by
  decide +kernel

private theorem row_41 : outgoing (rep 41) (budget 41) = weights 41 := by
  decide +kernel

private theorem row_42 : outgoing (rep 42) (budget 42) = weights 42 := by
  decide +kernel

private theorem row_43 : outgoing (rep 43) (budget 43) = weights 43 := by
  decide +kernel

private theorem row_44 : outgoing (rep 44) (budget 44) = weights 44 := by
  decide +kernel

private theorem row_45 : outgoing (rep 45) (budget 45) = weights 45 := by
  decide +kernel

private theorem row_46 : outgoing (rep 46) (budget 46) = weights 46 := by
  decide +kernel

private theorem row_47 : outgoing (rep 47) (budget 47) = weights 47 := by
  decide +kernel

theorem checked (j : Fin 12) :
    let i : Fresh := ⟨36 + j.val, by omega⟩
    outgoing (rep i) (budget i) = weights i := by
  fin_cases j
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39
  · exact HardinA229635Sample.row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows3
