/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635RowCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635RowCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: All labelled successor lists for the fresh width-six row patterns. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows2
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows3
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows4
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows5
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows6
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows7

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635RowCertificate

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635Rows

theorem checked_weights (i : Fresh) : outgoing (rep i) (budget i) = weights i := by
  by_cases h0 : i.val < 12
  · let j : Fin 12 := ⟨i.val - 0, by omega⟩
    have hi : (⟨0 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows0.checked j
  by_cases h1 : i.val < 24
  · let j : Fin 12 := ⟨i.val - 12, by omega⟩
    have hi : (⟨12 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows1.checked j
  by_cases h2 : i.val < 36
  · let j : Fin 12 := ⟨i.val - 24, by omega⟩
    have hi : (⟨24 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows2.checked j
  by_cases h3 : i.val < 48
  · let j : Fin 12 := ⟨i.val - 36, by omega⟩
    have hi : (⟨36 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows3.checked j
  by_cases h4 : i.val < 60
  · let j : Fin 12 := ⟨i.val - 48, by omega⟩
    have hi : (⟨48 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows4.checked j
  by_cases h5 : i.val < 72
  · let j : Fin 12 := ⟨i.val - 60, by omega⟩
    have hi : (⟨60 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows5.checked j
  by_cases h6 : i.val < 84
  · let j : Fin 12 := ⟨i.val - 72, by omega⟩
    have hi : (⟨72 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
    simpa only [hi] using HardinA229635Rows6.checked j
  let j : Fin 12 := ⟨i.val - 84, by omega⟩
  have hi : (⟨84 + j.val, by omega⟩ : Fresh) = i := Fin.ext (by dsimp [j]; omega)
  simpa only [hi] using HardinA229635Rows7.checked j

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635RowCertificate
