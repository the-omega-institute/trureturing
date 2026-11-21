/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: Exact sparse iteration checks between tabulated integer vectors. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Powers

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck2

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635SparseData HardinA229635Powers

private theorem step_20 : ∀ s : State, power 21 s = step (power 20) s := by
  decide +kernel

private theorem step_21 : ∀ s : State, power 22 s = step (power 21) s := by
  decide +kernel

private theorem step_22 : ∀ s : State, power 23 s = step (power 22) s := by
  decide +kernel

private theorem step_23 : ∀ s : State, power 24 s = step (power 23) s := by
  decide +kernel

private theorem step_24 : ∀ s : State, power 25 s = step (power 24) s := by
  decide +kernel

private theorem step_25 : ∀ s : State, power 26 s = step (power 25) s := by
  decide +kernel

private theorem step_26 : ∀ s : State, power 27 s = step (power 26) s := by
  decide +kernel

private theorem step_27 : ∀ s : State, power 28 s = step (power 27) s := by
  decide +kernel

private theorem step_28 : ∀ s : State, power 29 s = step (power 28) s := by
  decide +kernel

private theorem step_29 : ∀ s : State, power 30 s = step (power 29) s := by
  decide +kernel

theorem checked (k : Fin 10) :
    let i : Fin 30 := ⟨20 + k.val, by omega⟩
    power i.succ = step (power i.castSucc) := by
  fin_cases k
  · exact funext step_20
  · exact funext step_21
  · exact funext step_22
  · exact funext step_23
  · exact funext step_24
  · exact funext step_25
  · exact funext step_26
  · exact funext step_27
  · exact funext step_28
  · exact funext step_29

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck2
