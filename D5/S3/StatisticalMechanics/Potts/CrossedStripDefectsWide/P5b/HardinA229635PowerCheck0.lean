/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_prefix
   digest: Exact sparse iteration checks between tabulated integer vectors. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Powers

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck0

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635SparseData HardinA229635Powers

private theorem step_0 : ∀ s : State, power 1 s = step (power 0) s := by
  decide +kernel

private theorem step_1 : ∀ s : State, power 2 s = step (power 1) s := by
  decide +kernel

private theorem step_2 : ∀ s : State, power 3 s = step (power 2) s := by
  decide +kernel

private theorem step_3 : ∀ s : State, power 4 s = step (power 3) s := by
  decide +kernel

private theorem step_4 : ∀ s : State, power 5 s = step (power 4) s := by
  decide +kernel

private theorem step_5 : ∀ s : State, power 6 s = step (power 5) s := by
  decide +kernel

private theorem step_6 : ∀ s : State, power 7 s = step (power 6) s := by
  decide +kernel

private theorem step_7 : ∀ s : State, power 8 s = step (power 7) s := by
  decide +kernel

private theorem step_8 : ∀ s : State, power 9 s = step (power 8) s := by
  decide +kernel

private theorem step_9 : ∀ s : State, power 10 s = step (power 9) s := by
  decide +kernel

theorem checked (k : Fin 10) :
    let i : Fin 30 := ⟨0 + k.val, by omega⟩
    power i.succ = step (power i.castSucc) := by
  fin_cases k
  · exact funext step_0
  · exact funext step_1
  · exact funext step_2
  · exact funext step_3
  · exact funext step_4
  · exact funext step_5
  · exact funext step_6
  · exact funext step_7
  · exact funext step_8
  · exact funext step_9

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck0
