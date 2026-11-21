/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck1
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Exact sparse iteration checks between tabulated integer vectors. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Powers

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State HardinA229635SparseData HardinA229635Powers

private theorem step_10 : ∀ s : State, power 11 s = step (power 10) s := by
  decide +kernel

private theorem step_11 : ∀ s : State, power 12 s = step (power 11) s := by
  decide +kernel

private theorem step_12 : ∀ s : State, power 13 s = step (power 12) s := by
  decide +kernel

private theorem step_13 : ∀ s : State, power 14 s = step (power 13) s := by
  decide +kernel

private theorem step_14 : ∀ s : State, power 15 s = step (power 14) s := by
  decide +kernel

private theorem step_15 : ∀ s : State, power 16 s = step (power 15) s := by
  decide +kernel

private theorem step_16 : ∀ s : State, power 17 s = step (power 16) s := by
  decide +kernel

private theorem step_17 : ∀ s : State, power 18 s = step (power 17) s := by
  decide +kernel

private theorem step_18 : ∀ s : State, power 19 s = step (power 18) s := by
  decide +kernel

private theorem step_19 : ∀ s : State, power 20 s = step (power 19) s := by
  decide +kernel

theorem checked (k : Fin 10) :
    let i : Fin 30 := ⟨10 + k.val, by omega⟩
    power i.succ = step (power i.castSucc) := by
  fin_cases k
  · exact funext step_10
  · exact funext step_11
  · exact funext step_12
  · exact funext step_13
  · exact funext step_14
  · exact funext step_15
  · exact funext step_16
  · exact funext step_17
  · exact funext step_18
  · exact funext step_19

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
