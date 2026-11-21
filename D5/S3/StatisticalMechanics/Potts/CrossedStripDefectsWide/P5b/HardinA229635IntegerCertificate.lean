/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.finite_certificate
   digest: Signed residual at the first index and its one-step image. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck2

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635IntegerCertificate

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229635State HardinA229635Transfer HardinA229635Sparse
open HardinA229635SparseData HardinA229635Powers HardinA229635Residual
open DefectTransfer (forward)

private def initialResidual (s : State) : ℤ :=
  if s = 12 then 192 else
  if s = 14 then -192 else
  if s = 15 then -192 else
  if s = 16 then 192 else
  0

private theorem initial_power : ∀ s : State, power 0 s = initial s := by decide +kernel

private theorem step_checks (i : Fin 30) : power i.succ = step (power i.castSucc) := by
  by_cases h0 : i.val < 10
  · let k : Fin 10 := ⟨i.val, h0⟩
    have hi : (⟨0 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by simp [k])
    simpa only [hi] using HardinA229635PowerCheck0.checked k
  by_cases h1 : i.val < 20
  · let k : Fin 10 := ⟨i.val - 10, by omega⟩
    have hi : (⟨10 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by dsimp [k]; omega)
    simpa only [hi] using HardinA229635PowerCheck1.checked k
  · let k : Fin 10 := ⟨i.val - 20, by omega⟩
    have hi : (⟨20 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by dsimp [k]; omega)
    simpa only [hi] using HardinA229635PowerCheck2.checked k

private theorem forward_at (i : Fin 31) : forward T initial i.val = power i := by
  induction i using Fin.induction with
  | zero => exact (funext initial_power).symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.val) T = power i.succ
    change forward T initial i.val = power i.castSucc at ih
    rw [ih, ← step_correct]
    exact (step_checks i).symm

private theorem residual_entries : ∀ s : State,
    (power 30 - ∑ j : Fin 27, coefficients j • power ⟨29 - j.val, by omega⟩) s =
      initialResidual s := by
  decide +kernel

private theorem vector_residual : residualVector T initial = initialResidual := by
  have h0 : forward T initial 30 = power 30 := forward_at 30
  have hj (j : Fin 27) : forward T initial (29 - j.val) =
      power ⟨29 - j.val, by omega⟩ := forward_at _
  simp only [residualVector, h0, hj]
  exact funext residual_entries

private theorem initial_readout : dotProduct initialResidual terminal = 0 := by decide +kernel

private theorem image_entries : ∀ s : State, step initialResidual s = 0 := by decide +kernel

theorem residual_prefix : ∀ t < 127, residual T initial terminal t = 0 := by
  intro t _
  rw [residual_as_power, vector_residual]
  cases t with
  | zero => simpa using initial_readout
  | succ k =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← step_correct]
    have hz : step initialResidual = 0 := funext image_entries
    simp only [hz, zero_dotProduct]

#print axioms residual_prefix

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635IntegerCertificate
