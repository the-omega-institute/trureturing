/- GID: D5/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nondegenerate reflected spectral pair has canonical first-separation time one. -/

import D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
import D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility
import D5.S3.Observer.Separation.FiniteFutureCongruence

/-!
Library-first audit:
* `separationTime` and `observedAt` are reused from the canonical finite-future
  congruence theory.
* The spectral model supplies a concrete realization in which the reflected
  branches collide at time zero and separate at time one.
* No second break-depth or first-visible-time API is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.TemporalReflectionSeparationTime

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
open D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility
open D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

/-- Canonical point observation of diagonal spectral evolution is the scalar
crystal-time sample at that time. -/
theorem observed_at_spectral_eq_crystal_time_sample
    {n : ℕ} (modes amplitudes : Fin n → ℂ) (time : ℕ) :
    observedAt (oneStepSpectralUpdate modes) modalSumReadout time amplitudes =
      crystalTimeSample modes amplitudes time := by
  unfold observedAt
  rw [one_step_spectral_update_iterate]
  unfold modalSumReadout spectralFiberTransport crystalTimeSample
  apply Finset.sum_congr rfl
  intro mode _
  ring

/-- A reflected pair that is invisible at time zero and nondegenerate at time
one has canonical first-separation time exactly one. -/
theorem reflected_branch_separation_time_eq_one
    {z : ℂ} (hBreak : z ≠ z⁻¹) :
    separationTime (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
      (firstBranch, secondBranch) = 1 := by
  have hZero :
      observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          0 firstBranch =
        observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          0 secondBranch := by
    rw [observed_at_spectral_eq_crystal_time_sample,
      observed_at_spectral_eq_crystal_time_sample]
    exact reflected_branches_static_collision z
  have hOne :
      observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          1 firstBranch ≠
        observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          1 secondBranch := by
    rw [observed_at_spectral_eq_crystal_time_sample,
      observed_at_spectral_eq_crystal_time_sample]
    exact reflected_branches_time_one_separation hBreak
  let existsSeparation : ∃ time,
      observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          time firstBranch ≠
        observedAt (oneStepSpectralUpdate (reflectedModes z)) modalSumReadout
          time secondBranch :=
    ⟨1, hOne⟩
  simp only [separationTime, dif_pos existsSeparation]
  have hUpper : Nat.find existsSeparation ≤ 1 :=
    Nat.find_min' existsSeparation hOne
  have hNonzero : Nat.find existsSeparation ≠ 0 := by
    intro hAtZero
    have hSpec := Nat.find_spec existsSeparation
    rw [hAtZero] at hSpec
    exact hSpec hZero
  omega

#print axioms observed_at_spectral_eq_crystal_time_sample
#print axioms reflected_branch_separation_time_eq_one

end D5.S3.ObserverMemory.FourierFibers.TemporalReflectionSeparationTime
