/- GID: D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal modal multipliers leave a nonzero antisymmetric amplitude invisible at every observation time. -/

import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
import Mathlib.Data.Matrix.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.DegenerateModeHiddenFiber

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

/-- A two-mode system with an exact spectral degeneracy. -/
def degenerateModes (z : ℂ) : Fin 2 → ℂ :=
  ![z, z]

/-- Antisymmetric amplitude hidden by an equal-mode scalar readout. -/
def antisymmetricAmplitude : Fin 2 → ℂ :=
  ![1, -1]

/-- Exact degeneracy keeps the antisymmetric branch invisible at every time. -/
theorem antisymmetric_amplitude_invisible_all_times (z : ℂ) (time : ℕ) :
    crystalTimeSample (degenerateModes z) antisymmetricAmplitude time = 0 := by
  simp [crystalTimeSample, degenerateModes, antisymmetricAmplitude,
    Fin.sum_univ_two]

/-- The hidden amplitude is nonzero. -/
theorem antisymmetricAmplitude_ne_zero :
    antisymmetricAmplitude ≠ (0 : Fin 2 → ℂ) := by
  intro h
  have hAtZero := congrFun h (0 : Fin 2)
  norm_num [antisymmetricAmplitude] at hAtZero

/-- Even the entire natural-time trace is noninjective under exact degeneracy. -/
theorem all_time_trace_not_injective (z : ℂ) :
    ¬ Function.Injective
      (fun amplitudes : Fin 2 → ℂ =>
        fun time : ℕ => crystalTimeSample (degenerateModes z) amplitudes time) := by
  intro hInjective
  apply antisymmetricAmplitude_ne_zero
  apply hInjective
  funext time
  simpa using antisymmetric_amplitude_invisible_all_times z time

#print axioms antisymmetric_amplitude_invisible_all_times
#print axioms antisymmetricAmplitude_ne_zero
#print axioms all_time_trace_not_injective

end D5.S3.ObserverMemory.FourierFibers.DegenerateModeHiddenFiber
