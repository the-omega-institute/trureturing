/- GID: D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct finite crystal modes are exactly reconstructible from an equally long scalar time window. -/

import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

/-!
A finite Bloch or spectral truncation is represented by modal multipliers and
hidden amplitudes.  Time samples are the corresponding power moments.  The
statement is finite-dimensional and does not construct an infinite Bloch bundle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

universe u

variable {K : Type u} [Field K]

/-- Scalar observation at a natural time after diagonal modal transport. -/
def crystalTimeSample {n : ℕ}
    (modes amplitudes : Fin n → K) (time : ℕ) : K :=
  ∑ mode : Fin n, amplitudes mode * modes mode ^ time

/-- The first `n` time observations of an `n`-mode truncation. -/
def firstCrystalTimeWindow {n : ℕ}
    (modes amplitudes : Fin n → K) : Fin n → K :=
  fun time => crystalTimeSample modes amplitudes time

/-- The first time window is exactly the Vandermonde moment readout. -/
theorem first_crystal_time_window_eq_moment_readout {n : ℕ}
    (modes amplitudes : Fin n → K) :
    firstCrystalTimeWindow modes amplitudes =
      finiteMomentReadout modes amplitudes := by
  funext time
  exact finite_moment_readout_apply modes amplitudes time |>.symm

/-- Pairwise distinct finite modes are reconstructed by the first matching
number of scalar time samples. -/
theorem first_crystal_time_window_injective
    {n : ℕ} {modes : Fin n → K} (hModes : Function.Injective modes) :
    Function.Injective (firstCrystalTimeWindow modes) := by
  intro left right hWindow
  apply finite_moment_readout_injective hModes
  rw [← first_crystal_time_window_eq_moment_readout,
    ← first_crystal_time_window_eq_moment_readout]
  exact hWindow

/-- Equal finite time traces force equal modal amplitudes under mode separation. -/
theorem finite_crystal_time_trace_eq_iff
    {n : ℕ} {modes : Fin n → K} (hModes : Function.Injective modes)
    {left right : Fin n → K} :
    firstCrystalTimeWindow modes left = firstCrystalTimeWindow modes right ↔
      left = right :=
  (first_crystal_time_window_injective hModes).eq_iff

#print axioms first_crystal_time_window_eq_moment_readout
#print axioms first_crystal_time_window_injective
#print axioms finite_crystal_time_trace_eq_iff

end D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
