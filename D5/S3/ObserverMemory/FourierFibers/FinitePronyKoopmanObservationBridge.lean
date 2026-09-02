/- GID: D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Prony moments and shifted Hankel entries are exactly the existing diagonal spectral-fiber observations and delay coordinates. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil
import D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

/-!
# Finite Prony to Koopman-style observation bridge

The repository already owns diagonal spectral-fiber transport and scalar time
samples. The Prony development owns the same finite exponential moments from
the rational-transfer and Hankel side. This module identifies the two without
introducing a second dynamics or delay-coordinate API.

A Prony moment is a crystal time sample. Shifted Prony weights are the existing
spectral-fiber transport. Every shifted Hankel entry is therefore a scalar
observation of the transported hidden state at a row-plus-column delay. Under
mode separation, the first matching moment window is injective by the existing
Vandermonde observation theorem.

This finite bridge does not construct an infinite Koopman operator, a continuous
spectral measure, or noisy delay-coordinate convergence.
-/

/- Library-search audit trail (2026-09-03):
   * `FiniteCrystalTimeFrequencyBridge` already owns `crystalTimeSample` and
     finite delay-window injectivity.
   * `TimeShiftSpectralFiberTransport` already owns diagonal modal transport and
     the time-translation law.
   * The Prony owners added in this branch supply the rational, recurrence,
     shifted-Hankel, rank, and matrix-pencil views. The statements below are
     conservative bridge equalities between these existing owners. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.FinitePronyKoopmanObservationBridge

open D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
open D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

/-- A finite Prony moment is exactly the scalar observation of diagonal modal
transport at the same natural time. -/
@[simp]
theorem finite_prony_moment_eq_crystal_time_sample {m : ℕ}
    (nodes weights : Fin m → ℂ) (time : ℕ) :
    finitePronyMoment nodes weights time =
      crystalTimeSample nodes weights time := by
  rfl

/-- The shifted modal weights in the Hankel factorization are exactly the
repository's spectral-fiber transport. -/
@[simp]
theorem finite_prony_shifted_weights_eq_spectral_fiber_transport {m : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ) :
    finitePronyShiftedWeights nodes weights shift =
      spectralFiberTransport nodes shift weights := by
  rfl

/-- Every shifted Hankel entry is a delay-coordinate observation of the hidden
state after the corresponding spectral-fiber transport. -/
theorem finite_prony_shifted_hankel_entry_eq_transported_sample {m n : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ)
    (row column : Fin n) :
    finitePronyShiftedHankel (n := n) nodes weights shift row column =
      crystalTimeSample nodes
        (spectralFiberTransport nodes shift weights)
        ((row : ℕ) + (column : ℕ)) := by
  rw [crystal_time_sample_after_transport]
  simp [finitePronyShiftedHankel, finitePronyMoment,
    crystalTimeSample, Nat.add_assoc]

/-- The first matching Prony moment window is the existing first crystal time
window. -/
theorem finite_prony_first_window_eq_crystal_time_window {m : ℕ}
    (nodes weights : Fin m → ℂ) :
    (fun time : Fin m =>
      finitePronyMoment nodes weights (time : ℕ)) =
      firstCrystalTimeWindow nodes weights := by
  rfl

/-- Distinct modal nodes make the first matching Prony moment window a faithful
finite Koopman-style delay embedding of the hidden amplitudes. -/
theorem finite_prony_first_window_injective {m : ℕ}
    {nodes : Fin m → ℂ} (hNodes : Function.Injective nodes) :
    Function.Injective
      (fun weights : Fin m → ℂ =>
        fun time : Fin m =>
          finitePronyMoment nodes weights (time : ℕ)) := by
  change Function.Injective (firstCrystalTimeWindow nodes)
  exact first_crystal_time_window_injective hNodes

/-- The complete finite observation bridge: moments are time samples, shifts
are diagonal spectral transport, Hankel entries are transported delay
coordinates, and separated modes give a faithful first window. -/
theorem finite_prony_koopman_observation_package {m : ℕ}
    {nodes : Fin m → ℂ} (weights : Fin m → ℂ)
    (hNodes : Function.Injective nodes) :
    (∀ time : ℕ,
      finitePronyMoment nodes weights time =
        crystalTimeSample nodes weights time) ∧
    (∀ shift : ℕ,
      finitePronyShiftedWeights nodes weights shift =
        spectralFiberTransport nodes shift weights) ∧
    Function.Injective
      (fun amplitudes : Fin m → ℂ =>
        fun time : Fin m =>
          finitePronyMoment nodes amplitudes (time : ℕ)) :=
  ⟨finite_prony_moment_eq_crystal_time_sample nodes weights,
    finite_prony_shifted_weights_eq_spectral_fiber_transport nodes weights,
    finite_prony_first_window_injective hNodes⟩

#print axioms finite_prony_moment_eq_crystal_time_sample
#print axioms finite_prony_shifted_weights_eq_spectral_fiber_transport
#print axioms finite_prony_shifted_hankel_entry_eq_transported_sample
#print axioms finite_prony_first_window_eq_crystal_time_window
#print axioms finite_prony_first_window_injective
#print axioms finite_prony_koopman_observation_package

end D5.S3.ObserverMemory.FourierFibers.FinitePronyKoopmanObservationBridge
