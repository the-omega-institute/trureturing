/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenTimedMemoryMagnusReadout
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: At the prime half beat, the golden second-Magnus readout is exactly a unit phase times twice the time-ordered memory swap curvature. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenPrimeBeatSecondMagnus
import D5.S3.Observer.MemoryChronology.TimeOrderedMemoryChronologySignatureBridge
import Mathlib.Tactic

/-!
# Golden half-beat readout of time-ordered memory chronology

A scalar product of the short and long golden Fourier letters is insensitive to
which letter came first. The time-ordered memory matrices carry a noncommuting
step-two logarithmic coordinate whose upper-right entry is the oriented swap
curvature. This file combines the two facts at the prime half-beat window.

The resulting scalar witness is the second-Magnus slot kernel multiplied by the
upper-right step-two logarithmic coordinate. Its exact value is

`2 * shortPhase * primeSwapCurvature`.

The short phase has unit norm, so the witness norm is exactly twice the
curvature norm. It is nonzero precisely whenever the supplied curvature is
nonzero, and exchanging the two timed events reverses its sign. This gives a
finite explicit instance of the principle that an abelian Fourier endpoint
forgets chronology while a noncommutative lift can retain it.

No infinite prime family, common beat time, continuous Magnus integral,
completed Hopf algebra, physical arrow of time, zeta-zero statement, or RH
claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenTimedMemoryMagnusReadout

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
open D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
open D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature
open D5.S3.Observer.MemoryChronology.TimeOrderedMemoryChronologySignatureBridge
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.GoldenPrimeCircle.GoldenPrimeBeatSecondMagnus

noncomputable section

/-- The commutative scalar endpoint of one short and one long golden frequency
letter. -/
def goldenScalarTwoStepEndpoint
    (prime : Nat.Primes) (time : ℝ) : ℂ :=
  orderedPhaseProduct
    [shortGoldenPrimeFrequency prime, longGoldenPrimeFrequency prime] time

/-- Swapping the two scalar Fourier letters leaves their final endpoint
unchanged. -/
theorem golden_scalar_two_step_endpoint_order_invisible
    (prime : Nat.Primes) (time : ℝ) :
    goldenScalarTwoStepEndpoint prime time =
      orderedPhaseProduct
        [longGoldenPrimeFrequency prime, shortGoldenPrimeFrequency prime]
        time := by
  simp [goldenScalarTwoStepEndpoint, orderedPhaseProduct, mul_comm]

/-- The half-beat second-Magnus coefficient multiplied by the oriented
upper-right step-two logarithmic coordinate of two timed memory events. -/
noncomputable def goldenTimedMemoryMagnusReadout
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) : ℂ :=
  secondMagnusSwapKernel
      (shortGoldenPrimeFrequency prime)
      (longGoldenPrimeFrequency prime)
      0 (goldenPrimeHalfBeatTime prime) *
    (doubledMagnusDegreeTwo
      (chronologicalSignature (timedMatrixObservation stable)
        [eventP, eventQ])) 0 1

/-- At the calibrated half beat, the complete chronology witness factors into
a unit short-channel phase, the universal factor two, and the frozen swap
curvature. -/
theorem golden_timed_memory_magnus_readout_factorization
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    goldenTimedMemoryMagnusReadout prime stable eventP eventQ =
      (2 : ℂ) *
        fourierPhase (shortGoldenPrimeFrequency prime)
          (goldenPrimeHalfBeatTime prime) *
        primeSwapCurvature stable
          (timedInjection eventP) eventP.localFactor
          (timedInjection eventQ) eventQ.localFactor := by
  unfold goldenTimedMemoryMagnusReadout
  rw [second_magnus_kernel_at_prime_half_beat,
    timed_matrix_two_event_doubled_magnus_upper_right]
  ring

/-- The half-beat witness has exactly twice the norm of the underlying memory
swap curvature. -/
theorem golden_timed_memory_magnus_readout_norm
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    ‖goldenTimedMemoryMagnusReadout prime stable eventP eventQ‖ =
      2 * ‖primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor‖ := by
  rw [golden_timed_memory_magnus_readout_factorization,
    norm_mul, norm_mul]
  have hPhaseNorm :
      ‖fourierPhase (shortGoldenPrimeFrequency prime)
          (goldenPrimeHalfBeatTime prime)‖ = 1 :=
    (fourier_phase_character_laws
      (shortGoldenPrimeFrequency prime) 0
      (goldenPrimeHalfBeatTime prime) 0).2.2.2.1
  rw [hPhaseNorm]
  norm_num

/-- Every nonzero time-ordered memory curvature is detected by the calibrated
golden half-beat witness. -/
theorem golden_timed_memory_magnus_readout_ne_zero
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent)
    (hCurvature :
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor ≠ 0) :
    goldenTimedMemoryMagnusReadout prime stable eventP eventQ ≠ 0 := by
  rw [golden_timed_memory_magnus_readout_factorization]
  have hPhase :
      fourierPhase (shortGoldenPrimeFrequency prime)
          (goldenPrimeHalfBeatTime prime) ≠ 0 := by
    simp [fourierPhase]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hPhase) hCurvature

/-- Exchanging the two timed events reverses the orientation of the calibrated
noncommutative chronology witness. -/
theorem golden_timed_memory_magnus_readout_swap
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent) :
    goldenTimedMemoryMagnusReadout prime stable eventQ eventP =
      -goldenTimedMemoryMagnusReadout prime stable eventP eventQ := by
  unfold goldenTimedMemoryMagnusReadout
  have hSwapEntry :
      (doubledMagnusDegreeTwo
          (chronologicalSignature (timedMatrixObservation stable)
            [eventQ, eventP])) 0 1 =
        -(doubledMagnusDegreeTwo
          (chronologicalSignature (timedMatrixObservation stable)
            [eventP, eventQ])) 0 1 := by
    simpa using congrArg (fun matrix => matrix 0 1)
      (timed_matrix_two_event_doubled_magnus_swap stable eventP eventQ)
  rw [hSwapEntry]
  ring

/-- Headline contrast: the scalar short/long endpoint is order-blind, while a
nonzero matrix-memory curvature yields a nonzero sign-oriented chronology
witness at the prime half beat. -/
theorem scalar_invisible_noncommutative_visible
    (prime : Nat.Primes) (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent)
    (hCurvature :
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor ≠ 0) :
    goldenScalarTwoStepEndpoint prime (goldenPrimeHalfBeatTime prime) =
        orderedPhaseProduct
          [longGoldenPrimeFrequency prime, shortGoldenPrimeFrequency prime]
          (goldenPrimeHalfBeatTime prime) ∧
      goldenTimedMemoryMagnusReadout prime stable eventP eventQ ≠ 0 ∧
      goldenTimedMemoryMagnusReadout prime stable eventQ eventP =
        -goldenTimedMemoryMagnusReadout prime stable eventP eventQ :=
  ⟨golden_scalar_two_step_endpoint_order_invisible
      prime (goldenPrimeHalfBeatTime prime),
    golden_timed_memory_magnus_readout_ne_zero
      prime stable eventP eventQ hCurvature,
    golden_timed_memory_magnus_readout_swap
      prime stable eventP eventQ⟩

#print axioms golden_scalar_two_step_endpoint_order_invisible
#print axioms golden_timed_memory_magnus_readout_factorization
#print axioms golden_timed_memory_magnus_readout_norm
#print axioms golden_timed_memory_magnus_readout_ne_zero
#print axioms golden_timed_memory_magnus_readout_swap
#print axioms scalar_invisible_noncommutative_visible

end

end D5.S3.Observer.GoldenPrimeCircle.GoldenTimedMemoryMagnusReadout
