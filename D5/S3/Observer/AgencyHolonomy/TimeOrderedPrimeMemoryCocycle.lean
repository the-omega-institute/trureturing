/- GID: D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourier-timed prime events form an affine memory cocycle whose swap defect is prime curvature. -/

import D5.S3.Observer.AgencyHolonomy.PhaseTwistedStableSwapCurvature
import D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature
import Mathlib.Tactic

/-!
# Time-ordered prime memory cocycle

A timed event carries a scalar local factor, a base memory injection, a real
frequency, and a real Fourier time.  Its effective injection is the base
injection rotated by `exp (-i * time * frequency)`.

A list records operational chronology.  Iterating the associated affine
updates gives an exact scalar word and an exact memory cocycle.  Concatenation
of event lists obeys the twisted law

`M(earlierWord ++ laterWord) = stable ^ laterWord.length * M(earlierWord)
  + M(laterWord) * Lambda(earlierWord)`.

Thus Fourier time and list chronology are distinct coordinates.  Fourier time
rotates each local injection; list order determines how later stable powers
and earlier scalar factors transport that injection.

For two events, reversing chronology leaves the scalar coordinate unchanged
and changes the memory coordinate by the previously formalized prime swap
curvature.  Residual events recover the phase-twisted stable residual
curvature, including the existing common-time specialization.

This file does not impose monotonicity of event times, construct a continuous
time-ordered exponential, prove a Magnus expansion, establish an arrow of
time, control an infinite prime family, dominate zero-side odd energy, locate
zeta zeros, or prove RH.
-/

/- Library-search audit trail (2026-08-31):
   * `PrimeFrequencyPhaseFlow` proves the Fourier character laws and scalar
     ordered-product collapse.
   * `PhaseTwistedStableSwapCurvature` proves uniform residual bounds after a
     common Fourier phase twist.
   * `PrimeSwapCurvature` supplies the gauge-invariant adjacent-swap defect.
   * Repository search found no existing owner of the exact list-level affine
     cocycle and append law formalized below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.PrimeSwapCurvature
open D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound
open D5.S3.Observer.AgencyHolonomy.PhaseTwistedStableSwapCurvature

noncomputable section

/-- One local memory event with an attached Fourier frequency and time.  Prime
channels are obtained by setting `frequency = log p`. -/
structure TimedPrimeMemoryEvent where
  localFactor : ℂ
  baseInjection : ℂ
  frequency : ℝ
  time : ℝ

/-- The Fourier-rotated injection actually seen by the memory update. -/
noncomputable def timedInjection (event : TimedPrimeMemoryEvent) : ℂ :=
  fourierPhase event.frequency event.time * event.baseInjection

/-- The affine update associated with one timed event. -/
noncomputable def timedPrimeUpdate
    (stable : ℂ) (event : TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) : ℂ × ℂ :=
  (stable * state.1 + timedInjection event * state.2,
    event.localFactor * state.2)

/-- The commutative scalar word carried by a chronological event list. -/
def timeOrderedScalarCocycle : List TimedPrimeMemoryEvent → ℂ
  | [] => 1
  | event :: events =>
      event.localFactor * timeOrderedScalarCocycle events

/-- The memory response of a chronological event list to unit scalar input and
zero initial memory. -/
noncomputable def timeOrderedMemoryCocycle
    (stable : ℂ) : List TimedPrimeMemoryEvent → ℂ
  | [] => 0
  | event :: events =>
      stable ^ events.length * timedInjection event +
        timeOrderedMemoryCocycle stable events * event.localFactor

/-- Apply the listed events from left to right.  The head event acts first. -/
noncomputable def timeOrderedEvolution
    (stable : ℂ) :
    List TimedPrimeMemoryEvent → (ℂ × ℂ) → (ℂ × ℂ)
  | [], state => state
  | event :: events, state =>
      timeOrderedEvolution stable events
        (timedPrimeUpdate stable event state)

/-- Shift the Fourier time attached to one event. -/
def shiftTimedEvent
    (shift : ℝ) (event : TimedPrimeMemoryEvent) :
    TimedPrimeMemoryEvent :=
  { event with time := event.time + shift }

/-- A natural-number address event whose frequency is the logarithm of the
address.  Prime addresses give the zeta frequency `log p`. -/
def logAddressTimedEvent
    (address : ℕ) (time : ℝ)
    (localFactor baseInjection : ℂ) : TimedPrimeMemoryEvent where
  localFactor := localFactor
  baseInjection := baseInjection
  frequency := Real.log (address : ℝ)
  time := time

/-- A residual event with local factor `1 + residual` and base injection
`residual * channel`. -/
def residualTimedEvent
    (residual channel : ℂ) (frequency time : ℝ) :
    TimedPrimeMemoryEvent where
  localFactor := 1 + residual
  baseInjection := residual * channel
  frequency := frequency
  time := time

/-- Fourier time translation multiplies the effective injection by the shift
character. -/
theorem timed_injection_shift
    (event : TimedPrimeMemoryEvent) (shift : ℝ) :
    timedInjection (shiftTimedEvent shift event) =
      timedInjection event * fourierPhase event.frequency shift := by
  have hTime :=
    (fourier_phase_character_laws
      event.frequency 0 event.time shift).2.1
  change
    fourierPhase event.frequency (event.time + shift) *
        event.baseInjection =
      (fourierPhase event.frequency event.time * event.baseInjection) *
        fourierPhase event.frequency shift
  rw [hTime]
  ring

/-- Logarithmic address events recover the existing address phase exactly. -/
theorem log_address_timed_injection
    (address : ℕ) (time : ℝ)
    (localFactor baseInjection : ℂ) :
    timedInjection
        (logAddressTimedEvent address time localFactor baseInjection) =
      logAddressPhase address time * baseInjection := by
  rfl

/-- Every finite chronological word acts by an affine upper-triangular law. -/
theorem time_ordered_evolution_affine
    (stable : ℂ) (events : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    timeOrderedEvolution stable events state =
      (stable ^ events.length * state.1 +
          timeOrderedMemoryCocycle stable events * state.2,
        timeOrderedScalarCocycle events * state.2) := by
  induction events generalizing state with
  | nil =>
      simp [timeOrderedEvolution, timeOrderedMemoryCocycle,
        timeOrderedScalarCocycle]
  | cons event events ih =>
      change
        timeOrderedEvolution stable events
            (timedPrimeUpdate stable event state) =
          (stable ^ (event :: events).length * state.1 +
              timeOrderedMemoryCocycle stable (event :: events) * state.2,
            timeOrderedScalarCocycle (event :: events) * state.2)
      rw [ih]
      apply Prod.ext
      · simp only [Prod.fst, timedPrimeUpdate,
          timeOrderedMemoryCocycle, timeOrderedScalarCocycle,
          List.length_cons]
        rw [pow_succ]
        ring
      · simp only [Prod.snd, timedPrimeUpdate,
          timeOrderedScalarCocycle]
        ring

private theorem time_ordered_scalar_cocycle_append
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedScalarCocycle (earlierWord ++ laterWord) =
      timeOrderedScalarCocycle earlierWord *
        timeOrderedScalarCocycle laterWord := by
  induction earlierWord with
  | nil => simp [timeOrderedScalarCocycle]
  | cons event earlierWord ih =>
      simp [timeOrderedScalarCocycle, ih, mul_assoc]

private theorem time_ordered_memory_cocycle_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedMemoryCocycle stable (earlierWord ++ laterWord) =
      stable ^ laterWord.length *
          timeOrderedMemoryCocycle stable earlierWord +
        timeOrderedMemoryCocycle stable laterWord *
          timeOrderedScalarCocycle earlierWord := by
  induction earlierWord with
  | nil =>
      simp [timeOrderedMemoryCocycle, timeOrderedScalarCocycle]
  | cons event earlierWord ih =>
      simp only [List.cons_append, timeOrderedMemoryCocycle,
        timeOrderedScalarCocycle, List.length_append]
      rw [ih, pow_add]
      ring

private theorem time_ordered_evolution_append
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    timeOrderedEvolution stable (earlierWord ++ laterWord) state =
      timeOrderedEvolution stable laterWord
        (timeOrderedEvolution stable earlierWord state) := by
  induction earlierWord generalizing state with
  | nil => rfl
  | cons event earlierWord ih =>
      change
        timeOrderedEvolution stable (earlierWord ++ laterWord)
            (timedPrimeUpdate stable event state) =
          timeOrderedEvolution stable laterWord
            (timeOrderedEvolution stable earlierWord
              (timedPrimeUpdate stable event state))
      exact ih (timedPrimeUpdate stable event state)

/--
The scalar and memory summaries obey exact append laws, and list concatenation
is represented by composition of the affine evolutions.  The memory identity
is the twisted cocycle law for chronology.
-/
theorem time_ordered_cocycle_append_laws
    (stable : ℂ)
    (earlierWord laterWord : List TimedPrimeMemoryEvent) :
    timeOrderedScalarCocycle (earlierWord ++ laterWord) =
        timeOrderedScalarCocycle earlierWord *
          timeOrderedScalarCocycle laterWord ∧
    timeOrderedMemoryCocycle stable (earlierWord ++ laterWord) =
        stable ^ laterWord.length *
            timeOrderedMemoryCocycle stable earlierWord +
          timeOrderedMemoryCocycle stable laterWord *
            timeOrderedScalarCocycle earlierWord ∧
    ∀ state : ℂ × ℂ,
      timeOrderedEvolution stable (earlierWord ++ laterWord) state =
        timeOrderedEvolution stable laterWord
          (timeOrderedEvolution stable earlierWord state) := by
  refine
    ⟨time_ordered_scalar_cocycle_append earlierWord laterWord, ?_, ?_⟩
  · exact time_ordered_memory_cocycle_append stable earlierWord laterWord
  · intro state
    exact time_ordered_evolution_append stable earlierWord laterWord state

/--
Reversing two timed events preserves the scalar output.  The memory difference
is exactly their prime swap curvature, both at arbitrary input and at the
unit-scalar cocycle level.
-/
theorem time_ordered_two_event_swap_curvature
    (stable : ℂ)
    (eventP eventQ : TimedPrimeMemoryEvent)
    (state : ℂ × ℂ) :
    (timeOrderedEvolution stable [eventP, eventQ] state).1 -
        (timeOrderedEvolution stable [eventQ, eventP] state).1 =
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor * state.2 ∧
    (timeOrderedEvolution stable [eventP, eventQ] state).2 =
        (timeOrderedEvolution stable [eventQ, eventP] state).2 ∧
    timeOrderedMemoryCocycle stable [eventP, eventQ] -
        timeOrderedMemoryCocycle stable [eventQ, eventP] =
      primeSwapCurvature stable
        (timedInjection eventP) eventP.localFactor
        (timedInjection eventQ) eventQ.localFactor := by
  constructor
  · simp [timeOrderedEvolution, timedPrimeUpdate, primeSwapCurvature]
    ring
  constructor
  · simp [timeOrderedEvolution, timedPrimeUpdate]
    ring
  · simp [timeOrderedMemoryCocycle, primeSwapCurvature]
    ring

/--
For residual events at possibly different Fourier times, the chronological
swap defect is stable residual curvature evaluated on independently rotated
channels.
-/
theorem timed_residual_two_event_swap
    (stable residualP residualQ channelP channelQ : ℂ)
    (frequencyP frequencyQ timeP timeQ : ℝ) :
    timeOrderedMemoryCocycle stable
        [residualTimedEvent residualP channelP frequencyP timeP,
          residualTimedEvent residualQ channelQ frequencyQ timeQ] -
      timeOrderedMemoryCocycle stable
        [residualTimedEvent residualQ channelQ frequencyQ timeQ,
          residualTimedEvent residualP channelP frequencyP timeP] =
      stableResidualSwapCurvature stable residualP residualQ
        (phaseTwistedChannel frequencyP timeP channelP)
        (phaseTwistedChannel frequencyQ timeQ channelQ) := by
  simp [timeOrderedMemoryCocycle, residualTimedEvent, timedInjection,
    stableResidualSwapCurvature, phaseTwistedChannel]
  ring

/-- Equal event times recover the existing common-time phase-twisted stable
curvature exactly. -/
theorem common_time_residual_swap_recovers_phase_twisted_curvature
    (stable residualP residualQ channelP channelQ : ℂ)
    (frequencyP frequencyQ time : ℝ) :
    timeOrderedMemoryCocycle stable
        [residualTimedEvent residualP channelP frequencyP time,
          residualTimedEvent residualQ channelQ frequencyQ time] -
      timeOrderedMemoryCocycle stable
        [residualTimedEvent residualQ channelQ frequencyQ time,
          residualTimedEvent residualP channelP frequencyP time] =
      phaseTwistedStableSwapCurvature stable residualP residualQ
        channelP channelQ frequencyP frequencyQ time := by
  simpa [phaseTwistedStableSwapCurvature] using
    timed_residual_two_event_swap stable residualP residualQ
      channelP channelQ frequencyP frequencyQ time time

#print axioms timed_injection_shift
#print axioms log_address_timed_injection
#print axioms time_ordered_evolution_affine
#print axioms time_ordered_cocycle_append_laws
#print axioms time_ordered_two_event_swap_curvature
#print axioms timed_residual_two_event_swap
#print axioms common_time_residual_swap_recovers_phase_twisted_curvature

end

end D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
