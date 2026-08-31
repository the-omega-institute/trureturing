# Time-Ordered Prime Memory Cocycle

## Abstract

Fourier-timed prime events form an affine memory cocycle whose swap defect is prime curvature.

**Definition 1.1 (Timed prime memory event).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.TimedPrimeMemoryEvent`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.TimedPrimeMemoryEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local event stores a scalar factor, a base memory injection, a real frequency, and a real Fourier time. Prime channels are obtained by using logarithmic prime frequency.

**Definition 1.2 (Time-ordered memory cocycle).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedMemoryCocycle`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedMemoryCocycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The memory summary weights an earlier event by the stable powers of all later slots and by the scalar factors accumulated before later injections. It is normalized at zero initial memory and unit scalar input.

**Definition 1.3 (Chronological affine evolution).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedEvolution`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedEvolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The event list acts from left to right. The list head acts first, so list order is an operational chronology distinct from the real Fourier time stored in each event.

**Theorem 1.4 (Fourier time translation of an injection).**

$$\forall e, s: \mathbb{R}, \operatorname{timedInjection}(\operatorname{shiftTimedEvent}(s, e)) = \operatorname{timedInjection}(e) \cdot \operatorname{fourierPhase}(\operatorname{frequency}(e), s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timed_injection_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shifting the event time multiplies its effective injection by the Fourier character of the shift. This imports the additive time-character law without adding an arrow of time.

**Theorem 1.5 (Exact affine word action).**

$$\forall s: \mathbb{C}, L, x, \operatorname{timeOrderedEvolution}(s, L, x) = (s^{\lvert L \rvert} \cdot \operatorname{fst}(x) + \operatorname{timeOrderedMemoryCocycle}(s, L) \cdot \operatorname{snd}(x), \operatorname{timeOrderedScalarCocycle}(L) \cdot \operatorname{snd}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_evolution_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite chronological word acts by a stable power on initial memory, the time-ordered memory cocycle on scalar input, and the commutative scalar word on the scalar coordinate.

**Theorem 1.6 (Twisted cocycle law under concatenation).**

$$\begin{gathered}\forall s: \mathbb{C}, P, S:\\{}\operatorname{timeOrderedScalarCocycle}(\operatorname{append}(P, S)) = \operatorname{timeOrderedScalarCocycle}(P) \cdot \operatorname{timeOrderedScalarCocycle}(S) \land\\{}\operatorname{timeOrderedMemoryCocycle}(s, \operatorname{append}(P, S)) = s^{\lvert S \rvert} \cdot \operatorname{timeOrderedMemoryCocycle}(s, P) + \operatorname{timeOrderedMemoryCocycle}(s, S) \cdot \operatorname{timeOrderedScalarCocycle}(P) \land\\{}\forall x, \operatorname{timeOrderedEvolution}(s, \operatorname{append}(P, S), x) = \operatorname{timeOrderedEvolution}(s, S, \operatorname{timeOrderedEvolution}(s, P, x)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_cocycle_append_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar summaries multiply under list concatenation. Memory summaries obey the twisted law in which the suffix length transports the prefix memory by a stable power and the prefix scalar transports the suffix memory.

The full affine evolution of a concatenated list is the composition of the prefix evolution followed by the suffix evolution.

**Theorem 1.7 (Two-event chronology defect).**

$$\begin{gathered}\forall s: \mathbb{C}, P, Q, x:\\{}\operatorname{fst}(\operatorname{timeOrderedEvolution}(s, [P, Q], x)) - \operatorname{fst}(\operatorname{timeOrderedEvolution}(s, [Q, P], x)) = \operatorname{primeSwapCurvature}(s, \operatorname{timedInjection}(P), \operatorname{localFactor}(P), \operatorname{timedInjection}(Q), \operatorname{localFactor}(Q)) \cdot \operatorname{snd}(x) \land\\{}\operatorname{snd}(\operatorname{timeOrderedEvolution}(s, [P, Q], x)) = \operatorname{snd}(\operatorname{timeOrderedEvolution}(s, [Q, P], x)) \land\\{}\operatorname{timeOrderedMemoryCocycle}(s, [P, Q]) - \operatorname{timeOrderedMemoryCocycle}(s, [Q, P]) = \operatorname{primeSwapCurvature}(s, \operatorname{timedInjection}(P), \operatorname{localFactor}(P), \operatorname{timedInjection}(Q), \operatorname{localFactor}(Q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_two_event_swap_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing two timed events leaves the scalar coordinate unchanged. The memory-coordinate difference is exactly the gauge-invariant prime swap curvature evaluated on their Fourier-rotated injections.

**Theorem 1.8 (Residual chronology with independent event times).**

$$\begin{gathered}\operatorname{timeOrderedMemoryCocycle}(s, [\operatorname{residualTimedEvent}(r_{p}, v_{p}, f_{p}, t_{p}), \operatorname{residualTimedEvent}(r_{q}, v_{q}, f_{q}, t_{q})]) - \operatorname{timeOrderedMemoryCocycle}(s, [\operatorname{residualTimedEvent}(r_{q}, v_{q}, f_{q}, t_{q}), \operatorname{residualTimedEvent}(r_{p}, v_{p}, f_{p}, t_{p})])\\{}= \operatorname{stableResidualSwapCurvature}(s, r_{p}, r_{q}, \operatorname{phaseTwistedChannel}(f_{p}, t_{p}, v_{p}), \operatorname{phaseTwistedChannel}(f_{q}, t_{q}, v_{q})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timed_residual_two_event_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For residual local factors at possibly different Fourier times, the chronology defect is stable residual curvature evaluated on the two independently phase-rotated channels.

**Theorem 1.9 (Recovery of the common-time phase-twisted curvature).**

$$\begin{gathered}\operatorname{timeOrderedMemoryCocycle}(s, [\operatorname{residualTimedEvent}(r_{p}, v_{p}, f_{p}, t), \operatorname{residualTimedEvent}(r_{q}, v_{q}, f_{q}, t)]) - \operatorname{timeOrderedMemoryCocycle}(s, [\operatorname{residualTimedEvent}(r_{q}, v_{q}, f_{q}, t), \operatorname{residualTimedEvent}(r_{p}, v_{p}, f_{p}, t)])\\{}= \operatorname{phaseTwistedStableSwapCurvature}(s, r_{p}, r_{q}, v_{p}, v_{q}, f_{p}, f_{q}, t).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.common_time_residual_swap_recovers_phase_twisted_curvature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two event times coincide, the list-level chronology defect specializes exactly to the existing common-time phase-twisted stable swap curvature.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.TimedPrimeMemoryEvent`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.common_time_residual_swap_recovers_phase_twisted_curvature`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedEvolution`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timeOrderedMemoryCocycle`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_cocycle_append_laws`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_evolution_affine`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.time_ordered_two_event_swap_curvature`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timed_injection_shift`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle.timed_residual_two_event_swap`
- Dependency: [D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature](PhaseTwistedStableSwapCurvature.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow](PrimeFrequencyPhaseFlow.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature](PrimeSwapCurvature.md)
