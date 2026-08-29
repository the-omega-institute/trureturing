# The Weak Prime Signal Completion Threshold

## Abstract

Weak prime signals separate exactly at exponent one half.

**Definition 1.1 (A weak prime signal is an amplitude times an inverse power).**

$$delta\left(c, alpha, p\right) = c\cdot p^{{-alpha}}$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weakPrimeSignal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signal attached to a prime is a fixed amplitude times the first-event mass at the given exponent. Naming the family keeps the energy sum, the threshold, and the degeneracy audit tied to one definition.

**Theorem 1.2 (Signal energy is the amplitude squared times the prime power sum).**

$$E\left(c, alpha\right) = c^{2} \sum_{p} p^{{-2alpha}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_quadratic_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the squared signal over the primes factors the amplitude out of the series, leaving the prime inverse-power sum at twice the exponent.

**Theorem 1.3 (Energy diverges exactly at and below one half).**

$$\neg Summable\left(energy\right) \Leftrightarrow alpha \le \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_energy_not_summable_iff_half_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero amplitude the energy series fails to converge precisely when the exponent is at most one half. The boundary value itself lies on the divergent side.

**Theorem 1.4 (The completion dichotomy at exponent one half).**

$$\left(P \perp Q \Leftrightarrow alpha \le \frac{1}{2}\right) \land \left(Equivalent\left(P, Q\right) \Leftrightarrow \frac{1}{2} < alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_completion_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the named signal dichotomy hypothesis, the two product laws are mutually singular exactly when the exponent is at most one half, and mutually absolutely continuous exactly when it exceeds one half.

The dichotomy hypothesis stands for the Kakutani product-measure criterion, which pinned mathlib does not provide; it is carried as an explicit named premise rather than assumed silently.

**Theorem 1.5 (A zero amplitude collapses the threshold).**

$$\forall alpha, delta\left(0, alpha, p\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.nonzero_amplitude_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With zero amplitude every signal vanishes and the energy converges for every exponent, so the nonzero-amplitude hypothesis cannot be dropped.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.nonzero_amplitude_is_necessary`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weakPrimeSignal`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_completion_dichotomy`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_energy_not_summable_iff_half_le`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold.weak_prime_signal_quadratic_energy`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold](../../Analytic/ZetaEntropyPlane/LocalEvidenceOrderThreshold.md)
