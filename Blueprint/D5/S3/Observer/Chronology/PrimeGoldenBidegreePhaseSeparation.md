# Prime-Golden Bidegree Phase Separation

## Abstract

One scalar Euler phase sample can alias bidegrees, while the complete time trajectory recovers the bidegree.

**Theorem 1.1 (A snapshot aliases and the complete phase trajectory separates).**

$$\begin{gathered}\forall p: Nat.Primes,\\{}\neg\operatorname{Injective}(d \mapsto \operatorname{bidegreePhase}(0, p, d)) \land\\{}\operatorname{Injective}(d \mapsto (t \mapsto \operatorname{bidegreePhase}(t, p, d))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation.prime_golden_phase_observation_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time zero every bidegree has unit phase, giving an explicit noninjective scalar sample.

For distinct bidegrees, the half-beat of their nonzero frequency difference sends the relative phase to minus one and separates them.

The full scalar trajectory therefore recovers the two count coordinates, while Magnus or Hopf data is still required for event order.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation.prime_golden_phase_observation_boundary`
- Dependency: [D5/S3/Observer/Chronology/PrimeGoldenBidegreeFrequencyRigidity](PrimeGoldenBidegreeFrequencyRigidity.md)
