# Encoding into a subset of a finite abelian carrier

## Abstract

A finite translate mixture gives a common CPTP encoder for Fourier character records.

**Theorem 1.1 (Restricted characters resolve the memory identity).**

Lean statement: `D5/S3/Quantum/PureState/FourierMemoryEncoder.sum_characterEffect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/FourierMemoryEncoder.sum_characterEffect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite abelian group G of order N and a nonempty subset A as the output basis. Each effect is the rank-one matrix of the corresponding restricted character, scaled by 1/N. Orthogonality of the character sums makes the effects sum to the identity on A.

**Theorem 1.2 (The translate encoder attains the prescribed profile score).**

Lean statement: `D5/S3/Quantum/PureState/FourierMemoryEncoder.character_encoder_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/FourierMemoryEncoder.character_encoder_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose dᵢ is the probability that i lies in A + z when z is drawn with weights b(z). The branch indexed by z sends coordinate a + z to a with coefficient √b(z)/√dₐ₊ᶻ on the positive support of d. The sum of the branch Grams is the projection onto that support. Completing the channel resets the complementary coordinates to a fixed basis state in A. The signal has zero amplitude on that complement.

Use tᵢ = √dᵢ rᵢ with rᵢ = c wherever dᵢ < 1. Every coordinate with dᵢ = 1 lies in each translate of positive weight, so the sum of the rᵢ on any such translate is the profile value. The Fourier phase of a translation is a single unit-modulus factor for each character. Thus after summing branches the restricted POVM gives the same score, the squared profile value divided by N, for each label. The historical novelty of this common encoder remains provisional.

## References

- Truth anchor: `D5/S3/Quantum/PureState/FourierMemoryEncoder.character_encoder_attains`
- Truth anchor: `D5/S3/Quantum/PureState/FourierMemoryEncoder.sum_characterEffect`
- Dependency: [D5/S3/Quantum/PureState/QuantumMemoryBudget](QuantumMemoryBudget.md)
