# Independent Source Noise in a Quantum Triangle

## Abstract

Born distributions of three physically independent noisy bipartite sources.

**Theorem 1.1 (Positive normalized Born distribution and exact eight-term source expansion).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise.triangle_noise_distribution`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise.triangle_noise_distribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each edge has a signal density state and a background density state in the canonical finite DensityState carrier. An edge of visibility w is mixed as w times the signal plus (1-w) times the background before the three independent edge matrices are tensored.

LocalPOVM contains actual positive complex matrix effects whose sum is the identity. The six incident systems are reordered explicitly from source order AB, BC, CA to the cyclic party order A=(AB,CA), B=(BC,AB), C=(CA,BC). Each party jointly measures its two incident systems.

The distribution is the real part of the Born trace of that independent source tensor against the routed tensor of the three local effects. For each visibility in the closed unit interval the trace is nonnegative and the outcomes sum to one.

Bilinearity in each source matrix yields eight endpoint Born distributions. A true endpoint chooses that edge's signal and contributes its visibility; a false endpoint chooses its background and contributes one minus its visibility. The three edge weights multiply. This is physical independent source noise, with no assumption that the eight endpoint distributions are arbitrary tables or that global output noise has the same law.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise.triangle_noise_distribution`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
