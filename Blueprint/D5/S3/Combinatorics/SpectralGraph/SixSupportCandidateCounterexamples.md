# Divisor candidates do not determine the residual spectrum

## Abstract

The original failed sign rule and the entire persistent candidate-family rejection.

**Theorem 1.1 (The full unbounded repeated-minimum candidate family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.persistent_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.persistent_family` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every integer k>=1, a=6k, b=a, c=(a-1)(2a-1) is an endpoint-one point and d=9k=3a/2 divides the exact quartic constant and lies in (b,2a). Nevertheless F(d)<0 and d squared does not divide N-Dd. The linear coefficient test therefore rejects that candidate throughout the entire stated family. The cancellation is valid for every k>=1, and the remaining contradiction is exact reduction modulo three. This excludes one candidate family, not all window divisors or all fully distinct exponent triples.

**Theorem 1.2 (The original exact two-sign control).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.opposite_sign_control`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.opposite_sign_control` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

At the received repeated-exponent endpoint point (20,20,741), both 21 and 30 divide N and lie in the strict spectral window, with F(21)=1207587225600 and F(30)=-1257386661900. This consumed helper supplies the following full-surface refutation. The graph was already settled by the repeated-exponent theorem; no new graph nonintegrality family is asserted.

**Definition 1.3 (The original full-surface negativity proposal).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.uniform_negativity`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.uniform_negativity` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The proposed rule quantifies over every ordered integer minimum-four endpoint-one triple and every constant divisor in the strict spectral window. It requires the residual quartic value to be negative at every such divisor.

**Theorem 1.4 (Full-surface uniform negativity is false).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.refutation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.refutation` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The actual endpoint polynomial and divisor at the original control refute this universal sign rule. Its restriction to fully distinct integer endpoint points is not decided here. The full higher-prime Q3 and integer-point feasibility boundaries remain as received.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.opposite_sign_control`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.persistent_family`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.refutation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples.uniform_negativity`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointOneArithmetic](SixSupportEndpointOneArithmetic.md)
