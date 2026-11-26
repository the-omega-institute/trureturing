# Pure Fourier rim scores

## Abstract

The explicit rim potential has a cubic expansion with a uniform quartic remainder.

RawRim is the quaternion-valued rim potential with a positive square-root real fibre. PureEstimates is the conjunction of the scalar identities, radicand and unit-norm bounds, the pure score lower bound, and the linearization identities used to add the second Fourier mode.

**Theorem 1.1 (The pure-mode estimates).**

$$\operatorname{PureEstimates}\left(\operatorname{RawRim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore.pure_score_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the complex-pair score through degree three in the first Fourier amplitude. The constant score is one over the square root of three, the linear term vanishes, and the three quadratic terms coincide. Rationalization bounds the discarded terms in each quaternion factor. The product of their norm majorants bounds the tail of degree four and higher.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore.pure_score_estimates`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry](RoundQuaternionLocalGeometry.md)
