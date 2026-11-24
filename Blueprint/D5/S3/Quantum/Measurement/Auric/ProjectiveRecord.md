# The coherent record of a complete projective measurement

## Abstract

The coherent record of a complete projective measurement

**Theorem 1.1 (The joint state and its actual marginals).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/ProjectiveRecord.coherent_projective_record`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/ProjectiveRecord.coherent_projective_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For a complete finite PVM (E_j), set Wψ = Σ_j E_jψ ⊗ |j⟩ and ω = WρW†. Orthogonality and completeness give W†W = I. The system marginal is Πρ = Σ_j E_jρE_j. The record marginal is diag(q), with q_j = Re Tr(E_jρ). The joint entropy equals S(ρ). If G = S(Πρ) − S(ρ), then I(S:R) = H(q) + G and S(R|S) = −G.

Watrous Corollary 2.27 locates the finite-dimensional channel dilation. Proposition 5.19 supplies isometric entropy invariance, including singular states. The marginal calculation here uses the actual orthogonal projectors and the same joint state throughout.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/ProjectiveRecord.coherent_projective_record`
- Dependency: [D5/S3/Quantum/Decoherence/NonselectiveMarginalization](../../Decoherence/NonselectiveMarginalization.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](CoordinatePinching.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport](ProjectionSpectralTransport.md)
