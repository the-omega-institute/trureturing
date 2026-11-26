# Wu's cubic deficit over all complex frames

## Abstract

The ordinary two-mode Wu cubic inequality has a uniform positive margin at a fixed spectrum.

**Theorem 1.1 (A strict bound at the specified temperature and spectrum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicSpectralCertificate.matrix_level_Wu_cubic_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicSpectralCertificate.matrix_level_Wu_cubic_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let ρ be any positive definite complex four-by-four matrix of ordinary trace one with ascending spectrum (262144, 531441, 551368, 1030301)/2375254. Set h = 3 log(9/8), a = exp(−h)/(2 cosh h), b = exp(h)/(2 cosh h), and D = diag(a², ab, ab, b²) in the occupation basis 00, 01, 10, 11.

Use Wu v1 (2.4) and (3.54) with the two fermionic lowering jumps Jₖ and L(X) = ∑ₖ [2a K(Jₖ,X) + 2b K(Jₖ†,X)], where K(V,X) = ((V†V)X + X(V†V))/2 − V†XV. Write G = D^(1/6), X = D^(−1/6)ρ^(1/3)D^(−1/6), and M = GXG. Then E₃ = (9/8) Re Tr(M² G L(X) G) and H = Re Tr(ρ (log ρ − log D)).

With α₃ = (9/2) sinh(h/3) sinh(2h/3)/(2h sinh h) from Wu v1 (3.55), the normalized deficit (4 cosh(h)/9)(E₃ − α₃ H) is strictly greater than 1/8000.

The spectral expansion of the generator trace gives the directed cubic energy. The Gibbs logarithm gives the entropy as an affine function of Tr(ρ(N − I)). In the same complex eigenframe, the canonical anticommutation relations and the even occupation probabilities supply the hypotheses of the scalar occupation envelope.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicSpectralCertificate.matrix_level_Wu_cubic_lower_bound`
- Dependency: [D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison](TwistedTwoModeOUComparison.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope](WuCubicOccupationEnvelope.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointPauliFrame](WuEndpointPauliFrame.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuModularEdgeSpectral](WuModularEdgeSpectral.md)
