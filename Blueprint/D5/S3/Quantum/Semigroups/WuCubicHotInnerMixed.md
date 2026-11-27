# One-mode mixed derivative for the Wu cubic deficit

## Abstract

The physical one-mode mixed derivative and Hermitian trace for the Wu cubic deficit.

For the equal-cap CAR specialization of Wu v1, Remark 3.15, equation (3.54), take exponent three and write u = exp(−β/3). The physical Gibbs weights are a = u³b and b(1+u³) = 1. The two diagonal entries of the scaled sandwiched input are v = u(1+by) and w = 1−ay, and its real coherence entry is √u k. With Gibbs density diag(a,b), the physical sandwiched input is b^(1/3) times this matrix V. Set z = k² on the physical locus.

**Theorem 1.1 (Mixed derivative at the scalar ray).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.hot_inner_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.hot_inner_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Fix 0 < u < 1 and b > 0 with the stated Gibbs relations, and set α = α₃*(β). Use the scalar extension of the deficit in real z. Differentiate in z at zero, then differentiate that function of y at zero. The derivative is −b(9a/4)(1+u)/(1−u) times [2(1−2α)+2(1−u)²/(1+u+u²)]. The gap w−v is positive near the base point, so the inner spectral derivatives there are obtained from the two characteristic roots. The cubic mass has zero y derivative at the base point, and the Gibbs logarithms retain both diagonal charges.

**Theorem 1.2 (Hermitian cubic logarithm trace).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For u ≥ 0 and arbitrary real a, b, k and y, the real part of the ordinary trace of V³ log(V³), with log given by continuous functional calculus, equals the sum of 3λ³ log λ over the two roots λ = (v+w ± √((w−v)²+4uk²))/2, counted with multiplicity.

**Theorem 1.3 (Scaled ordinary-trace deficit).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For u ≥ 0 and arbitrary real a, b, α, k and y, the scalar deficit at z = k² equals b[(9/8) E − α(S − T log T − d₀ log a − d₁ log b)]. Here S is the cubic logarithm trace, T is the real part of the ordinary trace of V³, and d₀ and d₁ are its real diagonal entries. The energy E is the real part of the ordinary trace of V²W, where W has diagonal entries 2uby and −2ay and the same coherence entry √u k. In the Gibbs normalization the scale logarithm cancels between the spectral logarithm and the mass normalization.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_deficit`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.embedded_spectral`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.hot_inner_mixed`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicConditionalTensorization](WuCubicConditionalTensorization.md)
