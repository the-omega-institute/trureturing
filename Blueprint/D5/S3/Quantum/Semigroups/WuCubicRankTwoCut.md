# Sharp rank-two occupation cut

## Abstract

Fixing even occupation and charge gives sharp lower bounds on both directed CAR cut weights.

**Theorem 1.1 (Lower bounds in both directions).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_ge_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_ge_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In a complex unitary frame, let a and b be the empty and full masses of columns 0 and 1. Write t = a+b−1 for the even occupation offset and g = a−b for the empty-minus-full charge. The weight from columns 0 and 1 to columns 2 and 3 is at least L₋ = 1+t²−g−2√(ab(1−a)(1−b)). The opposite direction is at least L₊ = 1+t²+g−2√(ab(1−a)(1−b)). Bounding the product of the even and odd minors gives the square-root term. Each L± is at least (1±g)²/2 + 3t²/2, which improves the one-parameter projection bound (1±g)²/2 strictly whenever t is nonzero.

**Theorem 1.2 (Simultaneous attainment).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_sqrt_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_sqrt_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every a,b ∈ [0,1], one unitary frame realizes those two masses and simultaneously attains L₋ and L₊ in their respective directions. Thus the two occupations, or equivalently the even offset and charge, can be fixed throughout the minimization.

**Theorem 1.3 (Reverse cubic penalty).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.reverseCubicPenalty_ge_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.reverseCubicPenalty_ge_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Write wⱼᵢ for the summed squared lowering amplitudes from column i to column j. For any monotone real tuple u₀ ≤ u₁ ≤ u₂ ≤ u₃, the reverse-edge sum ∑ᵢ<ⱼ wⱼᵢ(uⱼ−uᵢ)³ is at least (u₂−u₁)³ L₋. Every crossing edge has gap at least u₂−u₁, and each of the two within-pair terms is nonnegative.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_ge_sqrt`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.cutWeight_sqrt_attained`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.reverseCubicPenalty_ge_sqrt`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap](WuCubicDirectedOccupationCap.md)
