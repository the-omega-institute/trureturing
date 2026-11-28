# Attained rank-two orientation minimum

## Abstract

The exact attained orientation minimum on the complex rank-two two-mode CAR orbit.

The public source writes the physical orientation value as a constant plus two occupation contrasts and two within-block crossing costs. The weightedCost form uses the real Clifford coordinates of a rank-two projection, while planeCoordinates gives an explicit comparison plane.

**Theorem 1.1 (Coordinate normalization of a unit Plücker form).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_with_sixth_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_with_sixth_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

A unit Plücker coordinate with all Plücker relations has an orthonormal two-plane representation whose first vector has sixth coordinate zero and whose wedge is the original coordinate.

**Theorem 1.2 (Additive comparison cost).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.additiveCost_le_weightedCost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.additiveCost_le_weightedCost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For nonnegative mode weights and an orthonormal pair, additiveCost is at most weightedCost of its wedge.

**Theorem 1.3 (Comparison plane with signed occupations).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Every unit Plücker form satisfying the Plücker relations admits X₁, X₂, c₁, c₂ with nonnegative masses, X₁+X₂=1, c₁²+c₂²≤1, the two signed coordinates preserved, and scalar comparison cost no greater than the original weightedCost.

**Theorem 1.4 (Reduction of a physical projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_plane_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_plane_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For a Hermitian idempotent rank-two matrix and nonnegative mode weights, there is a comparison plane with the same two occupation contrasts and with scalar cost bounded by twice the physical crossing cost.

**Theorem 1.5 (Explicit comparison projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.planeProjection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.planeProjection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The planeProjection built from admissible X₁, X₂, c₁, c₂ is Hermitian, idempotent, and rank two. Its occupation contrasts are the prescribed square-root products, and its two crossing costs are X₁+c₁² and X₂+c₂² after the factor of two in the declaration.

**Theorem 1.6 (Scalar lower bound for every orientation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every complex rank-two orthogonal projection, orientationValue is bounded below by twoModeMinimum with the absolute field magnitudes |B₁| and |B₂|.

**Theorem 1.7 (Single-mode axis projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.axisProjection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.axisProjection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For either mode and any z with z²≤1, axisProjection is Hermitian, idempotent, rank two, has contrast z in the chosen mode and zero in the spectator mode, with the stated crossing costs.

**Theorem 1.8 (Axis value equals scalar quadratic).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.orientationValue_axisProjection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.orientationValue_axisProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Choosing favorableContrast for the signed field makes the orientationValue of an axis projection equal to the corresponding axisQuadratic with the absolute field magnitude.

**Theorem 1.9 (Explicit minimizing projection).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.minimizingProjection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.minimizingProjection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

With nonnegative A₁ and A₂, minimizingProjection is Hermitian, idempotent, and rank two. It has zero spectator contrast and zero spectator crossing cost, and its orientationValue equals twoModeMinimum with |B₁| and |B₂|.

**Theorem 1.10 (Attained exact minimum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_exact_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_exact_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The set of values attained by Hermitian idempotent rank-two matrices has least element twoModeMinimum C A₁ A₂ |B₁| |B₂|. The witness is minimizingProjection, and the lower-bound direction is rank_two_orientation_lower.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.additiveCost_le_weightedCost`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.axisProjection_spec`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.minimizingProjection_spec`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.orientationValue_axisProjection`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.planeProjection_spec`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_exact_minimum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_orientation_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.rank_two_plane_reduction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_reduction`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoModeRankTwoAttainedOrientation.wedge_with_sixth_zero`
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum](WuTwoLevelOrientationMinimum.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker](WuTwoModeCliffordPluecker.md)
