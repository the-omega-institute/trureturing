# The four-level mixed three-distinguishability region

## Abstract

A guarded cubic decides membership in the mixed three-distinguishability region for every four-coordinate probability law.

**Theorem 1.1 (Exact membership on the closed simplex).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2000). *Convexity of the Joint Numerical Range*. DOI: [10.1137/s0895479898343516](https://doi.org/10.1137/s0895479898343516). URL: <https://doi.org/10.1137/s0895479898343516>.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Acknowledgement.* Ingemar Bengtsson, Åsa Ericsson, Marek Kuś, Wojciech Tadej, Karol Życzkowski (2004). *Birkhoff's polytope and unistochastic matrices, N = 3 and N = 4*. DOI: [10.1007/s00220-005-1392-8](https://doi.org/10.1007/s00220-005-1392-8). URL: <https://arxiv.org/abs/math/0402325v2>.

*Commentary.*

Let pᵢ ≥ 0 and Σᵢ pᵢ = 1. The predicate InRegion requires three positive semidefinite trace-one matrices with common diagonal p and pairwise zero products. It holds exactly when every pᵢ ≤ 1/3 and there is a real t with 0 < t ≤ 1, xᵢ = (1−2pᵢ)²t−(4pᵢ−1)² ≥ 0 for all i, and phaseCubic(p,t) = 0.

The cap is the diagonal bound from the projection WWᴴ for an isometry W with three columns of common squared moduli p. Gauge two columns as conjugates. For their real complementary plane with orthonormal axes c,e, the diagonal equations are cᵢ²+eᵢ² = qᵢ = 1−2pᵢ and s(cᵢ²−eᵢ²) = dᵢ = 4pᵢ−1, where s is the difference of the compressed eigenvalues. For s ≠ 0 put t = s². The numbers 2s cᵢeᵢ square to xᵢ, and their signed sum vanishes by orthogonality. If s = 0, p is uniform and t = 1 admits signed half-units with sum zero.

For A = x₀+x₁−x₂−x₃, the quartic (A²−4x₀x₁−4x₂x₃)²−64x₀x₁x₂x₃ is the product of the eight real signed sums of the square roots with the first sign fixed. A zero is therefore equivalent to actual real roots yᵢ with yᵢ² = xᵢ and Σᵢ yᵢ = 0, even when roots vanish. Substituting xᵢ = qᵢ²t−dᵢ² gives zero constant coefficient because Σᵢ dᵢ = 0. The quartic is t phaseCubic(p,t), so the division only uses the positive root range.

Given an admissible root, put s = √t and take cᵢ ≥ 0 with square (qᵢ+dᵢ/s)/2. Give eᵢ the sign of yᵢ and square (qᵢ−dᵢ/s)/2, taking the positive sign at zero. This choice yields 2s cᵢeᵢ = yᵢ, including zero roots. The sums of the squared coordinates are one, and the signed sum makes c·e = 0. Completing the pair over ℝ supplies the conjugate columns. The third column uses the c and e components in phase quadrature and the eigenvalues (1+s)/2 and (1−s)/2.

Korzekwa, Czachórski, Puchała and Życzkowski give the pure-state and repeated-column equivalence in Lemma 5 of arXiv:1812.09083v3. Lemma 6 gives pure replacement on the saturated cap. Section III.B and Appendix C study the four-dimensional region, and Appendix C.3 reports numerical tests on [p,p,p,1−3p] using Haagerup’s order-four procedure as presented by Rajchel, Gąsiorowski and Życzkowski in arXiv:1804.10715v2, Appendix A.

On the special line p(u) = (1−3u,1+u,1+u,1+u)/4, the matrix in Appendix C.2, Eq. (C37), is the type-I central ray of Bengtsson et al., arXiv:math/0402325v2, §IV, Eqs. (35)–(40), and Appendix C. Their phase equations require L = (1−3u)/(1+u) ≤ 1 on this line, excluding −1/9 ≤ u < 0. The uniform endpoint u = 0 has a Hadamard lift. This ray parameter u labels the law.

The product refutation in ThreeDistinguishabilityProductRefutation supplies a point in the region missed by every labelling of the product ansatz in Eq. (30). The cubic equivalence decides membership in both directions at every point of the simplex. As a topological corollary, the region is compact and closed. The equal-row-modulus equations cut out a closed subset of the compact complex Stiefel manifold of 4 × 3 isometries. The map taking the squared moduli of the first column is continuous and has image exactly the mixed region. This paragraph gives the compactness argument in prose.

**Theorem 1.2 (Mixed and pure witnesses).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_weighted_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_weighted_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2000). *Convexity of the Joint Numerical Range*. DOI: [10.1137/s0895479898343516](https://doi.org/10.1137/s0895479898343516). URL: <https://doi.org/10.1137/s0895479898343516>.

*Commentary.*

Pairwise orthogonality of the supports bounds the sum of their ranks by four. Each rank is at least one because the trace is one. After permuting the states, the first two are rank one and have orthogonal unit representatives. Gauge this pair simultaneously and replace the third state in its real complementary plane. The result is a complex isometry with the required common row moduli. The converse uses the three column projectors and gives the simplex equations from the squared moduli of any unit column.

**Theorem 1.3 (A common row gauge preserves the diagonal).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.pure_replacement_for_equal_moduli`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.pure_replacement_for_equal_moduli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2000). *Convexity of the Joint Numerical Range*. DOI: [10.1137/s0895479898343516](https://doi.org/10.1137/s0895479898343516). URL: <https://doi.org/10.1137/s0895479898343516>.

*Commentary.*

The two orthogonal pure columns have equal moduli on each row. Choose a common unit row phase to make their entries conjugate, using the identity where both entries vanish. Conjugate the remaining density by the same unit diagonal matrix. This preserves trace, positivity, diagonal and the two annihilations. After real compression, undo the gauge on the replacement. Its squared moduli are the original remaining diagonal, which can be arbitrary.

**Theorem 1.4 (Three pure columns from mixed witnesses).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.weighted_isometry_of_inRegion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.weighted_isometry_of_inRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extract two rank-one unit columns, apply equal-modulus replacement to the remaining density, and use orthogonality and the common diagonal to obtain the target isometry.

**Theorem 1.5 (Column projectors witness membership).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_of_weighted_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_of_weighted_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer products of the unit columns have trace one, use the prescribed diagonal, and have pairwise zero products because the column inner products vanish.

**Theorem 1.6 (A vertex with one zero weight).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.one_zero_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.one_zero_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At p = (0,1/3,1/3,1/3), t = 1 satisfies the cap and makes each radicand zero. Exact substitution gives phaseCubic(p,1) = 0. Any law in the region with a zero entry is a permutation of this law by normalization and the cap. Permuting coordinates transports the witnesses.

**Theorem 1.7 (A strictly sub-cap law excluded from the mixed region).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.infeasible_not_inRegion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.infeasible_not_inRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The law (19999,15001,12000,13000)/60000 is positive and normalized with every entry strictly below 1/3. Its cubic has strictly positive coefficients and hence no positive root. The weighted-column obstruction transfers to InRegion.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_weighted_isometry`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_of_weighted_isometry`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.infeasible_not_inRegion`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.one_zero_feasible`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.pure_replacement_for_equal_moduli`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.weighted_isometry_of_inRegion`
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic](ThreeDistinguishabilityCubic.md)
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation](ThreeDistinguishabilityProductRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityRealCompression](ThreeDistinguishabilityRealCompression.md)
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount](ThreeDistinguishabilitySupportCount.md)
