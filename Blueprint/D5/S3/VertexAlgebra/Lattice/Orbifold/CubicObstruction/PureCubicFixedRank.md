# Fixed Ranks in a Cubic Coset

## Abstract

Three commuting cubic twists have fixed ranks summing to the ambient dimension when the twisting operator has zero cyclic norm.

**Theorem 1.1 (Sum of the three fixed ranks).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.fixed_rank_sum_of_commuting_cubics`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.fixed_rank_sum_of_commuting_cubics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be finite-dimensional over a field of characteristic zero. Let A and C be commuting endomorphisms of V with A^3=C^3=I and I+C+C^2=0. The sum of the fixed-space dimensions of A, AC, and AC^2 equals the dimension of V.

For each T among A, AC, and AC^2, its cube is I, so (I+T+T^2)/3 is the average onto its fixed space. The sum of these averages is I. The linear terms sum to A(I+C+C^2), and the quadratic terms sum to A^2(I+C^2+C^4). Both sums vanish since C^4=C. The trace formula for the order-three action gives the rank of each fixed space from the trace of its average.

**Theorem 1.2 (Fixed rank sixteen in dimension forty-eight).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.pure_cubic_fixed_ranks_eq_sixteen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.pure_cubic_fixed_ranks_eq_sixteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions, suppose V has dimension 48 and the fixed ranks of A, AC, and AC^2 each belong to the set {0,16}. Their sum is 48, so all three ranks are 16.

In the application to P48p, A represents a cubic from the SL2(23) factor and C a generator of the commuting C3 factor. Nebe, arXiv:1212.0865, Theorem 3.6, proof (B), describes these factors, and Proposition 4.8 supplies the allowed ranks for order-three lattice isometries. The operator relations and allowed ranks are premises of the rank calculation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.fixed_rank_sum_of_commuting_cubics`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank.pure_cubic_fixed_ranks_eq_sixteen`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate](../P48qFixedRankCertificate.md)
