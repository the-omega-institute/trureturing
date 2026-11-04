# InfiniteGaussianRows

## Abstract

InfiniteGaussianRows

Fixing an external occupation selects a square-summable slice of the joint factorial Gaussian norm. Pairing two such slices gives an absolutely convergent internal contraction.

**Theorem 1.1 (Every fixed external row is in factorial l2).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.row_square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.row_square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing InfiniteGaussianFock.Data.occupation_summable theorem to the actual scaled joint block. Restrict the nonnegative joint sum to the injection n maps to (d,n). Its factorial weight is d!n!, and exact diagonal congruence contributes abs(t^degree(d))^2. Both external factors are strictly positive, so cancelling them proves sum_n n! abs(c_K(d,n))^2 is finite. The scale can be chosen independently for each block because the resulting row estimate concerns the original unscaled coefficients.

**Theorem 1.2 (Absolute internal sewing convergence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.contraction_norm_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.contraction_norm_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of finite external occupations, use the two actual row square sums and the inequality ab <= (a^2+b^2)/2. This proves summability of abs(n! c_K1(d,n)c_K2(n,e)). No positivity, commutation, nonzero normalization, full joint smallness or supplied convergence hypothesis is required.

**Theorem 1.3 (The whole coordinate support net).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.cutoff_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.cutoff_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F ranging over all finite internal coordinate sets, retain all occupations supported in F, with no degree cutoff. Every fixed occupation is eventually retained, and the proved absolute series dominates every cutoff. Dominated convergence identifies the cutoff limit with the whole native contraction. Empty internal and external types are retained.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.contraction_norm_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.cutoff_tendsto`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.row_square_summable`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling](GaussianCoefficientScaling.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock](GaussianExternalBlock.md)
