# Nested support and cancellation

## Abstract

Injectivity of the six-factor multiplier on nested-supported distributions.

**Definition 1.1 (A separate second-coordinate cutoff on each first-coordinate row).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.NestedSupport`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.NestedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A three-variable distribution has a uniform lower cutoff x>=-U. For each fixed x it has its own lower cutoff y>=-B(x), uniform over z. There is no z lower bound and no common y cutoff over all x.

**Theorem 1.2 (Cancellation of the exact six-factor multiplier).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.finalR_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.finalR_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any commutative complex algebra R, for all nonnegative k,A,C,D, multiplication by x^k y^k (x+y)^k (x+y+z)^A (y+z)^C z^D is injective between nested-supported coefficient distributions. The zero algebra and zero exponents are included.

The coordinate shifts and their finite sums preserve nested support. Cancellation of x+y uses the uniform x cutoff, while cancellation of y+z uses the current row's y cutoff. Both use supported_positive_reconstruction from SupportedChannelSeries on the corresponding legal bivariate row.

For x+y+z, strong induction on the nonnegative row index x+U first eliminates the preceding x row. The zero product recurrence then becomes the y+z recurrence on the current row. That row's own y cutoff makes positive reconstruction finite and proves that the entire row vanishes. This couples the row induction to bivariate reconstruction without strengthening the support hypotheses.

Iterating these cancellations removes each finite power; applying the resulting zero-kernel statement to F-G proves injectivity. This is a formal algebraic statement about distributions. It does not identify a vertex-algebra channel or assert analytic convergence or sewing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.NestedSupport`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.finalR_injective`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries](SupportedChannelSeries.md)
- Dependency: [D5/S3/VertexAlgebra/UniformGradedLocalCorrelator](../UniformGradedLocalCorrelator.md)
