# The geometric core of nuclear-norm additivity

## Abstract

A common contraction saturates a positive weighted pairing exactly when the normalized Gram matrices agree.

**Theorem 1.1 (Positive weights and a common contraction).**

Lean statement: `D5/S3/QuadraticForms/WeightedGramContraction.weighted_dual_saturation_iff_normalized_gram`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/WeightedGramContraction.weighted_dual_saturation_iff_normalized_gram` (`✓ std3`). ∎

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

This is the geometric dual-witness step of Lemma 4 in Eran Kopel's v2 additions supplied in the October 2026 correspondence. Let x and y be finite families of nonzero vectors in real inner product spaces E and F, where F is finite dimensional, and let every weight u be strictly positive. There is a continuous real linear map Z from F to E of operator norm at most one for which the sum of u times the inner products of x with Z(y) equals the sum of u times the products of their norms if and only if all pairwise inner products of the normalized x vectors equal the corresponding normalized y inner products.

In the forward direction, contractivity and Cauchy-Schwarz bound every summand. Strictly positive weights force equality in each summand, so Z maps each normalized y vector to the corresponding normalized x vector. Applying contractivity to both sums and differences of those unit vectors proves equality of their Gram matrices.

In the reverse direction, equality of the Gram matrices implies equality of norms of every pair of corresponding linear combinations. The synthesis map therefore descends through its kernel to an isometry on the span of y. Composing this isometry with orthogonal projection onto that span gives the required contraction. The argument allows repeated and linearly dependent vectors, different source and target dimensions, and an empty outcome type; there is no basis assumption.

This theorem concerns existence of a contraction attaining the weighted pairing. Identifying its optimized value with the actual real rectangular matrix trace norm requires an additional polar-factor or duality argument. This declaration alone is not the full nuclear-norm additivity lemma and does not prove Theorem 5's channel equality characterization.

## References

- Truth anchor: `D5/S3/QuadraticForms/WeightedGramContraction.weighted_dual_saturation_iff_normalized_gram`
