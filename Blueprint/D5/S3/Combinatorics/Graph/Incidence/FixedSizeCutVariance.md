# Variance of fixed-size weighted cuts

## Abstract

The variance of a uniformly sampled fixed-size weighted cut has two incidence contributions.

**Theorem 1.1 (The degree and zero-degree contributions).**

$$\operatorname{Var}(C) = \frac{m \cdot (n - m) \cdot (n - 2 \cdot m)^{2}}{n \cdot (n - 1) \cdot (n - 2)} \cdot \sum_{i<j} (u(i) + u(j))^{2} + \frac{4 \cdot m \cdot (m - 1) \cdot (n - m) \cdot (n - m - 1)}{n \cdot (n - 1) \cdot (n - 2) \cdot (n - 3)} \cdot \sum_{i<j} z(i,j)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/FixedSizeCutVariance.fixed_size_cut_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite vertex set of size n at least four and an integer m from two to n minus two. Each unordered edge receives an arbitrary real weight w. The sampled side S is uniform over the m-element subsets. The cut weight C is the sum over edges with exactly one endpoint in S.

Subtract the mean edge weight from each edge to get centered weights. For vertex i, let u(i) be the sum of its incident centered weights divided by n minus two. The residual z on edge {i,j} is its centered weight minus u(i) and u(j). The sum of the incident residual weights is zero at each vertex. Both sums in the formula range over unordered edges.

The two crossing indicators have different joint probabilities according to whether the edges coincide, meet at one vertex, or are disjoint. Counting the permitted placements of their endpoints gives the covariance in terms of unsigned incidence. Constants shift the cut by the same amount for every S. The remaining degree and residual weights are orthogonal, and their covariance contributions have the displayed coefficients.

When the two sides have equal size, the degree coefficient vanishes. The residual coefficient remains positive throughout the stated interval.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/FixedSizeCutVariance.fixed_size_cut_variance`
