# Ungraded Local Word Series

## Abstract

Finite local words admit a common vector power series on all signed exponents.

Let V be a complex module and A a finite labelled family of actual VertexOperator maps. Labels are distinct even when their field values coincide. Choose a complete list with no repeated labels. Pairwise operator locality supplies a common order k independently of the input vector w. No energy, vacuum or weight is specified.

**Theorem 1.1 (A common native vector series with exact signed recovery).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.ungraded_local_word_common_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.ungraded_local_word_common_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The clearing polynomial Q is the product of (z_i-z_j)^k over all i<j, acting by finite convolution on the original signed coefficient distributions. The imported common_cleared_fields supplies their order independence and coordinate lower bounds on w. Each field has a nonnegative truncation cutoff a_i on this same input. The common series P has coefficient at native multi-index d equal to the cleared distribution at d-a.

For every permuted complete list and every signed exponent vector e, the cleared distribution at e-a equals P at the native multi-index e when all coordinates of e are nonnegative, and equals zero otherwise. The statement also gives the lower rectangle directly, uniformly in the remaining signed coordinates. The vector coefficients have no multiplication and P need not have finite support. Empty and singleton label types use the same construction.

This is an algebraic common-series representation. It assumes neither positivity nor homogeneity, and proves no analytic convergence, collision substitution, associator or sewing law. The construction reuses the graded supplier's word, clearing polynomial and finite convolution without changing its finite homogeneous numerator theorem.

Finite Laurent convolution and signed zero extension commute with linear vector readouts. These laws are consumed by the canonical charge-sector application. The classical locality suppliers retain Matsuo-Nagatomo and Carnahan attribution; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.ungraded_local_word_common_series`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator](../LatticeHalfFockChargedCollision/WeightedLocalCorrelator.md)
