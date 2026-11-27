# The common-radius three-center Laurent obstruction

## Abstract

The common-radius three-center Laurent obstruction

**Theorem 1.1 (Weight transport and energy ratios force single-active private support).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_single_active`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_single_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three private coordinate blocks are relative to the coordinatewise majority center. Matching row exponents fixes the bits in each residual's own block, and closure forces those bits to be opposite its center. The common exact sphere radius rules out a missing private block.

The shared-row energies have ratios determined by the sums of squared weights on the private blocks. After factoring out the common Laurent shift, scale one block using weights one, two and four. The resulting moment identities give zero weighted variance, forcing exactly one active private coordinate in every nonzero shared row.

**Theorem 1.2 (Three nonzero closed residuals with matching exponents are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_false`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three-center support reduction gives the hypotheses of the single-active curvature theorem. Its signed square relations contradict nonzero residuals. The proof works with arbitrary real residual coefficients.

For common-radius pieces of the two-contact monomial kernel in Hong, Wu and Xia's Problem 2, this supplies the algebraic three-piece obstruction. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_false`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleMonomial.closed_triple_laurent_single_active`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference](CenterOutwardDifference.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature](CenterOutwardTripleCurvature.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge](CenterOutwardWeightGauge.md)
