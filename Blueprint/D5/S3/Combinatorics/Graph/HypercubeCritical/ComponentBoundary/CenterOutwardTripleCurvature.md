# Curvature of closed residuals on single-active private coordinates

## Abstract

Curvature of closed residuals on single-active private coordinates

**Theorem 1.1 (A closed vector supported in a center-bit slice vanishes).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_eq_zero_of_fixed_center_bit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_eq_zero_of_fixed_center_bit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the flip of a nonzero support point across this coordinate, only the term in that coordinate can contribute. A nonzero coordinate weight and unit Huang edge sign force the value to vanish.

**Theorem 1.2 (A two-coordinate square relates the normalized residual values).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_single_active_edge_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_single_active_edge_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At two active private coordinates the closed residual equation reduces to two terms. Negative Huang square curvature makes their base-edge-normalized single-coordinate values equal.

**Theorem 1.3 (Three closed single-active residuals cannot cancel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_triple_single_active_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_triple_single_active_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one direction in each nonempty private block. For the three possible single-active rows, the closure relations and the pointwise sum force the normalized values to be pairwise opposite. They vanish, and the single-active support exhausts all remaining rows.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_eq_zero_of_fixed_center_bit`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_single_active_edge_relation`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardTripleCurvature.closed_triple_single_active_eq_zero`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference](CenterOutwardDifference.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge](CenterOutwardWeightGauge.md)
