# The universal linear lower estimate

## Abstract

The universal linear lower estimate

The no-low-path restriction supplies the local hypothesis of the boundary-counting estimate. Row and column degree sums are reused from the metric-independent Hamming incidence core.

**Theorem 1.1 (Edges equal landmarks).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.incidence_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.incidence_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every landmark set, the edge cardinality of its bipartite incidence graph equals its landmark cardinality, as follows by summing the original row and column degrees and applying the degree-sum formula.

**Theorem 1.2 (Tagged low-path obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.no_low_walk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.no_low_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least four, no three consecutive incidence edges can have all four vertex degrees two when the first and third vertices differ and the second and fourth differ. Bipartite tags reduce the statement to the rectangle-path obstruction.

**Theorem 1.3 (No adjacent low centers).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.low_middle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.low_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the degree-two induced incidence graph of a weak-four set, a vertex with two low neighbors cannot be adjacent to another vertex with two low neighbors. Otherwise choosing a second neighbor at each endpoint gives the forbidden low path.

**Theorem 1.4 (Universal minimum-degree-two estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.linear_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.linear_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four and every weak-four landmark set with all row and column degrees at least two, 24n is at most eleven times the landmark cardinality. This is the twelve-elevenths graph estimate applied to the 2n incidence vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.incidence_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.linear_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.low_middle`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.no_low_walk`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower](Lower.md)
