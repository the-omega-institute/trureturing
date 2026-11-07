# Concentrating two paths on the original bipartition

## Abstract

Two actual B-ended paths concentrate on the complete original labelled bipartition with an exact six-vertex residual and a signed-Catalan shift.

**Theorem 1.1 (The actual graph move and its exact Catalan difference).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.actual_two_path_concentration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.actual_two_path_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite carrier is arbitrary. Its original disjoint independent parts A and B cover every vertex. ActualTwoPaths gives a complete adjacency correspondence with paths of orders 2p+1 and 2q+1 and the given induced graph on R. It fixes every R label and gives one original B endpoint of each path. A compiled path-colouring argument derives that the original A vertices occupy odd positions and the B vertices occupy even positions from independence, disjointness, and coverage. Both p and q are at least one.

The move isolates the last B vertex of the first path. Its remaining prefix has 2p vertices and is concatenated with the whole second path. The resulting path has 2p+2q+1 vertices. The new graph has the same full carrier and the same pointwise A and B labels. Its coordinates describe every edge, including the absence of edges between these path components and R; all R relations are unchanged.

Independent configurations of a disjoint graph sum decompose into pairs of actual configurations by disjoint union. Their cardinalities add, and the empty configurations remain included. Exact graph relabeling then transports the entire configuration families to the given original labels. Weighted partition sums multiply along this decomposition, so the arbitrary graph R contributes exactly once.

The residual keeps the first 2p-2 original vertices of the first path, the first 2q-2 original vertices of the second path, and every vertex of R. Its adjacency is the induced original adjacency. The embedding and the cardinality equation show that precisely six original vertices were removed; no residual vertices are added.

For every m at least the full original cardinality, Phi at m before the move minus Phi at m after the move equals Phi at m-3 on this actual residual. The proof applies the original path-series recurrence to the configuration factorization and extracts coefficients after multiplication by the integer Catalan series. The six-vertex cardinality equation supplies all natural-subtraction bounds, including the case m equal to the full cardinality.

The equality allows an arbitrary graph on R, including nonforests. Nonnegativity of the difference follows only when the actual induced residual is acyclic and every residual degree is at most two, by the finite-forest Catalan theorem. The statement includes empty tails when either parameter equals one, two empty tails when both equal one, empty R, original isolates, and arbitrary actual relabelings. It makes no global extremum or native-capacity assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.actual_two_path_concentration`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan](FiniteForestCatalan.md)
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional](PathCatalanFunctional.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling](../../../StatisticalMechanics/HardCore/PartitionRelabeling.md)
