# Small mixed graph inequality

## Abstract

Every finite properly three-colored simple graph whose mixed vertices all have degree two and whose mixed population has size between two and five has reciprocal deletion potential at least two.

**Theorem 1.1 (Actual graph theorem).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorSmallMixed.small_mixed_graph_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorSmallMixed.small_mixed_graph_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite simple graph with a proper coloring by Fin 3, assume every mixed vertex has degree exactly two and that the mixed vertex count lies between two and five. Then ColoredReciprocalDeletion.potential is at least two. Isolates and empty color classes are allowed, and there is no bound on the ordinary populations or graph size.

The proof deletes isolates only in the accounting argument, transfers the mixed populations to the finite-set incidence API, applies the substantive small_population_bound certificate, and restores the isolated vertices with the reciprocal monotonicity estimate. The public theorem has only graph, coloring, degree, and mixed-count hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorSmallMixed.small_mixed_graph_potential`
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorSmallMixedCore](ThreeColorSmallMixedCore.md)
