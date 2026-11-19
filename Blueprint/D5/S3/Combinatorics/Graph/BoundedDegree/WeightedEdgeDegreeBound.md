# Weighted edge bounds for induced subgraphs

## Abstract

WeightedEdgeDegreeBound

**Theorem 1.1 (Edge weights bound the size of an induced bounded-degree set).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/WeightedEdgeDegreeBound.card_le_of_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/WeightedEdgeDegreeBound.card_le_of_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite vertex region, assign nonnegative weights to vertices, edges, and vertex slack. Each edge weight is at most the sum of its endpoint weights. At each vertex the incident edge weights and slack cover one unit plus its vertex weight times the degree limit.

For a selected set with the stated induced degree limit, sum the covering inequalities over selected vertices. An edge with two selected endpoints contributes twice. Its second contribution is bounded by the two endpoint weights and charged to the induced degree at each endpoint. The remaining edge weights and slack bound the cardinality.

Integer scaling lets a solver propose rational weights and lets Lean verify their inequalities exactly. In the nine-cube, the region can exclude a fixed cubic component and its neighbors, so the certificate bounds the number of vertices that can extend the component.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/WeightedEdgeDegreeBound.card_le_of_weights`
