# A uniform forward degree bound

## Abstract

A uniform forward degree bound.

**Theorem 1.1 (A uniform forward degree bound).**

Lean statement: `D5/S3/Topology/WeavingReferenceDegree.orderedGraph_forward_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingReferenceDegree.orderedGraph_forward_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every interval-circle vertex meets only four possible crossing labels. Distinct incident edges yield distinct neighbors, so its full degree is at most four, including connectors to outer hubs. Hubs are independent. Order all interval vertices before the hubs, using the explicit finite equivalence supplied by the uniform-circle classification. An interval vertex then has at most four later neighbors, while a hub has no later neighbors. This proves a bound on forward degree; no bound on the full degree of a hub is asserted.

## References

- Truth anchor: `D5/S3/Topology/WeavingReferenceDegree.orderedGraph_forward_degree`
- Dependency: [D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate](../Combinatorics/Graph/Polynomials/CyclicRankEstimate.md)
- Dependency: [D5/S3/Topology/WeavingReferenceIncidence](WeavingReferenceIncidence.md)
