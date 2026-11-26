# The prefix of a second arm

## Abstract

The next edge on the second arm is fresh in the two path disclosures.

**Theorem 1.1 (The next edge is absent from the disclosed path edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/FreshMeetingArm.fresh_edge_after_first_arm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FreshMeetingArm.fresh_edge_after_first_arm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two simple paths with the same start. If the first path has an edge, it starts with a different edge from the second. Every internal vertex of the second path lies outside the first path. The last vertex of the second path may lie on the first path.

For any strict prefix of the second path, the next edge appears neither on the first path nor in that prefix. The recorded edges consist of the edges traversed on the two paths through the end of the prefix.

At the common start a simple path uses only its first edge incident to that start. At a later step the departure vertex is outside the first path. Within the second path every edge is traversed at most once.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FreshMeetingArm.fresh_edge_after_first_arm`
