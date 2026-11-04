# Named Paths and Positive Duration

## Abstract

On a recurrent quiver, positive additive duration detects all rooted named paths exactly in the absence of branching.

**Theorem 1.1 (Recurrent branching is exactly the reconstruction obstruction).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.readout_injective_iff_no_branching`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.readout_injective_iff_no_branching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any quiver, let r be a fixed root, and assign a strictly positive real duration to every actual arrow. Suppose a finite path exists between every ordered pair of vertices. On the dependent sum of all finite paths starting at r, the pair consisting of endpoint and summed duration is injective if and only if, at every vertex a, the dependent sum of all arrows a to b over all targets b is a subsingleton. Arrows retain their names: parallel arrows are separate choices. Empty paths and empty return segments are included. No finiteness or rational independence is assumed.

For necessity, the return-block inventory below provides the specified collision and its consequent failure of injectivity. For sufficiency, unique outgoing arrows force the same first edge of two nonempty paths. Cancel its duration and induct on path length; positivity separates the empty path from every nonempty path. The one-vertex one-loop graph is included, as is the one-vertex graph with no arrows, whose only path is empty.

This is the structural no-branching intermediate of Theorem 3.1 in Recursive Relational Observation: Typed Residual Cocycles and Ordered-Path Reconstruction. The theorem operates directly on actual quiver paths. The finite nonempty-edge hypothesis needed to turn unique outgoing arrows into an exhaustive single-cycle enumeration, the explicit lap-and-suffix reconstruction formula, and the lifting of such paths to concrete typed source executions remain separate obligations. The result supplies no physical clock realization, finite-precision algorithm, resource bound or whole-source closure.

**Theorem 1.2 (Specified outgoing arrows give exchanged return blocks).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.branching_collision_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.branching_collision_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the vertex type and arrow universe be independent, fix a root r, and suppose every ordered vertex pair is joined by a finite path. Fix a vertex z and two unequal actual outgoing-arrow-and-target pairs a and b at z. For any real arrow-duration assignment, there exist an actual prefix p from r to z and actual return segments A from the target of a to z and B from the target of b to z. Either return segment may be empty. The blocks U formed by a followed by A and W formed by b followed by B are paths from z to z of positive length. Their ordered edge words are the actual named arrow a followed by the edge word of A, and the actual named arrow b followed by the edge word of B; these first named arrows differ, including when a and b are parallel.

The particular paths p followed by U then W and p followed by W then U are legal paths from r to z and are distinct after cancellation of the common prefix p. The first duration is exactly duration(p) plus duration(U) plus duration(W); the second is exactly duration(p) plus duration(W) plus duration(U). Thus these two actual paths have the same endpoint-duration readout, and the rooted readout is not injective. This inventory uses additivity and commutative real addition, without requiring positive clocks. The reconstruction equivalence uses its noninjectivity conclusion for necessity and retains positivity for decoding. The inventory has no instance on an edgeless singleton because its hypothesis requires two unequal outgoing arrows.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.branching_collision_inventory`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/NamedPathDurationReconstruction.readout_injective_iff_no_branching`
