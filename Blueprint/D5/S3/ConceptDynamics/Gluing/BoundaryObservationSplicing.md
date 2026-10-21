# Boundary Observation Splicing

## Abstract

Boundary-preserving partial splicing of dependent raw joins has an exact compatibility domain, a single-valued observation graph, and an exact reachable image.

A node component A carries a dependent rawJoin record on the union of its local scopes. For disjoint components A and B, overlapScope is the complete variable carrier shared by their scopes. The left and right overlap boundaries are the restrictions of the two records to this same carrier. The splice assignment uses the left value on the left scope and the right value elsewhere; agreement on the overlap makes this independent of the branch.

**Definition 1.1 (Shared component scope).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared variable carrier is U_A intersect U_B.

**Definition 1.2 (Left overlap restriction).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left record is restricted to U_A intersect U_B.

**Definition 1.3 (Right overlap restriction).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A right record is restricted to U_A intersect U_B.

**Definition 1.4 (Pointwise partial splice).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x in U_{A union B}, use a(x) when x is in U_A and b(x) otherwise. The latter branch is defined because every x in U_{A union B} lies in U_A or U_B.

**Theorem 1.5 (Unique compatible raw join).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For disjoint A and B, if the two complete overlap restrictions agree, the pointwise splice is a rawJoin record on A union B and is the unique rawJoin record with that value function. Empty local scopes and empty local relations remain allowed; the theorem is conditional on the displayed compatible pair.

**Theorem 1.6 (Transport of initial overlap compatibility).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_overlap_transport`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_overlap_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If equal local summaries preserve their corresponding complete overlap restrictions, an initially compatible pair remains compatible after both records are replaced. This is the boundary transport step used by the partial graph.

**Definition 1.7 (Partial observation graph).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph`

*Formalization.* `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph contains ((q_A(a),q_B(b)),q_C(a union b)) exactly for pairs whose complete overlap restrictions agree. Its domain is therefore a partial domain of summary pairs.

**Theorem 1.8 (Single-valued observation graph).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_single_valued`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_single_valued` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If equal left summaries preserve the left overlap, equal right summaries preserve the right overlap, and equal summary pairs preserve the union observation after the compatible splice, then the partial graph is single-valued on its summary domain. The hypotheses are explicit so no quotient lift or representative choice is hidden.

**Theorem 1.9 (Exact compatible summary domain).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_domain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph domain is exactly the set of pairs (q_A(a),q_B(b)) with representatives whose complete overlap restrictions agree. This is an equality of sets and does not require either component relation or value family to be nonempty.

**Theorem 1.10 (Exact reachable union image).**

Lean statement: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_range`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of the partial graph is exactly the set of q_C observations of compatible raw pairs. Thus every reachable union observation has two local witnesses, and every compatible pair contributes a reachable observation. No global representative-selection function is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_overlap_transport`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.compatible_splice_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryLeft`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapBoundaryRight`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.overlapScope`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceAssignment`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_domain`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_range`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.spliceGraph_single_valued`
- Dependency: [D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords](RunningIntersectionRecords.md)
