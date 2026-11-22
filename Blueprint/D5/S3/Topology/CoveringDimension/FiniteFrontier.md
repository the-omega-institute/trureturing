# Finite frontiers and covering dimension

## Abstract

Finite frontiers and covering dimension

Covering dimension at most n means that every finite open cover has a finite open refinement of multiplicity at most n + 1.

**Theorem 1.1 (Finite frontiers give refinements of multiplicity two).**

Lean statement: `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_one_of_finiteFrontier`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_one_of_finiteFrontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a compact Hausdorff space have a basis of open neighborhoods with finite frontiers. Choose a finite subcover from these neighborhoods. Off the union of the frontiers, the membership patterns in the chosen neighborhoods give disjoint open cells. Pairwise disjoint neighborhoods of the frontier points complete the refinement.

**Theorem 1.2 (A nontrivial preconnected space with closed points has positive covering dimension).**

Lean statement: `D5/S3/Topology/CoveringDimension/FiniteFrontier.not_atMost_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CoveringDimension/FiniteFrontier.not_atMost_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complements of two distinct points form an open cover. A multiplicity-one refinement would contain a nonempty proper clopen member.

**Theorem 1.3 (Closed finite-to-one maps pull covering-dimension bounds back).**

Lean statement: `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_of_closedMap_finiteFibers`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_of_closedMap_finiteFibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a continuous closed map from a Hausdorff space to a compact space have finite fibers. Separate each fiber by disjoint open sets subordinate to the original cover. Closedness gives a base neighborhood whose entire preimage lies in those sets. Refine in the base, then split each pullback into the corresponding disjoint pieces.

## References

- Truth anchor: `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_of_closedMap_finiteFibers`
- Truth anchor: `D5/S3/Topology/CoveringDimension/FiniteFrontier.atMost_one_of_finiteFrontier`
- Truth anchor: `D5/S3/Topology/CoveringDimension/FiniteFrontier.not_atMost_zero`
