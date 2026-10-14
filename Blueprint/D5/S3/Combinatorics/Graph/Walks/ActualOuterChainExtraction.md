# Actual Route Inventories

## Abstract

Extract the literal intermediate route and its inventories from a supplied closed parent.

**Theorem 1.1 (Extract the Entire Outside Chain).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction.actual_closed_route_outer_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction.actual_closed_route_outer_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From a supplied linked route whose first and final pieces are kept distinct, the theorem constructs the complete walk between their adjacent endpoints. Its interior support is exactly the concatenated supports of the intermediate pieces. Both the support and edge permutations are earned for the same supplied reversed parent cycle, including the single closing seam. The intermediate route is not supplied as a factorization assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction.actual_closed_route_outer_chain`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
