# Endpoint Pairs after Actual Joint Replacement

## Abstract

Actual replacement walks update the complete endpoint set by erasure and insertion.

The vertex type and simple graph are arbitrary. A Piece records its actual walk and both actual endpoints. Full support lists retain every vertex; Sym2 edges forget orientation. These generic statements supply the local slicing and endpoint steps used in recursive native graph surgery. They do not themselves assert a recursively constructed Hamilton cycle for all orders.

**Theorem 1.1 (Update the Exact Endpoint Pair Set).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs.actual_three_path_endpoint_update`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs.actual_three_path_endpoint_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual distinguished walk d from l to z and a list rest whose full supports concatenate without repetition, replace d by actual walks z to l0, r0 to l1 and r1 to l. The endpoint-pair set of these three walks followed by rest equals the old endpoint-pair set with {l,z} erased, union the three new pairs {z,l0}, {r0,l1} and {r1,l}. Support disjointness excludes {l,z} from rest, so erasure removes exactly the distinguished old pair. This result assumes no new pairing law and imposes no path or inventory condition on the three replacement walks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs.actual_three_path_endpoint_update`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
