# BufferLayout

## Abstract

Stable partial matchings and the Mertens range-two probability estimate.

**Theorem 1.1 (occupied_iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every request map into the six buffer sites that avoids the central sites 2 and 3, occupied (flags request) i is true exactly when some old request lands at i. The complete_requests proof uses this equivalence.

**Definition 1.2 (occupied).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions.

**Definition 1.3 (mate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions.

**Theorem 1.4 (buffer_completion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions.

**Theorem 1.5 (complete_requests).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite clique with a distinguished vertex, a matching covers the whole clique when its size is even and the clique without that vertex when its size is odd. The free sites in each three-site half form such a clique containing its central vertex. Mathlib's finite-clique matching theorem pairs either the whole free clique or its center-deleted subset, according to parity. The two centers are paired when both are left single. The resulting involution fixes reserved sites, uses edges of length at most two, and leaves at most one central single. PaddedCompletion and CyclicClosure use these properties for their stable matching constructions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.buffer_completion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.complete_requests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.mate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/BufferLayout.occupied_iff`
