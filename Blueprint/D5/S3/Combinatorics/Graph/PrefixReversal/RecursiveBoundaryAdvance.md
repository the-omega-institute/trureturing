# Exact Even and Odd Boundary Propagation

## Abstract

Exact Even and Odd Boundary Propagation.

**Theorem 1.1 (Earn the Next Even Endpoint Relation).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_even_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_even_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three, shifting both indices of every unaffected even boundary pair and replacing the affected whole path by the two new boundary pairs is exactly the even boundary relation at k+1. This is an equivalence of endpoint relations, not existence of walks.

**Theorem 1.2 (Earn the Next Odd Endpoint Relation).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_odd_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_odd_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three, the same explicit affected-path replacement and positive-index shift takes the odd boundary relation exactly to the odd boundary relation at k+1. The index zero cases are proved as part of the equivalence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_even_boundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.advance_odd_boundary`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary](RecursivePortBoundary.md)
