# Marginals of independent-word matrices

## Abstract

Single-site deletion traces on matrices supported on independent words.

**Theorem 1.1 (The common kernel of the deletion traces).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals.deletion_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals.deletion_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Words put a binary occupation at each vertex of a finite simple graph. An occupied edge in either index forces the matrix entry to vanish. All one-site deletion traces vanish exactly when agreement of the row and column bits at any vertex with a neighbor forces a zero entry, and at an isolated vertex the two entries with a common bit sum to zero.

A deletion trace adds the entries with equal deleted bits of zero and one. If the two words agree at a vertex and either word occupies a neighbor, the summand for common bit one is forbidden. If both words leave the neighbor empty, use its deletion equation after setting the original vertex to one. Setting both endpoints to one is then forbidden, so both summands for the original vertex vanish. Conversely the agreement and isolated-vertex conditions cancel every deletion equation.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals.deletion_kernel_iff`
