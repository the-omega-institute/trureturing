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

Each support condition is necessary for this characterization of arbitrary complex matrices. On a single edge, set the row-column entries (01,00) and (11,10) to one and minus one, with all other entries zero. The two terms cancel when the first bit is deleted. Both entries have different second bits, so neither appears when the second bit is deleted. The row 11 is forbidden, all occupied columns are legal, and the nonzero entry at (01,00) has equal first bits. Transposing the matrix gives the corresponding example with legal rows and a forbidden column.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals.deletion_kernel_iff`
