# Deletion kernel and allowed words when three consecutive occupations are forbidden

## Abstract

Compare the one-site deletion kernel with the allowed word space for a ban on triples.

**Theorem 1.1 (Exact comparison).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison.triple_kernel_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison.triple_kernel_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an open chain of k plus three sites, allow the binary words with no three consecutive ones. Write T for the Tribonacci sequence with initial values 0, 1 and 1. The allowed Hilbert space has dimension T(k+5). The supported complex matrix kernel of all single-site deletion traces has dimension 4 times the sum of T(k+3) and T(k+2). The kernel dimension is strictly less than twice the word count.

Each triple window must have a zero. This condition is preserved by taking the tail, and with the first window checked it implies Tribonacci admissibility by induction. Conversely, every Tribonacci-admissible word has a zero in each triple window. The known count of Tribonacci names therefore gives the word count. The shifted Tribonacci sum satisfies the kernel recurrence and agrees at the first three lengths. The two recurrences at indices k+4 and k+5 and the positivity of T(k+1) give the strict inequality.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison.triple_kernel_exact`
- Dependency: [D5/S0/Tower/Tribonacci/Representation](../../../../S0/Tower/Tribonacci/Representation.md)
- Dependency: [D5/S0/Tower/Tribonacci/Values](../../../../S0/Tower/Tribonacci/Values.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension](BinaryDeletionDimension.md)
