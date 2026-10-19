# Universal Ky Fan upper bound

## Abstract

Universal square-root bounds for real symmetric zero-one matrices.

**Theorem 1.1 (Truncation at the matrix dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_eq_of_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_eq_of_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

Every singular value with index at least the matrix dimension vanishes. Hence extending a Ky Fan prefix beyond that dimension does not change its sum. The cited source supplies the singular-value machinery.

**Theorem 1.2 (Square-root upper bound).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_le_of_zero_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_le_of_zero_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Acknowledgement.* Vladimir Nikiforov (2015). *Extrema of graph eigenvalues*. URL: <https://arxiv.org/abs/1502.00359v1>.

*Commentary.*

The rectangular source supplies the variational machinery. Nikiforov's bound (12) gives the known graph bound, where the adjacency matrix has zero diagonal. The centering argument here extends that bound to symmetric zero-one matrices with arbitrary diagonal. For a symmetric zero-one matrix A of order n, every Ky Fan prefix of length k is at most n times (1+sqrt(k))/2. Centering gives B=2A-J, with all entries of B equal to plus or minus one. An attaining signed orthonormal family pairs with B by at most sqrt(k) times n, using Cauchy-Schwarz and Bessel's inequality on the rows. Its pairing with J is at most n by Bessel's inequality on the constant vector. Summing these bounds proves the result; prefixes longer than n reduce by truncation. Diagonal entries equal to one are allowed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_eq_of_ge`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Upper.kyFan_le_of_zero_one`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/SignedVariational](SignedVariational.md)
