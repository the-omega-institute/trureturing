# Actual xi Taylor coefficients are folded moments

## Abstract

Actual xi Taylor coefficients are folded moments.

**Theorem 1.1 (Actual xi Taylor coefficients are folded moments).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary.actual_xi_taylor_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary.actual_xi_taylor_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex moment of order j is the complete sum of weight times node to power j over actual positive-height zero indices. Absolute weight summability and the bounded complex nodes justify every moment and the double geometric series. Its sum on norm(w) less than one quarter is the independently defined xiOdd(w).

The full scalar formal power series has zero even coefficients and moment j at coefficient 2j+1. The kernel-checked formal-power-series factorial identity identifies moment j with iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial, at every natural j. All even iterated derivatives vanish. The same full series proves analyticity throughout the disk. Conjugation of actual indices makes every moment real.

Let W be the complete sum of absolute weights and Lambda the supremum of the node norms with zero included. Lambda lies between zero and one. The moment norm is at most W times Lambda to power j. The coefficients are analytic data of the genuine xi expression; the moment interpretation is a proved identity, not a replacement definition of xi or its logarithmic derivative.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary.actual_xi_taylor_moment`
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiFoldedResolvent](ActualXiFoldedResolvent.md)
