# Squarefree integers with a coprimality condition

## Abstract

The density of squarefree integers coprime to a fixed modulus.

**Theorem 1.1 (An explicit square-root error).**

Lean statement: `D5/S3/Weil/Mertens/CoprimeSquarefreeDensity.squarefree_coprime_count_error`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CoprimeSquarefreeDensity.squarefree_coprime_count_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every squarefree positive integer Q and nonnegative real X, let S(Q,X) count the positive squarefree integers at most X that are coprime to Q. The density rho(Q) is the reciprocal of the sum of the inverse squares of the positive integers, multiplied by p/(p+1) over the prime divisors p of Q. The real zeta series at two is written as the sum of ((n+1)^2) inverse over natural numbers n starting at zero. The absolute difference between S(Q,X) and rho(Q) times X is at most (2 to the number of distinct prime divisors of Q, plus 2) times the square root of X. The density is classical.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CoprimeSquarefreeDensity.squarefree_coprime_count_error`
- Dependency: [D5/S3/Weil/Mertens/CoprimeMobiusCertificateError](CoprimeMobiusCertificateError.md)
