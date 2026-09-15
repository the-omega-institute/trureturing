# A uniform error for a truncated Mobius sum

## Abstract

The error of the coprime Mobius certificate.

**Theorem 1.1 (The explicit divisor bound).**

Lean statement: `D5/S3/Weil/Mertens/CoprimeMobiusCertificateError.certificate_error`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CoprimeMobiusCertificateError.certificate_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a squarefree integer R greater than one, sum the absolute truncated Mobius kernel over every positive integer at most N that is coprime to R. Its difference from c(R) times N has absolute value at most twice the number of divisors of R times the sum of the absolute partial Mobius sums on consecutive divisor intervals. Here c(R) is the coprime density times the sum of those absolute partial sums weighted by the differences of reciprocal endpoints. The bound holds for every natural number N, including zero.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CoprimeMobiusCertificateError.certificate_error`
- Dependency: [D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz](../../Arith/Congruence/DivisorDifferenceGcdHeinz.md)
