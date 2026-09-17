# Upper-half Prime Certificate Extension

## Abstract

Upper-half Prime Certificate Extension.

**Theorem 1.1 (The exact change of two absolute Mobius certificates).**

Lean statement: `D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension.certificate_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension.certificate_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a positive squarefree integer and N an integer at least two. Choose a finite set T of primes p with N less than twice p, p at most N, and p not dividing Q. Write R for their product, s for their number, and b for the Mobius sum over divisors of Q at most N. The certificate U sums absolute truncated kernels over all positive coprime indices at most N; W further restricts these indices to squarefree integers. Both differences, from support Q to support QR, equal s plus the absolute value of b minus the absolute value of (b minus s). This includes the empty set and Q equal to one. The new divisors in the window and the deleted coprime outer indices are exactly T. Every retained index other than one has the same truncated kernel.

## References

- Truth anchor: `D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension.certificate_extension`
- Dependency: [D5/S3/Weil/Mertens/CoprimeMobiusCertificateError](CoprimeMobiusCertificateError.md)
