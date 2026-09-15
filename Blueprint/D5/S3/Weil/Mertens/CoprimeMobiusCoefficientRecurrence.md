# Prime extension and same-sign overlap

## Abstract

The coprime Mobius coefficient under adjoining a prime.

**Theorem 1.1 (An exact recurrence and strict decrease).**

Lean statement: `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.coefficient_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.coefficient_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be squarefree and greater than one, and let p be a prime not dividing R. The function H is the same-sign overlap of the two truncated Mobius kernels B(R,u) and B(R,u/p), and J is its inverse-square integral over u greater than one. The coefficient c(Rp) equals (1-p to the power minus two)c(R) minus 2e(R)(1-1/p)J(R,p), and is strictly smaller than c(R).

**Theorem 1.2 (Positivity from a same-sign overlap).**

Lean statement: `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.overlap_integral_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.overlap_integral_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a squarefree R greater than one and a prime p, suppose that at some real u at least one the two kernels B(R,u) and B(R,u/p) have positive product. Their same-sign overlap persists on an interval of positive length, so J(R,p) is strictly positive.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.coefficient_recurrence`
- Truth anchor: `D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.overlap_integral_pos`
- Dependency: [D5/S3/Weil/Mertens/CoprimeMobiusCertificateError](CoprimeMobiusCertificateError.md)
