# A vanishing tail isolates the second coefficient

## Abstract

Coefficient extraction from scaled alternating derivatives.

**Theorem 1.1 (Extraction limit).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An eventual decomposition of the scaled derivative sequence into its second coefficient and a vanishing tail gives convergence to that coefficient.

**Theorem 1.2 (Extraction for the consecutive ratios).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Extraction.quotient_extraction_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Extraction.quotient_extraction_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index i, evaluating the signed derivative of order k at k log(7/4) and multiplying by (49/32)^k converges to b(2). The normalized weight is a(n)=(49/32)n(4/7)^n, with a(1)=7/8, a(2)=1, and a(n+3) at most (6/7)(16/21)^n. If B=2^(i+2) and B(16/21)^k is at most one half, absolute convergence and the coefficient bound give an error at most |b(1)|(7/8)^k+2B^3(6/7)^k. Both terms tend to zero. The quotient derivative series applies eventually because k log(7/4) tends to infinity.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Extraction.quotient_extraction_limit`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Series](Series.md)
