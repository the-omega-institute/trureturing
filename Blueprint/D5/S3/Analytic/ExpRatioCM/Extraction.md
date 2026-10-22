# A vanishing tail isolates the second coefficient

## Abstract

Coefficient extraction from scaled alternating derivatives.

**Theorem 1.1 (Extraction limit).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the scaled derivative sequence equals a fixed second coefficient plus a tail converging to zero, then it converges to that coefficient. The exponential-series estimate supplies the equality and the geometric tail in the quotient application.

**Theorem 1.2 (Negative extracted coefficient).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Extraction.not_completelyMonotone_of_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Extraction.not_completelyMonotone_of_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete monotonicity makes every scaled alternating derivative nonnegative. A convergent sequence of such values cannot have a negative limit, so a negative extracted coefficient rules out complete monotonicity.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Extraction.not_completelyMonotone_of_extraction`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Series](Series.md)
