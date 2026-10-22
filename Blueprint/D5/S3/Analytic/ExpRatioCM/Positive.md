# The coefficient criterion

## Abstract

Positive exponential coefficients and complete monotonicity.

**Theorem 1.1 (Nonnegative exponential expansion).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A smooth function whose every derivative is represented by nonnegative coefficients at nonnegative exponential frequencies has alternating derivatives of the required sign on the positive half-line.

**Theorem 1.2 (Low-index positive cases).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed exponential moments give complete monotonicity of the zeroth moment. Differentiating the reciprocal three times gives the low-index closed forms on the entire positive half-line. The first two ratios are a nonnegative constant plus a nonnegative multiple of the zeroth moment. The third ratio is one plus four times that moment minus twice its value at twice the argument. At every derivative order the even terms of the moment series bound this subtraction, proving the required sign. This is the same coefficient positivity as coefficient four at positive odd frequencies and coefficient two at positive even frequencies. The zeroth ratio of the second family equals the zeroth moment, and its positive-index ratios agree with the first family.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Series](Series.md)
