# Failure and classification from the extracted coefficient

## Abstract

Coefficient extraction and the low-index classification of exponential derivative ratios.

**Theorem 1.1 (Indices at least three).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an index at least three, the second quotient coefficient is 2 times 3 to the index minus 4 to the index, hence negative. The extraction contradiction excludes complete monotonicity for either ratio family once the corresponding limits are supplied.

**Theorem 1.2 (Classification from positive cases and limits).**

Lean statement: `D5/S3/Analytic/ExpRatioCM/Result.classification_of_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRatioCM/Result.classification_of_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining complete monotonicity of the low-index coefficient cases with the failure family gives the exact index classification for each ratio family.

## References

- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.classification_of_limits`
- Truth anchor: `D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Extraction](Extraction.md)
- Dependency: [D5/S3/Analytic/ExpRatioCM/Positive](Positive.md)
