# Cutoff acceptance at every binary precision

## Abstract

Cutoff acceptance at every binary precision.

**Theorem 1.1 (Uniform finite Taylor depth).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform.checkCutoffLogistic_all_precision`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform.checkCutoffLogistic_all_precision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational t and natural m, the exact rational cutoff checker succeeds with Taylor depth 4m+4. Its endpoints are ordered, lie in [0,1], and differ by at most 2^-m.

The Taylor factorial estimate controls the scaled exponential width uniformly. The construction uses exact rational arithmetic, endpoint cases and reflection, and requires no supplied success hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform.checkCutoffLogistic_all_precision`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic](Logistic.md)
