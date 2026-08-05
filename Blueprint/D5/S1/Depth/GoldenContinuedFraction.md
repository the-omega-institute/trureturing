# The Golden Continued Fraction

## Abstract

The continued fraction of the golden ratio has constant unit coefficients.

**Theorem 1.1 (Every continued-fraction coefficient is one).**

$$\varphi = [\,1;\overline{1}\,]$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/GoldenContinuedFraction.golden_ratio_continued_fraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's generalized continued fraction of the real golden ratio has head one, and every subsequent numerator-denominator pair is the pair (1, 1).

## References

- Truth anchor: `D5/S1/Depth/GoldenContinuedFraction.golden_ratio_continued_fraction`
