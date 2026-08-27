# Strict Lower Bound for the Golden Displacement Series

## Abstract

A summable golden displacement series is strictly greater than one.

**Theorem 1.1 (The displacement series is strictly greater than one).**

$$\forall s, w \in \mathbb{R},\quad\operatorname{Summable}(\operatorname{dTerm}(s, w)) \Rightarrow\\1 < \sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound.one_lt_golden_displacement_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real parameter pair (s,w) where dTerm(s,w) is summable, the golden displacement series is strictly greater than one.

The term at index one equals one. The public bound le_nS shows that nS(2) is positive, so both real-power factors in dTerm(s,w,2) are positive for arbitrary real parameters. Every displacement term is nonnegative.

Mathlib's strict HasSum comparison applies the positive witness at index two together with nonnegativity away from index one. It makes the index-one term strictly smaller than the total sum.

The summability hypothesis is necessary. At (s,w)=(0,0), the exact two-constraint criterion fails, so the series is not summable and the infinite sum is zero by convention; the unrestricted strict inequality would read 1<0.

The theorem does not claim an infimum characterization, an attained minimum, a quantitative gap, or a lower bound outside the summability region.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound.one_lt_golden_displacement_series`
- Dependency: [D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct](../../../S1/Deficit/Displacement/GoldenDisplacementEulerProduct.md)
