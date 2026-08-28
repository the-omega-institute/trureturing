# Value Set of the Golden Displacement Series

## Abstract

The values attained by convergent golden displacement series form exactly the open ray above one.

Every convergent golden displacement series has value strictly greater than one. Conversely, finite harmonic sums become arbitrarily large. On the zero first-parameter slice, exponents approaching one from above produce convergent p-series whose finite partial sums approach those harmonic sums.

**Theorem 1.1 (The attained value set is the open ray above one).**

$$\left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\} = \operatorname{Ioi}(1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesValueSet.golden_displacement_series_values_eq_Ioi_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given any real x greater than one, choose a finite harmonic sum above x. Continuity in its exponent supplies a p-series exponent greater than one whose matching finite sum still exceeds x. Summability and termwise nonnegativity put the full p-series sum above x.

That full sum is an attained golden displacement value on the zero slice. The established no-gap theorem then fills the interval from one to this attained value, proving that x is attained.

This theorem classifies only the set of attained real values. It does not identify which parameter pairs attain a given value, assert uniqueness of parameters, give convergence rates, or claim that a series converges at the boundary exponent one.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesValueSet.golden_displacement_series_values_eq_Ioi_one`
- Dependency: [D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness](../Connectivity/GoldenDisplacementSeriesValueConnectedness.md)
