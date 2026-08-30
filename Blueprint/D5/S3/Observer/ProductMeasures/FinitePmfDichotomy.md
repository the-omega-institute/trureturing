# Kakutani Dichotomy for Finite PMF Products

## Abstract

Locally equivalent finite coordinate laws satisfy Kakutani's dichotomy.

**Theorem 1.1 (Energy summability exactly separates the two product-law regimes).**

$$\left(\operatorname{MutuallySingular}\left(\operatorname{productLaw}\left(p\right), \operatorname{productLaw}\left(q\right)\right) \Leftrightarrow \neg \operatorname{Summable}\left(\operatorname{energySequence}\left(p, q\right)\right)\right) \land \left(\operatorname{MutuallyAbsolutelyContinuous}\left(\operatorname{productLaw}\left(p\right), \operatorname{productLaw}\left(q\right)\right) \Leftrightarrow \operatorname{Summable}\left(\operatorname{energySequence}\left(p, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfDichotomy.finite_pmf_kakutani_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinatewise mutual absolute continuity makes the finite likelihood ratios well behaved. Summable squared Hellinger energy yields mutual absolute continuity of the countable product laws.

When the real-valued energy sequence is not summable, a geometric subsequence of prefix affinities and Borel--Cantelli produce a measurable separating event, so the product laws are singular.

## References

- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfDichotomy.finite_pmf_kakutani_dichotomy`
- Dependency: [D5/S3/Observer/MeasureSeparation/WeakPrimeSignalCompletionThreshold](../MeasureSeparation/WeakPrimeSignalCompletionThreshold.md)
- Dependency: [D5/S3/Observer/ProductMeasures/FinitePmfLikelihood](FinitePmfLikelihood.md)
