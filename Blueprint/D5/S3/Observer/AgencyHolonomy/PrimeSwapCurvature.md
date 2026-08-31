# Prime Swap Curvature

## Abstract

Stable prime-memory swap curvature is gauge invariant.

**Theorem 1.1 (Stable prime swap curvature specification).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)],\\{}a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}, \xi: K,\\{}s: K \times K,\\{}(a - \lambda_{P} \neq 0) \land (a - \lambda_{Q} \neq 0) \Rightarrow\\{}((\operatorname{fst}\left(\operatorname{stablePrimeUpdate}\left(a, b_{Q}, \lambda_{Q}, \operatorname{stablePrimeUpdate}\left(a, b_{P}, \lambda_{P}, s\right)\right)\right) - \operatorname{fst}\left(\operatorname{stablePrimeUpdate}\left(a, b_{P}, \lambda_{P}, \operatorname{stablePrimeUpdate}\left(a, b_{Q}, \lambda_{Q}, s\right)\right)\right) = \operatorname{primeSwapCurvature}\left(a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}\right) \times \operatorname{snd}\left(s\right)) \land\\{}(\operatorname{snd}\left(\operatorname{stablePrimeUpdate}\left(a, b_{Q}, \lambda_{Q}, \operatorname{stablePrimeUpdate}\left(a, b_{P}, \lambda_{P}, s\right)\right)\right) = \operatorname{snd}\left(\operatorname{stablePrimeUpdate}\left(a, b_{P}, \lambda_{P}, \operatorname{stablePrimeUpdate}\left(a, b_{Q}, \lambda_{Q}, s\right)\right)\right)) \land\\{}(\operatorname{primeSwapCurvature}\left(a, b_{Q}, \lambda_{Q}, b_{P}, \lambda_{P}\right) = -\operatorname{primeSwapCurvature}\left(a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}\right)) \land\\{}(\operatorname{primeSwapCurvature}\left(a, \operatorname{memoryGaugeShift}\left(a, \lambda_{P}, \xi, b_{P}\right), \lambda_{P}, \operatorname{memoryGaugeShift}\left(a, \lambda_{Q}, \xi, b_{Q}\right), \lambda_{Q}\right) = \operatorname{primeSwapCurvature}\left(a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}\right)) \land\\{}(\operatorname{primeSwapCurvature}\left(a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}\right) = (a - \lambda_{P}) \times (a - \lambda_{Q}) \times (\operatorname{observerOrigin}\left(a, \lambda_{P}, b_{P}\right) - \operatorname{observerOrigin}\left(a, \lambda_{Q}, b_{Q}\right))) \land\\{}((\operatorname{primeSwapCurvature}\left(a, b_{P}, \lambda_{P}, b_{Q}, \lambda_{Q}\right) = 0) \Leftrightarrow (\operatorname{observerOrigin}\left(a, \lambda_{P}, b_{P}\right) = \operatorname{observerOrigin}\left(a, \lambda_{Q}, b_{Q}\right)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.prime_swap_curvature_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging two lifted prime updates produces a memory defect equal to the swap curvature times the scalar state, while the scalar output is unchanged. Reversing the exchange negates the curvature, and a common shift of memory origin leaves it invariant.

Under the two stated nonresonance hypotheses, the curvature factors through the difference of the observer-origin estimates. Its vanishing is therefore equivalent to agreement of those estimates; no analytic or zero-location conclusion is asserted.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.prime_swap_curvature_spec`
