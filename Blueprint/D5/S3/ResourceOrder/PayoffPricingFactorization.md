# Payoff Pricing Factorization

## Abstract

A linear price descends uniquely to attainable payoffs exactly when it kills null trades.

**Theorem 1.1 (Prices factor uniquely through payoff range).**

$$payoff: \operatorname{LinearMap}_{R}(M, N), price: \operatorname{LinearMap}_{R}(M, R),\ ((\forall z, zPrime, payoff(z) = payoff(zPrime) \Rightarrow price(z) = price(zPrime)) \Leftrightarrow \ker payoff \subseteq \ker price) \land (\ker payoff \subseteq \ker price \Leftrightarrow \exists! factor: \operatorname{LinearMap}_{R}(\operatorname{range}(payoff), R), \forall z, price(z) = factor(payoff(z))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PayoffPricingFactorization.payoff_price_factorization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let payoff and price be linear maps on the same trade module. Equal payoffs receive equal prices exactly when every null-payoff trade also has zero price, expressed by inclusion of the two kernels.

That kernel inclusion is also exactly the condition for price to factor through the attainable payoff range. The factor is unique because every element of the range has a trade witness, so agreement on all payoffs determines the linear map everywhere.

Pinned Mathlib source search found the reusable first-isomorphism infrastructure Submodule.liftQ, LinearMap.quotKerEquivRange, and LinearMap.quotKerEquivRange_symm_apply_image, but no declaration combining the displayed equivalences. Local smart-search declaration-name queries returned no exact hit. NyxID exposed no Loogle or LeanSearch service, so those endpoints are not counted as negative searches. A Tavily/GitHub search succeeded after an initial HTTP 422 caused by a missing Content-Type header and likewise found only the first-isomorphism infrastructure, not the combined theorem.

This closes exactly the displayed three-condition theorem in qdo-v1 theorem/34.3, atom qdo-residual-325e585194898f14ad5f72c580d596555f450f13d59ffb121c471def9d8513c5. No surrounding economic interpretation is claimed as a separate theorem.

## References

- Truth anchor: `D5/S3/ResourceOrder/PayoffPricingFactorization.payoff_price_factorization_iff`
