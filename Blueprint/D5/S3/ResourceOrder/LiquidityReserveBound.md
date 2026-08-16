# Liquidity Reserve Bound

## Abstract

A nonincreasing price curve has nonnegative liquidity reserve.

**Theorem 1.1 (Liquidity reserve is nonnegative).**

$$\forall P: \mathbb{R}\to\mathbb{R}, Q\in\mathbb{R},\ \operatorname{Antitone}(P) \land 0\leq Q \Rightarrow \int_{0}^{Q}(\operatorname{P}\left(x\right)) dx \leq \operatorname{P}\left(0\right)\cdot Q \land \operatorname{P}\left(0\right)\cdot Q - \int_{0}^{Q}(\operatorname{P}\left(x\right)) dx = \int_{0}^{Q}(\operatorname{P}\left(0\right) - \operatorname{P}\left(x\right)) dx \land 0\leq \operatorname{P}\left(0\right)\cdot Q - \int_{0}^{Q}(\operatorname{P}\left(x\right)) dx.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/LiquidityReserveBound.liquidity_reserve_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a nonincreasing real price curve and let Q be nonnegative. The accumulated liquidity cost is the integral of P from zero to Q. It is bounded above by the rectangle with height P(0) and width Q.

Subtracting the cost from that rectangle gives exactly the integral of the pointwise price drop P(0) - P(x). Consequently the liquidity reserve is nonnegative.

Pinned Mathlib and Loogle both return intervalIntegral.integral_mono_on as the exact comparison theorem. The proof also directly uses Antitone.intervalIntegrable, the constant integral identity, and intervalIntegral.integral_sub. Repository searches found no equivalent D5 theorem. The LeanSearch API request failed and is not counted as a negative result.

This closes qdo-v1 theorem/34.10, atom qdo-residual-c4eed44a7868133a4d15c1221a52a0a7e225b81ce63bc7f17699df5aa898b14b.

## References

- Truth anchor: `D5/S3/ResourceOrder/LiquidityReserveBound.liquidity_reserve_nonnegative`
