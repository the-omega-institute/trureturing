# No-Arbitrage Uniqueness of Reversible Rates

## Abstract

Two positive reversible exchange rates coincide exactly when neither cross-rate cycle has multiplier above one.

**Theorem 1.1 (No-arbitrage characterizes equality of reversible rates).**

$$\forall rate1, rate2 \in \mathbb{R},\ 0<rate1 \land 0<rate2 \Rightarrow (\frac{rate1}{rate2} \le 1 \land \frac{rate2}{rate1} \le 1) \Leftrightarrow rate1 = rate2.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/NoArbitrageRateUniqueness.no_arbitrage_iff_reversible_rates_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rate1 and rate2 be positive real exchange rates. The two displayed quotients are the multipliers obtained by composing one proposed rate with the inverse of the other. Requiring both cycle multipliers to be at most one rules out gain in either direction.

Pinned Mathlib and Loogle both identify div_le_one as the exact bridge from each quotient bound to an order comparison. Antisymmetry then forces equality. No exact combined no-arbitrage theorem was found. The local smart-search declaration-name query exited 1 with no hit; the LeanSearch API request returned HTTP 404 and is not counted as a negative search result.

This closes the reversible-rate uniqueness sentence in pzg-v170 remark/27.612, atom pzg-residual-fa0e8ffc2bb3d31040f8eee2a35ffc3c1cbdc199c8bddf608bbd0da1c534cd85. The surrounding entropy, compression, and resource-economy analogies are not claimed as separate formal theorems.

## References

- Truth anchor: `D5/S3/ResourceOrder/NoArbitrageRateUniqueness.no_arbitrage_iff_reversible_rates_eq`
