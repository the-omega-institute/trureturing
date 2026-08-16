# Marginal Trade and Marked Value

## Abstract

Marginal repricing amplifies marked value relative to the cash transferred by the trade.

**Theorem 1.1 (Marginal trade marked-value amplification).**

$$0 \leq N \land markedChange = N(p1 - p0) \land tradeCash = delta\cdot pBar \Rightarrow \frac{\lvert markedChange \rvert}{tradeCash} = \frac{N\cdot \lvert p1 - p0 \rvert}{delta\cdot pBar}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/MarginalTradeAmplification.marginal_trade_mark_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a nonnegative inventory, let the displayed price move from p0 to p1, and let a trade of size delta execute at average price pBar. The marked-value change is N(p1-p0), while the transferred cash is delta pBar.

Substitution shows that the absolute marked-value change divided by traded cash is N times the absolute price move divided by delta pBar. The statement is an accounting identity and imposes no model of how the marginal price move is generated.

Pinned Mathlib supplies abs_mul and abs_of_nonneg as the exact algebraic steps. Repository and pinned-library searches found no market-specific declaration for the complete ratio identity.

## References

- Truth anchor: `D5/S3/ResourceOrder/MarginalTradeAmplification.marginal_trade_mark_amplification`
