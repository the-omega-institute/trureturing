# Escape Probability Monotonicity

## Abstract

Escape probability is nondecreasing in guarded address cardinality and has the one-address value.

**Theorem 1.1 (Escape probability is monotone and has the one-address value).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y\to Y, (\forall a, b\in\mathbb{N}, a \ge 1 \land b \ge 1 \land a \le b \Rightarrow \operatorname{escapeProbability}\left(\operatorname{Fin}\left(a\right), f\right) \le \operatorname{escapeProbability}\left(\operatorname{Fin}\left(b\right), f\right)) \land \operatorname{escapeProbability}\left(\operatorname{Fin}\left(1\right), f\right) = 1 - \frac{\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)}{\operatorname{card}\left(Y\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbabilityMonotone.escape_probability_monotone_and_one_address` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty value type Y, the exact escape probability is nondecreasing as the guarded address cardinality increases. At address cardinality one it equals one minus the fixed-point count divided by the value cardinality.

The proof first rewrites the repository's escapeProbability definition using the frozen escaped_listing_card count. The successor inequality is then an elementary Bernoulli bound for the exact formula ((n^A-k)/n^A)^A; the finite fixed-point subtype supplies k <= n.

The source clause is guarded by 1 <= A. At A = 0 the formula evaluates to P_esc(0) = 1, while for k > 0 it gives P_esc(1) = 1 - k/n < 1; therefore unguarded monotonicity is false and the A = 1 endpoint must be stated on the guarded domain to faithfully express the paper's escape-rate claim. This deposit closes only clause (ii); source clause (v) remains unformalized, so corollary 3.6 is not fully closed.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbabilityMonotone.escape_probability_monotone_and_one_address`
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](FixedPointFreeEscapeProbability.md)
