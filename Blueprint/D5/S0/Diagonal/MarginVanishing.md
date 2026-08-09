# Vanishing Linear-Margin Failure

## Abstract

Corrected KL margin bounds and the associated failure probabilities vanish as the address cardinality grows.

**Definition 1.1 (Corrected linear-margin bound).**

Lean statement: `D5/S0/Diagonal/MarginVanishing.linearMarginBound`

*Formalization.* `D5/S0/Diagonal/MarginVanishing.linearMarginBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At address cardinality A, the bound is A times the exponential of minus A minus one times the Bernoulli KL divergence. Its first parameter is the corrected alpha A divided by A minus one, and its second parameter is the fixed nonzero-choice density.

**Theorem 1.2 (The corrected bound vanishes).**

$$\lim_{A\to\infty}\operatorname{linearMarginBound}\left(n, alpha, A\right)=0.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/MarginVanishing.linear_margin_bound_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed n at least two and alpha strictly between zero and (n-1)/n, the corrected bound tends to zero. Continuity of the frozen Bernoulli KL divergence gives a strictly positive limiting rate, and the standard real-power times negative-exponential asymptotic dominates the linear factor.

This limit does not claim that every finite prefix is monotone. For n=2 and alpha=1/4, the complete union bound increases on A=3 through A=8 before its eventual decrease.

**Theorem 1.3 (The actual failure probability vanishes).**

$$\lim_{A\to\infty}\operatorname{marginFailureProbability}\left(f, alpha\right)=0.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/MarginVanishing.margin_failure_probability_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed finite value type and a fixed diagonal map, instantiate the address type by Fin A. The finite theorem from MarginBound supplies the eventual upper bound, so nonnegativity and the vanishing corrected bound squeeze the actual failure probability to zero.

## References

- Truth anchor: `D5/S0/Diagonal/MarginVanishing.linearMarginBound`
- Truth anchor: `D5/S0/Diagonal/MarginVanishing.linear_margin_bound_tendsto_zero`
- Truth anchor: `D5/S0/Diagonal/MarginVanishing.margin_failure_probability_tendsto_zero`
- Dependency: [D5/S0/Diagonal/MarginBound](MarginBound.md)
