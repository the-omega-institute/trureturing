# Poisson-Domain Escape Limit

## Abstract

A finite scaled fixed-point weight gives the exponential limit of the frozen escape probability.

**Theorem 1.1 (Scaled fixed points give the Poisson-domain escape-probability limit).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y, \lambda\in \mathbb{R}, \left(\lim_{A \to \infty} \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) A \operatorname{card}\left(Y\right)^{-A} = \lambda\right) \Rightarrow \lim_{A \to \infty} \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = \operatorname{exp}(-\lambda).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit.poisson_domain_escape_probability_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty output type Y and f:Y->Y, put n=|Y| and k=|Fix(f)|. If the real scaled weight k A n^(-A) tends to lambda, then the repository's frozen escape probability on Fin A tends to exp(-lambda).

The public closed-form lemma derives P_esc(Fin A,f)=(1-k/n^A)^A from escaped_listing_card and the Nat.card ratio definition. The supporting analytic theorem then applies pinned Mathlib's Real.tendsto_one_add_pow_exp_of_tendsto.

This is the analytic conditional from the older Poisson-domain clause. The current corrected model clause is compatible with it: when k(A) is an actual fixed-point count bounded by n(A) in the fixed n at least two regime, the scaled weight tends to zero, so no positive Poisson parameter is realizable.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit.poisson_domain_escape_probability_limit`
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](../FixedPointFreeEscapeProbability.md)
