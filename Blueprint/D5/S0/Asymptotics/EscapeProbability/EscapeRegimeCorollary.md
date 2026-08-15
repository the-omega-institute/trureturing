# Realizable Escape Regimes

## Abstract

Fixed finite output systems admit only the full-escape large-address regime.

**Theorem 1.1 (The fixed-output escape regimes reduce to full escape).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y,\ n = \operatorname{card}\left(Y\right), k = \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right), \left(\begin{aligned}\left(k = 0 \Rightarrow \forall A\in\mathbb{N}, \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = 1\right)\\\land \operatorname{MonotoneOn}\left((A \mapsto \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right)), \operatorname{Ici}\left(1\right)\right)\\\land \left(\left(n \ge 2 \land k > 0\right) \Rightarrow \operatorname{StrictMonoOn}\left((A \mapsto \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right)), \operatorname{Ici}\left(1\right)\right)\right)\\\land \operatorname{escapeProbability}\left(\operatorname{Fin}\left(1\right), f\right) = 1 - \frac{k}{n}\\\land \left(n \ge 2 \Rightarrow \lim_{A\to\infty} \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = 1\right)\\\land k \le n\\\land \left(n \ge 2 \Rightarrow \left(\begin{aligned}\forall A\in\mathbb{N}, 0 \le k A n^{-A} \le A n^{1-A} \le A 2^{1-A}\\\land \lim_{A\to\infty} k A n^{-A} = 0\\\land \forall \lambda\in\mathbb{R}, \lambda > 0 \Rightarrow \neg\left(\lim_{A\to\infty} k A n^{-A} = \lambda\right)\end{aligned}\right)\right)\\\land \left(n \ge 2 \Rightarrow \left(\forall c\in\mathbb{R}, 0 < c < 1 \Rightarrow \exists A_{0}\in\mathbb{N}, \forall A\in\mathbb{N}, A_{0} \le A \Rightarrow k \neq c n^{A}\right)\right)\end{aligned}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/EscapeRegimeCorollary.escape_probability_realizable_regimes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite nonempty output alphabet, let f map Y to itself, write n for the size of Y and k for the number of fixed points. If k is zero, every address count has escape probability one. On positive address counts the probability is nondecreasing, and at one address it is one minus k divided by n. When n is at least two, the probability is strictly increasing if k is positive and tends to one as the address count grows.

The same theorem records the unconditional model constraint k at most n. When n is at least two, the scaled weight k A n to the minus A lies between zero and the two stated geometric envelopes, tends to zero, and therefore cannot tend to a positive lambda. Under that same size condition, every density c strictly between zero and one has a finite threshold beyond which k cannot equal c n to the A.

The proof applies the repository's exact closed-form, monotonicity, strict-monotonicity, fixed-output limit, geometric-decay, and positive-density exclusion theorems. Pinned Mathlib and Loogle contain no theorem combining these clauses; Mathlib's Fintype.card_subtype_le supplies the structural count bound. The conjunction preserves every mathematical clause of the named corollary, including its positive-address guard.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/EscapeRegimeCorollary.escape_probability_realizable_regimes`
- Dependency: [D5/S0/Asymptotics/DensePhaseUnrealizable](../DensePhaseUnrealizable.md)
- Dependency: [D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit](FixedOutputLimit.md)
- Dependency: [D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit](PoissonDomainLimit.md)
- Dependency: [D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity](StrictAddressMonotonicity.md)
- Dependency: [D5/S0/Asymptotics/EscapeProbabilityMonotone](../EscapeProbabilityMonotone.md)
- Dependency: [D5/S0/Asymptotics/PoissonWeightDecay](../PoissonWeightDecay.md)
