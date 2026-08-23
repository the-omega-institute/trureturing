# Term Bounds Do Not Bound Growing Family Sums

## Abstract

Growing finite families can keep a nonzero sum despite vanishing term bounds.

**Theorem 1.1 (Small terms do not force a growing family sum to vanish).**

$$\forall \gamma\in\mathbb{N}, 0 < \gamma \Rightarrow\\{}\exists \varepsilon: \mathbb{N}\to\mathbb{R}, n: \mathbb{N}\to\mathbb{N}, A: \forall m, \operatorname{Fin}\left(n_{m}\right)\to\mathbb{R},\\{}\lim_{m\to\infty} \varepsilon_{m} = 0 \land \forall m, 0 < \varepsilon_{m} \land\\{}\forall m, i\in\operatorname{Fin}\left(n_{m}\right), \lvert A_{m,i} \rvert \leq \varepsilon_{m}^{\gamma} \land\\{}\forall m, \sum_{i \in \operatorname{Fin}\left(n_{m}\right)} \lvert A_{m,i} \rvert = 1 \land\\{}\neg (\lim_{m\to\infty} \sum_{i \in \operatorname{Fin}\left(n_{m}\right)} \lvert A_{m,i} \rvert = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/FamilySums/TermBoundDoesNotBoundFamilySum.term_bound_does_not_bound_family_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every given positive natural exponent gamma, the witness takes epsilon_m equal to 1/(m+1), a family of (m+1)^gamma members, and identical amplitudes epsilon_m^gamma. The scale is positive and tends to zero, and every amplitude meets the bound with equality.

Summing the (m+1)^gamma absolute amplitudes gives exactly one for every m. The family sums are therefore bounded away from zero and cannot converge to zero, even though the individual bound vanishes.

A separate Lean example fixes the family size at one and verifies that its sum does converge to zero. This distinguishes the growth obstruction from a universal failure of termwise decay.

The source's six controls, covering analytic gain, object counts, cancellation grouping, cut termination, truncation remainders, and time-block accumulation, are a research checklist rather than mathematical assertions and are not encoded as propositions.

## References

- Truth anchor: `D5/S3/AnalyticClosure/FamilySums/TermBoundDoesNotBoundFamilySum.term_bound_does_not_bound_family_sum`
