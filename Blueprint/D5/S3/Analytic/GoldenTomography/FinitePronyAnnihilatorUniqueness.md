# Finite Prony Annihilator Uniqueness

## Abstract

The true finite Prony annihilator is uniquely determined by a full recurrence window.

**Theorem 1.1 (The bounded monic recurrence polynomial is unique).**

$$\operatorname{Monic}(q) \land \operatorname{deg}(q) \leq m \land \operatorname{Rec}(q, c) \iff q = \operatorname{A}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorUniqueness.existsUnique_prony_annihilator_from_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite exponential moment sequence with pairwise distinct nodes and nonzero weights, there is exactly one monic polynomial of degree at most the number of modes whose coefficient recurrence holds on the first matching number of shifts. It is the product of the linear factors determined by the true nodes.

The proof first uses the recurrence window to identify every true node as a root. Pairwise coprimality of the distinct linear factors makes their product divide the candidate. Monicity and the degree bound then force equality with the true annihilator.

This theorem establishes exact structural identifiability of the annihilator. It does not provide a numerical coefficient solver, a root-finding algorithm, confluent-mode recovery, or a noisy conditioning estimate.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorUniqueness.existsUnique_prony_annihilator_from_window`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification](FinitePronyNodeIdentification.md)
