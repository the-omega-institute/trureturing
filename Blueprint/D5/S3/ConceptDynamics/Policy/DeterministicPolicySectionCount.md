# Deterministic Policy Section Count

## Abstract

Distinct public states with at least two legal actions force exponentially many deterministic sections.

**Theorem 1.1 (Legal deterministic sections have an exponential lower bound).**

$$\forall Q, A, k: \operatorname{Type},\\{}legal: Q \to \operatorname{Set}(A), selected: \operatorname{Fin}\left(k\right) \to Q,\\{}\operatorname{Finite}\left(Q\right) \land \operatorname{Finite}\left(A\right) \land \forall q \in Q,\; \operatorname{Nonempty}\left(legal(q)\right) \land \operatorname{Injective}\left(selected\right) \land \forall i \in \operatorname{Fin}\left(k\right),\; 2 \leq \operatorname{card}(\{a \mid a \in legal(selected(i))\}) \Rightarrow 2^{k} \leq \operatorname{card}(\forall q \in Q,\; \{a \mid a \in legal(q)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Policy/DeterministicPolicySectionCount.deterministic_policy_sections_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The legal-action relation is the source primitive: every public state has a finite nonempty legal-action fiber. A deterministic section is the dependent product that assigns one subtype element to every public state.

An injectively selected family of k public states has at least two choices in each corresponding fiber. The finite product cardinality theorem therefore gives the lower bound 2^k, while the remaining nonempty fibers can only increase the full section-space cardinality.

The proof uses the exact finite-cardinality and product-order lemmas from pinned Mathlib; no Boolean-only or target-shaped section object is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Policy/DeterministicPolicySectionCount.deterministic_policy_sections_lower_bound`
